import V185TrunkScan23Chunk1199

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7109162 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 6]
def baseStart_7109162 : Nat := 118140960795 + 7109162 * 2 ^ 59
def prefixEnd_7109162 : Nat := 4983230072969 + 3 ^ 40 * 7109162 * 2
def baseEnd_7109162 : Nat := 405601906297646622742285

theorem tailTrace_7109162 : CollatzResearch.WordTrace tailWord_7109162 prefixEnd_7109162 405601906297646622742285 := by
  unfold tailWord_7109162
  simp only [CollatzResearch.WordTrace]
  refine ⟨64823109967681924262858435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172861626580485131367622493 64823109967681924262858435)
  ·
    refine ⟨97234664951522886394287653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64823109967681924262858435 97234664951522886394287653)
    ·
      refine ⟨18231499678410541198928935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97234664951522886394287653 18231499678410541198928935)
      ·
        refine ⟨27347249517615811798393403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18231499678410541198928935 27347249517615811798393403)
        ·
          refine ⟨41020874276423717697590105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27347249517615811798393403 41020874276423717697590105)
          ·
            refine ⟨30765655707317788273192579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41020874276423717697590105 30765655707317788273192579)
            ·
              refine ⟨46148483560976682409788869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30765655707317788273192579 46148483560976682409788869)
              ·
                refine ⟨8652840667683127951835413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46148483560976682409788869 8652840667683127951835413)
                ·
                  refine ⟨405601906297646622742285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8652840667683127951835413 405601906297646622742285)
                  ·
                    rfl

theorem cell23_7109162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_7109162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109162 prefixEnd_7109162 := by exact prefixLift 7109162
  have htrace : WordTrace (prefixWord ++ tailWord_7109162) baseStart_7109162 baseEnd_7109162 := by
    simpa [prefixWord, tailWord_7109162, baseEnd_7109162] using wordTrace_append hprefix tailTrace_7109162
  have hstable : (prefixWord ++ tailWord_7109162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109162).length < 2 ^ (prefixWord ++ tailWord_7109162).sum := by decide
  have hdescent : baseEnd_7109162 < baseStart_7109162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109175 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 5, 5]
def baseStart_7109175 : Nat := 118140960795 + 7109175 * 2 ^ 59
def prefixEnd_7109175 : Nat := 4983230072969 + 3 ^ 40 * 7109175 * 2
def baseEnd_7109175 : Nat := 1216807943975776017939335

theorem tailTrace_7109175 : CollatzResearch.WordTrace tailWord_7109175 prefixEnd_7109175 1216807943975776017939335 := by
  unfold tailWord_7109175
  simp only [CollatzResearch.WordTrace]
  refine ⟨259292914019680600271656979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172861942679787066847771319 259292914019680600271656979)
  ·
    refine ⟨388939371029520900407485469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259292914019680600271656979 388939371029520900407485469)
    ·
      refine ⟨145852264136070337652807051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388939371029520900407485469 145852264136070337652807051)
      ·
        refine ⟨218778396204105506479210577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145852264136070337652807051 218778396204105506479210577)
        ·
          refine ⟨164083797153079129859407933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218778396204105506479210577 164083797153079129859407933)
          ·
            refine ⟨61531423932404673697277975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164083797153079129859407933 61531423932404673697277975)
            ·
              refine ⟨92297135898607010545916963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61531423932404673697277975 92297135898607010545916963)
              ·
                refine ⟨138445703847910515818875445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92297135898607010545916963 138445703847910515818875445)
                ·
                  refine ⟨12979284735741610858019573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138445703847910515818875445 12979284735741610858019573)
                  ·
                    refine ⟨1216807943975776017939335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12979284735741610858019573 1216807943975776017939335)
                    ·
                      rfl

theorem cell23_7109175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_7109175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109175 prefixEnd_7109175 := by exact prefixLift 7109175
  have htrace : WordTrace (prefixWord ++ tailWord_7109175) baseStart_7109175 baseEnd_7109175 := by
    simpa [prefixWord, tailWord_7109175, baseEnd_7109175] using wordTrace_append hprefix tailTrace_7109175
  have hstable : (prefixWord ++ tailWord_7109175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109175).length < 2 ^ (prefixWord ++ tailWord_7109175).sum := by decide
  have hdescent : baseEnd_7109175 < baseStart_7109175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109189 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 3, 1, 3]
def baseStart_7109189 : Nat := 118140960795 + 7109189 * 2 ^ 59
def prefixEnd_7109189 : Nat := 4983230072969 + 3 ^ 40 * 7109189 * 2
def baseEnd_7109189 : Nat := 3650431020656490999042941

theorem tailTrace_7109189 : CollatzResearch.WordTrace tailWord_7109189 prefixEnd_7109189 3650431020656490999042941 := by
  unfold tailWord_7109189
  simp only [CollatzResearch.WordTrace]
  refine ⟨259293424641629880662666621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172862283094419920441777747 259293424641629880662666621)
  ·
    refine ⟨97235034240611205248499983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259293424641629880662666621 97235034240611205248499983)
    ·
      refine ⟨145852551360916807872749975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97235034240611205248499983 145852551360916807872749975)
      ·
        refine ⟨218778827041375211809124963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145852551360916807872749975 218778827041375211809124963)
        ·
          refine ⟨328168240562062817713687445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218778827041375211809124963 328168240562062817713687445)
          ·
            refine ⟨15382886276346694580329099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 328168240562062817713687445 15382886276346694580329099)
            ·
              refine ⟨23074329414520041870493649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15382886276346694580329099 23074329414520041870493649)
              ·
                refine ⟨17305747060890031402870237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23074329414520041870493649 17305747060890031402870237)
                ·
                  refine ⟨6489655147833761776076339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17305747060890031402870237 6489655147833761776076339)
                  ·
                    refine ⟨9734482721750642664114509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6489655147833761776076339 9734482721750642664114509)
                    ·
                      refine ⟨3650431020656490999042941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9734482721750642664114509 3650431020656490999042941)
                      ·
                        rfl

theorem cell23_7109189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_7109189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109189 prefixEnd_7109189 := by exact prefixLift 7109189
  have htrace : WordTrace (prefixWord ++ tailWord_7109189) baseStart_7109189 baseEnd_7109189 := by
    simpa [prefixWord, tailWord_7109189, baseEnd_7109189] using wordTrace_append hprefix tailTrace_7109189
  have hstable : (prefixWord ++ tailWord_7109189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109189).length < 2 ^ (prefixWord ++ tailWord_7109189).sum := by decide
  have hdescent : baseEnd_7109189 < baseStart_7109189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109199 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 2, 3, 2]
def baseStart_7109199 : Nat := 118140960795 + 7109199 * 2 ^ 59
def prefixEnd_7109199 : Nat := 4983230072969 + 3 ^ 40 * 7109199 * 2
def baseEnd_7109199 : Nat := 3650436155463035959917895

theorem tailTrace_7109199 : CollatzResearch.WordTrace tailWord_7109199 prefixEnd_7109199 3650436155463035959917895 := by
  unfold tailWord_7109199
  simp only [CollatzResearch.WordTrace]
  refine ⟨259293789371593652370530651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172862526247729101580353767 259293789371593652370530651)
  ·
    refine ⟨388940684057390478555795977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259293789371593652370530651 388940684057390478555795977)
    ·
      refine ⟨291705513043042858916846983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388940684057390478555795977 291705513043042858916846983)
      ·
        refine ⟨437558269564564288375270475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291705513043042858916846983 437558269564564288375270475)
        ·
          refine ⟨656337404346846432562905713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437558269564564288375270475 656337404346846432562905713)
          ·
            refine ⟨492253053260134824422179285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656337404346846432562905713 492253053260134824422179285)
            ·
              refine ⟨11537180935784409947394827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 492253053260134824422179285 11537180935784409947394827)
              ·
                refine ⟨17305771403676614921092241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11537180935784409947394827 17305771403676614921092241)
                ·
                  refine ⟨12979328552757461190819181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17305771403676614921092241 12979328552757461190819181)
                  ·
                    refine ⟨4867248207284047946557193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12979328552757461190819181 4867248207284047946557193)
                    ·
                      refine ⟨3650436155463035959917895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867248207284047946557193 3650436155463035959917895)
                      ·
                        rfl

theorem cell23_7109199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 3, 2].length) (baseStart_7109199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109199 prefixEnd_7109199 := by exact prefixLift 7109199
  have htrace : WordTrace (prefixWord ++ tailWord_7109199) baseStart_7109199 baseEnd_7109199 := by
    simpa [prefixWord, tailWord_7109199, baseEnd_7109199] using wordTrace_append hprefix tailTrace_7109199
  have hstable : (prefixWord ++ tailWord_7109199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109199).length < 2 ^ (prefixWord ++ tailWord_7109199).sum := by decide
  have hdescent : baseEnd_7109199 < baseStart_7109199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109215 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 5]
def baseStart_7109215 : Nat := 118140960795 + 7109215 * 2 ^ 59
def prefixEnd_7109215 : Nat := 4983230072969 + 3 ^ 40 * 7109215 * 2
def baseEnd_7109215 : Nat := 3650444371153507897317821

theorem tailTrace_7109215 : CollatzResearch.WordTrace tailWord_7109215 prefixEnd_7109215 3650444371153507897317821 := by
  unfold tailWord_7109215
  simp only [CollatzResearch.WordTrace]
  refine ⟨259294372939535687103113099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172862915293023791402075399 259294372939535687103113099)
  ·
    refine ⟨388941559409303530654669649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259294372939535687103113099 388941559409303530654669649)
    ·
      refine ⟨291706169556977647991002237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388941559409303530654669649 291706169556977647991002237)
      ·
        refine ⟨109389813583866617996625839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291706169556977647991002237 109389813583866617996625839)
        ·
          refine ⟨164084720375799926994938759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109389813583866617996625839 164084720375799926994938759)
          ·
            refine ⟨246127080563699890492408139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164084720375799926994938759 246127080563699890492408139)
            ·
              refine ⟨369190620845549835738612209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246127080563699890492408139 369190620845549835738612209)
              ·
                refine ⟨276892965634162376803959157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369190620845549835738612209 276892965634162376803959157)
                ·
                  refine ⟨25958715528202722825371171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 276892965634162376803959157 25958715528202722825371171)
                  ·
                    refine ⟨38938073292304084238056757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25958715528202722825371171 38938073292304084238056757)
                    ·
                      refine ⟨3650444371153507897317821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38938073292304084238056757 3650444371153507897317821)
                      ·
                        rfl

theorem cell23_7109215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_7109215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109215 prefixEnd_7109215 := by exact prefixLift 7109215
  have htrace : WordTrace (prefixWord ++ tailWord_7109215) baseStart_7109215 baseEnd_7109215 := by
    simpa [prefixWord, tailWord_7109215, baseEnd_7109215] using wordTrace_append hprefix tailTrace_7109215
  have hstable : (prefixWord ++ tailWord_7109215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109215).length < 2 ^ (prefixWord ++ tailWord_7109215).sum := by decide
  have hdescent : baseEnd_7109215 < baseStart_7109215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109225 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 6]
def baseStart_7109225 : Nat := 118140960795 + 7109225 * 2 ^ 59
def prefixEnd_7109225 : Nat := 4983230072969 + 3 ^ 40 * 7109225 * 2
def baseEnd_7109225 : Nat := 3650449505960052858192775

theorem tailTrace_7109225 : CollatzResearch.WordTrace tailWord_7109225 prefixEnd_7109225 3650449505960052858192775 := by
  unfold tailWord_7109225
  simp only [CollatzResearch.WordTrace]
  refine ⟨259294737669499458810977129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172863158446332972540651419 259294737669499458810977129)
  ·
    refine ⟨194471053252124594108232847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259294737669499458810977129 194471053252124594108232847)
    ·
      refine ⟨291706579878186891162349271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194471053252124594108232847 291706579878186891162349271)
      ·
        refine ⟨437559869817280336743523907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291706579878186891162349271 437559869817280336743523907)
        ·
          refine ⟨656339804725920505115285861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437559869817280336743523907 656339804725920505115285861)
          ·
            refine ⟨123063713386110094709116099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 656339804725920505115285861 123063713386110094709116099)
            ·
              refine ⟨184595570079165142063674149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123063713386110094709116099 184595570079165142063674149)
              ·
                refine ⟨34611669389843464136938903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184595570079165142063674149 34611669389843464136938903)
                ·
                  refine ⟨51917504084765196205408355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34611669389843464136938903 51917504084765196205408355)
                  ·
                    refine ⟨77876256127147794308112533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51917504084765196205408355 77876256127147794308112533)
                    ·
                      refine ⟨3650449505960052858192775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77876256127147794308112533 3650449505960052858192775)
                      ·
                        rfl

theorem cell23_7109225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_7109225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109225 prefixEnd_7109225 := by exact prefixLift 7109225
  have htrace : WordTrace (prefixWord ++ tailWord_7109225) baseStart_7109225 baseEnd_7109225 := by
    simpa [prefixWord, tailWord_7109225, baseEnd_7109225] using wordTrace_append hprefix tailTrace_7109225
  have hstable : (prefixWord ++ tailWord_7109225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109225).length < 2 ^ (prefixWord ++ tailWord_7109225).sum := by decide
  have hdescent : baseEnd_7109225 < baseStart_7109225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109252 : List Nat := [2, 3, 2, 1, 3, 2, 1, 9]
def baseStart_7109252 : Nat := 118140960795 + 7109252 * 2 ^ 59
def prefixEnd_7109252 : Nat := 4983230072969 + 3 ^ 40 * 7109252 * 2
def baseEnd_7109252 : Nat := 135202347034730527872413

theorem tailTrace_7109252 : CollatzResearch.WordTrace tailWord_7109252 prefixEnd_7109252 135202347034730527872413 := by
  unfold tailWord_7109252
  simp only [CollatzResearch.WordTrace]
  refine ⟨129647861220200821211105005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172863814960267761614806673 129647861220200821211105005)
  ·
    refine ⟨48617947957575307954164377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129647861220200821211105005 48617947957575307954164377)
    ·
      refine ⟨36463460968181480965623283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48617947957575307954164377 36463460968181480965623283)
      ·
        refine ⟨54695191452272221448434925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36463460968181480965623283 54695191452272221448434925)
        ·
          refine ⟨20510696794602083043163097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54695191452272221448434925 20510696794602083043163097)
          ·
            refine ⟨15383022595951562282372323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20510696794602083043163097 15383022595951562282372323)
            ·
              refine ⟨23074533893927343423558485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15383022595951562282372323 23074533893927343423558485)
              ·
                refine ⟨135202347034730527872413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23074533893927343423558485 135202347034730527872413)
                ·
                  rfl

theorem cell23_7109252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 9].length) (baseStart_7109252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109252 prefixEnd_7109252 := by exact prefixLift 7109252
  have htrace : WordTrace (prefixWord ++ tailWord_7109252) baseStart_7109252 baseEnd_7109252 := by
    simpa [prefixWord, tailWord_7109252, baseEnd_7109252] using wordTrace_append hprefix tailTrace_7109252
  have hstable : (prefixWord ++ tailWord_7109252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109252).length < 2 ^ (prefixWord ++ tailWord_7109252).sum := by decide
  have hdescent : baseEnd_7109252 < baseStart_7109252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109266 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_7109266 : Nat := 118140960795 + 7109266 * 2 ^ 59
def prefixEnd_7109266 : Nat := 4983230072969 + 3 ^ 40 * 7109266 * 2
def baseEnd_7109266 : Nat := 3650470558666887197780087

theorem tailTrace_7109266 : CollatzResearch.WordTrace tailWord_7109266 prefixEnd_7109266 3650470558666887197780087 := by
  unfold tailWord_7109266
  simp only [CollatzResearch.WordTrace]
  refine ⟨64824058265587730703304913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172864155374900615208813101 64824058265587730703304913)
  ·
    refine ⟨48618043699190798027478685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64824058265587730703304913 48618043699190798027478685)
    ·
      refine ⟨18231766387196549260304507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48618043699190798027478685 18231766387196549260304507)
      ·
        refine ⟨27347649580794823890456761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18231766387196549260304507 27347649580794823890456761)
        ·
          refine ⟨20510737185596117917842571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27347649580794823890456761 20510737185596117917842571)
          ·
            refine ⟨30766105778394176876763857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20510737185596117917842571 30766105778394176876763857)
            ·
              refine ⟨23074579333795632657572893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30766105778394176876763857 23074579333795632657572893)
              ·
                refine ⟨8652967250173362246589835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23074579333795632657572893 8652967250173362246589835)
                ·
                  refine ⟨12979450875260043369884753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8652967250173362246589835 12979450875260043369884753)
                  ·
                    refine ⟨9734588156445032527413565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12979450875260043369884753 9734588156445032527413565)
                    ·
                      refine ⟨3650470558666887197780087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9734588156445032527413565 3650470558666887197780087)
                      ·
                        rfl

theorem cell23_7109266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_7109266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109266 prefixEnd_7109266 := by exact prefixLift 7109266
  have htrace : WordTrace (prefixWord ++ tailWord_7109266) baseStart_7109266 baseEnd_7109266 := by
    simpa [prefixWord, tailWord_7109266, baseEnd_7109266] using wordTrace_append hprefix tailTrace_7109266
  have hstable : (prefixWord ++ tailWord_7109266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109266).length < 2 ^ (prefixWord ++ tailWord_7109266).sum := by decide
  have hdescent : baseEnd_7109266 < baseStart_7109266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109280 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 3, 2, 2]
def baseStart_7109280 : Nat := 118140960795 + 7109280 * 2 ^ 59
def prefixEnd_7109280 : Nat := 4983230072969 + 3 ^ 40 * 7109280 * 2
def baseEnd_7109280 : Nat := 3650477747396050143005023

theorem tailTrace_7109280 : CollatzResearch.WordTrace tailWord_7109280 prefixEnd_7109280 3650477747396050143005023 := by
  unfold tailWord_7109280
  simp only [CollatzResearch.WordTrace]
  refine ⟨129648371842150101602114647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172864495789533468802819529 129648371842150101602114647)
  ·
    refine ⟨194472557763225152403171971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129648371842150101602114647 194472557763225152403171971)
    ·
      refine ⟨291708836644837728604757957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194472557763225152403171971 291708836644837728604757957)
      ·
        refine ⟨54695406870907074113392117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291708836644837728604757957 54695406870907074113392117)
        ·
          refine ⟨5127694394147538198130511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54695406870907074113392117 5127694394147538198130511)
          ·
            refine ⟨7691541591221307297195767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5127694394147538198130511 7691541591221307297195767)
            ·
              refine ⟨11537312386831960945793651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7691541591221307297195767 11537312386831960945793651)
              ·
                refine ⟨17305968580247941418690477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11537312386831960945793651 17305968580247941418690477)
                ·
                  refine ⟨6489738217592978032008929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17305968580247941418690477 6489738217592978032008929)
                  ·
                    refine ⟨4867303663194733524006697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6489738217592978032008929 4867303663194733524006697)
                    ·
                      refine ⟨3650477747396050143005023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867303663194733524006697 3650477747396050143005023)
                      ·
                        rfl

theorem cell23_7109280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_7109280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109280 prefixEnd_7109280 := by exact prefixLift 7109280
  have htrace : WordTrace (prefixWord ++ tailWord_7109280) baseStart_7109280 baseEnd_7109280 := by
    simpa [prefixWord, tailWord_7109280, baseEnd_7109280] using wordTrace_append hprefix tailTrace_7109280
  have hstable : (prefixWord ++ tailWord_7109280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109280).length < 2 ^ (prefixWord ++ tailWord_7109280).sum := by decide
  have hdescent : baseEnd_7109280 < baseStart_7109280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109313 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7109313 : Nat := 118140960795 + 7109313 * 2 ^ 59
def prefixEnd_7109313 : Nat := 4983230072969 + 3 ^ 40 * 7109313 * 2
def baseEnd_7109313 : Nat := 3650494692257648513892371

theorem tailTrace_7109313 : CollatzResearch.WordTrace tailWord_7109313 prefixEnd_7109313 3650494692257648513892371 := by
  unfold tailWord_7109313
  simp only [CollatzResearch.WordTrace]
  refine ⟨259297947293180649840180593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172865298195453766560120395 259297947293180649840180593)
  ·
    refine ⟨194473460469885487380135445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259297947293180649840180593 194473460469885487380135445)
    ·
      refine ⟨9115943459525882220943849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 194473460469885487380135445 9115943459525882220943849)
      ·
        refine ⟨6836957594644411665707887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9115943459525882220943849 6836957594644411665707887)
        ·
          refine ⟨10255436391966617498561831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6836957594644411665707887 10255436391966617498561831)
          ·
            refine ⟨15383154587949926247842747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10255436391966617498561831 15383154587949926247842747)
            ·
              refine ⟨23074731881924889371764121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15383154587949926247842747 23074731881924889371764121)
              ·
                refine ⟨17306048911443667028823091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23074731881924889371764121 17306048911443667028823091)
                ·
                  refine ⟨25959073367165500543234637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17306048911443667028823091 25959073367165500543234637)
                  ·
                    refine ⟨9734652512687062703712989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25959073367165500543234637 9734652512687062703712989)
                    ·
                      refine ⟨3650494692257648513892371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9734652512687062703712989 3650494692257648513892371)
                      ·
                        rfl

theorem cell23_7109313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7109313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109313 prefixEnd_7109313 := by exact prefixLift 7109313
  have htrace : WordTrace (prefixWord ++ tailWord_7109313) baseStart_7109313 baseEnd_7109313 := by
    simpa [prefixWord, tailWord_7109313, baseEnd_7109313] using wordTrace_append hprefix tailTrace_7109313
  have hstable : (prefixWord ++ tailWord_7109313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109313).length < 2 ^ (prefixWord ++ tailWord_7109313).sum := by decide
  have hdescent : baseEnd_7109313 < baseStart_7109313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109349 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_7109349 : Nat := 118140960795 + 7109349 * 2 ^ 59
def prefixEnd_7109349 : Nat := 4983230072969 + 3 ^ 40 * 7109349 * 2
def baseEnd_7109349 : Nat := 3650513177561210373042205

theorem tailTrace_7109349 : CollatzResearch.WordTrace tailWord_7109349 prefixEnd_7109349 3650513177561210373042205 := by
  unfold tailWord_7109349
  simp only [CollatzResearch.WordTrace]
  refine ⟨259299260321050227988491101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172866173547366818658994067 259299260321050227988491101)
  ·
    refine ⟨97237222620393835495684163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259299260321050227988491101 97237222620393835495684163)
    ·
      refine ⟨145855833930590753243526245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97237222620393835495684163 145855833930590753243526245)
      ·
        refine ⟨27347968861985766233161171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145855833930590753243526245 27347968861985766233161171)
        ·
          refine ⟨41021953292978649349741757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27347968861985766233161171 41021953292978649349741757)
          ·
            refine ⟨15383232484866993506153159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41021953292978649349741757 15383232484866993506153159)
            ·
              refine ⟨23074848727300490259229739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15383232484866993506153159 23074848727300490259229739)
              ·
                refine ⟨34612273090950735388844609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23074848727300490259229739 34612273090950735388844609)
                ·
                  refine ⟨25959204818213051541633457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34612273090950735388844609 25959204818213051541633457)
                  ·
                    refine ⟨19469403613659788656225093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25959204818213051541633457 19469403613659788656225093)
                    ·
                      refine ⟨3650513177561210373042205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19469403613659788656225093 3650513177561210373042205)
                      ·
                        rfl

theorem cell23_7109349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_7109349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109349 prefixEnd_7109349 := by exact prefixLift 7109349
  have htrace : WordTrace (prefixWord ++ tailWord_7109349) baseStart_7109349 baseEnd_7109349 := by
    simpa [prefixWord, tailWord_7109349, baseEnd_7109349] using wordTrace_append hprefix tailTrace_7109349
  have hstable : (prefixWord ++ tailWord_7109349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109349).length < 2 ^ (prefixWord ++ tailWord_7109349).sum := by decide
  have hdescent : baseEnd_7109349 < baseStart_7109349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109432 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 10]
def baseStart_7109432 : Nat := 118140960795 + 7109432 * 2 ^ 59
def prefixEnd_7109432 : Nat := 4983230072969 + 3 ^ 40 * 7109432 * 2
def baseEnd_7109432 : Nat := 405617310717281505367147

theorem tailTrace_7109432 : CollatzResearch.WordTrace tailWord_7109432 prefixEnd_7109432 405617310717281505367147 := by
  unfold tailWord_7109432
  simp only [CollatzResearch.WordTrace]
  refine ⟨129651143789874766581881275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172868191719833022109175033 129651143789874766581881275)
  ·
    refine ⟨194476715684812149872821913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129651143789874766581881275 194476715684812149872821913)
    ·
      refine ⟨145857536763609112404616435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194476715684812149872821913 145857536763609112404616435)
      ·
        refine ⟨218786305145413668606924653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145857536763609112404616435 218786305145413668606924653)
        ·
          refine ⟨82044864429530125727596745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218786305145413668606924653 82044864429530125727596745)
          ·
            refine ⟨61533648322147594295697559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82044864429530125727596745 61533648322147594295697559)
            ·
              refine ⟨92300472483221391443546339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61533648322147594295697559 92300472483221391443546339)
              ·
                refine ⟨138450708724832087165319509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92300472483221391443546339 138450708724832087165319509)
                ·
                  refine ⟨405617310717281505367147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 138450708724832087165319509 405617310717281505367147)
                  ·
                    rfl

theorem cell23_7109432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 10].length) (baseStart_7109432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109432 prefixEnd_7109432 := by exact prefixLift 7109432
  have htrace : WordTrace (prefixWord ++ tailWord_7109432) baseStart_7109432 baseEnd_7109432 := by
    simpa [prefixWord, tailWord_7109432, baseEnd_7109432] using wordTrace_append hprefix tailTrace_7109432
  have hstable : (prefixWord ++ tailWord_7109432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109432).length < 2 ^ (prefixWord ++ tailWord_7109432).sum := by decide
  have hdescent : baseEnd_7109432 < baseStart_7109432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109466 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 6]
def baseStart_7109466 : Nat := 118140960795 + 7109466 * 2 ^ 59
def prefixEnd_7109466 : Nat := 4983230072969 + 3 ^ 40 * 7109466 * 2
def baseEnd_7109466 : Nat := 405619250533087379475463

theorem tailTrace_7109466 : CollatzResearch.WordTrace tailWord_7109466 prefixEnd_7109466 405619250533087379475463 := by
  unfold tailWord_7109466
  simp only [CollatzResearch.WordTrace]
  refine ⟨64825881915406589242625063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172869018441084237980333501 64825881915406589242625063)
  ·
    refine ⟨97238822873109883863937595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64825881915406589242625063 97238822873109883863937595)
    ·
      refine ⟨145858234309664825795906393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97238822873109883863937595 145858234309664825795906393)
      ·
        refine ⟨109393675732248619346929795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145858234309664825795906393 109393675732248619346929795)
        ·
          refine ⟨164090513598372929020394693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109393675732248619346929795 164090513598372929020394693)
          ·
            refine ⟨30766971299694924191324005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164090513598372929020394693 30766971299694924191324005)
            ·
              refine ⟨5768807118692798285873251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30766971299694924191324005 5768807118692798285873251)
              ·
                refine ⟨8653210678039197428809877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5768807118692798285873251 8653210678039197428809877)
                ·
                  refine ⟨405619250533087379475463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8653210678039197428809877 405619250533087379475463)
                  ·
                    rfl

theorem cell23_7109466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_7109466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109466 prefixEnd_7109466 := by exact prefixLift 7109466
  have htrace : WordTrace (prefixWord ++ tailWord_7109466) baseStart_7109466 baseEnd_7109466 := by
    simpa [prefixWord, tailWord_7109466, baseEnd_7109466] using wordTrace_append hprefix tailTrace_7109466
  have hstable : (prefixWord ++ tailWord_7109466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109466).length < 2 ^ (prefixWord ++ tailWord_7109466).sum := by decide
  have hdescent : baseEnd_7109466 < baseStart_7109466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109536 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 3]
def baseStart_7109536 : Nat := 118140960795 + 7109536 * 2 ^ 59
def prefixEnd_7109536 : Nat := 4983230072969 + 3 ^ 40 * 7109536 * 2
def baseEnd_7109536 : Nat := 3650609198443601141403845

theorem tailTrace_7109536 : CollatzResearch.WordTrace tailWord_7109536 prefixEnd_7109536 3650609198443601141403845 := by
  unfold tailWord_7109536
  simp only [CollatzResearch.WordTrace]
  refine ⟨129653040385686379462774231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172870720514248505950365641 129653040385686379462774231)
  ·
    refine ⟨194479560578529569194161347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129653040385686379462774231 194479560578529569194161347)
    ·
      refine ⟨291719340867794353791242021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194479560578529569194161347 291719340867794353791242021)
      ·
        refine ⟨54697376412711441335857879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291719340867794353791242021 54697376412711441335857879)
        ·
          refine ⟨82046064619067162003786819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54697376412711441335857879 82046064619067162003786819)
          ·
            refine ⟨123069096928600743005680229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82046064619067162003786819 123069096928600743005680229)
            ·
              refine ⟨23075455674112639313565043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123069096928600743005680229 23075455674112639313565043)
              ·
                refine ⟨34613183511168958970347565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23075455674112639313565043 34613183511168958970347565)
                ·
                  refine ⟨12979943816688359613880337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34613183511168958970347565 12979943816688359613880337)
                  ·
                    refine ⟨9734957862516269710410253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12979943816688359613880337 9734957862516269710410253)
                    ·
                      refine ⟨3650609198443601141403845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9734957862516269710410253 3650609198443601141403845)
                      ·
                        rfl

theorem cell23_7109536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_7109536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109536 prefixEnd_7109536 := by exact prefixLift 7109536
  have htrace : WordTrace (prefixWord ++ tailWord_7109536) baseStart_7109536 baseEnd_7109536 := by
    simpa [prefixWord, tailWord_7109536, baseEnd_7109536] using wordTrace_append hprefix tailTrace_7109536
  have hstable : (prefixWord ++ tailWord_7109536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109536).length < 2 ^ (prefixWord ++ tailWord_7109536).sum := by decide
  have hdescent : baseEnd_7109536 < baseStart_7109536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109583 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 1, 3, 3]
def baseStart_7109583 : Nat := 118140960795 + 7109583 * 2 ^ 59
def prefixEnd_7109583 : Nat := 4983230072969 + 3 ^ 40 * 7109583 * 2
def baseEnd_7109583 : Nat := 3650633332034362457516129

theorem tailTrace_7109583 : CollatzResearch.WordTrace tailWord_7109583 prefixEnd_7109583 3650633332034362457516129 := by
  unfold tailWord_7109583
  simp only [CollatzResearch.WordTrace]
  refine ⟨259307795002202485952509403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172871863334801657301672935 259307795002202485952509403)
  ·
    refine ⟨388961692503303728928764105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259307795002202485952509403 388961692503303728928764105)
    ·
      refine ⟨291721269377477796696573079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388961692503303728928764105 291721269377477796696573079)
      ·
        refine ⟨437581904066216695044859619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291721269377477796696573079 437581904066216695044859619)
        ·
          refine ⟨656372856099325042567289429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437581904066216695044859619 656372856099325042567289429)
          ·
            refine ⟨7691869407413965342585423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 656372856099325042567289429 7691869407413965342585423)
            ·
              refine ⟨11537804111120948013878135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7691869407413965342585423 11537804111120948013878135)
              ·
                refine ⟨17306706166681422020817203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11537804111120948013878135 17306706166681422020817203)
                ·
                  refine ⟨25960059250022133031225805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17306706166681422020817203 25960059250022133031225805)
                  ·
                    refine ⟨9735022218758299886709677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25960059250022133031225805 9735022218758299886709677)
                    ·
                      refine ⟨3650633332034362457516129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9735022218758299886709677 3650633332034362457516129)
                      ·
                        rfl

theorem cell23_7109583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 3, 3].length) (baseStart_7109583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109583 prefixEnd_7109583 := by exact prefixLift 7109583
  have htrace : WordTrace (prefixWord ++ tailWord_7109583) baseStart_7109583 baseEnd_7109583 := by
    simpa [prefixWord, tailWord_7109583, baseEnd_7109583] using wordTrace_append hprefix tailTrace_7109583
  have hstable : (prefixWord ++ tailWord_7109583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109583).length < 2 ^ (prefixWord ++ tailWord_7109583).sum := by decide
  have hdescent : baseEnd_7109583 < baseStart_7109583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109590 : List Nat := [5, 2, 1, 1, 2, 3, 2, 7]
def baseStart_7109590 : Nat := 118140960795 + 7109590 * 2 ^ 59
def prefixEnd_7109590 : Nat := 4983230072969 + 3 ^ 40 * 7109590 * 2
def baseEnd_7109590 : Nat := 135208775051812738152911

theorem tailTrace_7109590 : CollatzResearch.WordTrace tailWord_7109590 prefixEnd_7109590 135208775051812738152911 := by
  unfold tailWord_7109590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16206753144573570384250889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172872033542118084098676149 16206753144573570384250889)
  ·
    refine ⟨12155064858430177788188167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16206753144573570384250889 12155064858430177788188167)
    ·
      refine ⟨18232597287645266682282251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12155064858430177788188167 18232597287645266682282251)
      ·
        refine ⟨27348895931467900023423377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18232597287645266682282251 27348895931467900023423377)
        ·
          refine ⟨20511671948600925017567533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27348895931467900023423377 20511671948600925017567533)
          ·
            refine ⟨7691876980725346881587825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20511671948600925017567533 7691876980725346881587825)
            ·
              refine ⟨5768907735544010161190869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7691876980725346881587825 5768907735544010161190869)
              ·
                refine ⟨135208775051812738152911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5768907735544010161190869 135208775051812738152911)
                ·
                  rfl

theorem cell23_7109590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_7109590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109590 prefixEnd_7109590 := by exact prefixLift 7109590
  have htrace : WordTrace (prefixWord ++ tailWord_7109590) baseStart_7109590 baseEnd_7109590 := by
    simpa [prefixWord, tailWord_7109590, baseEnd_7109590] using wordTrace_append hprefix tailTrace_7109590
  have hstable : (prefixWord ++ tailWord_7109590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109590).length < 2 ^ (prefixWord ++ tailWord_7109590).sum := by decide
  have hdescent : baseEnd_7109590 < baseStart_7109590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109610 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_7109610 : Nat := 118140960795 + 7109610 * 2 ^ 59
def prefixEnd_7109610 : Nat := 4983230072969 + 3 ^ 40 * 7109610 * 2
def baseEnd_7109610 : Nat := 3650647196012033851878505

theorem tailTrace_7109610 : CollatzResearch.WordTrace tailWord_7109610 prefixEnd_7109610 3650647196012033851878505 := by
  unfold tailWord_7109610
  simp only [CollatzResearch.WordTrace]
  refine ⟨64827194943276167390935571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172872519848736446375828189 64827194943276167390935571)
  ·
    refine ⟨97240792414914251086403357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64827194943276167390935571 97240792414914251086403357)
    ·
      refine ⟨36465297155592844157401259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97240792414914251086403357 36465297155592844157401259)
      ·
        refine ⟨54697945733389266236101889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36465297155592844157401259 54697945733389266236101889)
        ·
          refine ⟨41023459300041949677076417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54697945733389266236101889 41023459300041949677076417)
          ·
            refine ⟨30767594475031462257807313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41023459300041949677076417 30767594475031462257807313)
            ·
              refine ⟨23075695856273596693355485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30767594475031462257807313 23075695856273596693355485)
              ·
                refine ⟨8653385946102598760008307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23075695856273596693355485 8653385946102598760008307)
                ·
                  refine ⟨12980078919153898140012461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8653385946102598760008307 12980078919153898140012461)
                  ·
                    refine ⟨4867529594682711802504673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12980078919153898140012461 4867529594682711802504673)
                    ·
                      refine ⟨3650647196012033851878505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867529594682711802504673 3650647196012033851878505)
                      ·
                        rfl

theorem cell23_7109610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_7109610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109610 prefixEnd_7109610 := by exact prefixLift 7109610
  have htrace : WordTrace (prefixWord ++ tailWord_7109610) baseStart_7109610 baseEnd_7109610 := by
    simpa [prefixWord, tailWord_7109610, baseEnd_7109610] using wordTrace_append hprefix tailTrace_7109610
  have hstable : (prefixWord ++ tailWord_7109610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109610).length < 2 ^ (prefixWord ++ tailWord_7109610).sum := by decide
  have hdescent : baseEnd_7109610 < baseStart_7109610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109634 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7109634 : Nat := 118140960795 + 7109634 * 2 ^ 59
def prefixEnd_7109634 : Nat := 4983230072969 + 3 ^ 40 * 7109634 * 2
def baseEnd_7109634 : Nat := 3650659519547741757978395

theorem tailTrace_7109634 : CollatzResearch.WordTrace tailWord_7109634 prefixEnd_7109634 3650659519547741757978395 := by
  unfold tailWord_7109634
  simp only [CollatzResearch.WordTrace]
  refine ⟨64827413781254430415653989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172873103416678481108410637 64827413781254430415653989)
  ·
    refine ⟨12155140083985205702935123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64827413781254430415653989 12155140083985205702935123)
    ·
      refine ⟨18232710125977808554402685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12155140083985205702935123 18232710125977808554402685)
      ·
        refine ⟨6837266297241678207901007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18232710125977808554402685 6837266297241678207901007)
        ·
          refine ⟨10255899445862517311851511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6837266297241678207901007 10255899445862517311851511)
          ·
            refine ⟨15383849168793775967777267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10255899445862517311851511 15383849168793775967777267)
            ·
              refine ⟨23075773753190663951665901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15383849168793775967777267 23075773753190663951665901)
              ·
                refine ⟨8653415157446498981874713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23075773753190663951665901 8653415157446498981874713)
                ·
                  refine ⟨6490061368084874236406035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8653415157446498981874713 6490061368084874236406035)
                  ·
                    refine ⟨9735092052127311354609053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6490061368084874236406035 9735092052127311354609053)
                    ·
                      refine ⟨3650659519547741757978395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9735092052127311354609053 3650659519547741757978395)
                      ·
                        rfl

theorem cell23_7109634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7109634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109634 prefixEnd_7109634 := by exact prefixLift 7109634
  have htrace : WordTrace (prefixWord ++ tailWord_7109634) baseStart_7109634 baseEnd_7109634 := by
    simpa [prefixWord, tailWord_7109634, baseEnd_7109634] using wordTrace_append hprefix tailTrace_7109634
  have hstable : (prefixWord ++ tailWord_7109634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109634).length < 2 ^ (prefixWord ++ tailWord_7109634).sum := by decide
  have hdescent : baseEnd_7109634 < baseStart_7109634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109649 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_7109649 : Nat := 118140960795 + 7109649 * 2 ^ 59
def prefixEnd_7109649 : Nat := 4983230072969 + 3 ^ 40 * 7109649 * 2
def baseEnd_7109649 : Nat := 3650667221757559199290825

theorem tailTrace_7109649 : CollatzResearch.WordTrace tailWord_7109649 prefixEnd_7109649 3650667221757559199290825 := by
  unfold tailWord_7109649
  simp only [CollatzResearch.WordTrace]
  refine ⟨259310202219963379224412001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172873468146642252816274667 259310202219963379224412001)
  ·
    refine ⟨194482651664972534418309001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259310202219963379224412001 194482651664972534418309001)
    ·
      refine ⟨145861988748729400813731751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194482651664972534418309001 145861988748729400813731751)
      ·
        refine ⟨218792983123094101220597627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145861988748729400813731751 218792983123094101220597627)
        ·
          refine ⟨328189474684641151830896441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218792983123094101220597627 328189474684641151830896441)
          ·
            refine ⟨246142106013480863873172331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328189474684641151830896441 246142106013480863873172331)
            ·
              refine ⟨369213159020221295809758497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246142106013480863873172331 369213159020221295809758497)
              ·
                refine ⟨276909869265165971857318873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369213159020221295809758497 276909869265165971857318873)
                ·
                  refine ⟨207682401948874478892989155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276909869265165971857318873 207682401948874478892989155)
                  ·
                    refine ⟨311523602923311718339483733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207682401948874478892989155 311523602923311718339483733)
                    ·
                      refine ⟨3650667221757559199290825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 311523602923311718339483733 3650667221757559199290825)
                      ·
                        rfl

theorem cell23_7109649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_7109649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109649 prefixEnd_7109649 := by exact prefixLift 7109649
  have htrace : WordTrace (prefixWord ++ tailWord_7109649) baseStart_7109649 baseEnd_7109649 := by
    simpa [prefixWord, tailWord_7109649, baseEnd_7109649] using wordTrace_append hprefix tailTrace_7109649
  have hstable : (prefixWord ++ tailWord_7109649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109649).length < 2 ^ (prefixWord ++ tailWord_7109649).sum := by decide
  have hdescent : baseEnd_7109649 < baseStart_7109649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109659 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 5, 7]
def baseStart_7109659 : Nat := 118140960795 + 7109659 * 2 ^ 59
def prefixEnd_7109659 : Nat := 4983230072969 + 3 ^ 40 * 7109659 * 2
def baseEnd_7109659 : Nat := 1216890785521368053388593

theorem tailTrace_7109659 : CollatzResearch.WordTrace tailWord_7109659 prefixEnd_7109659 1216890785521368053388593 := by
  unfold tailWord_7109659
  simp only [CollatzResearch.WordTrace]
  refine ⟨259310566949927150932276031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172873711299951433954850687 259310566949927150932276031)
  ·
    refine ⟨388965850424890726398414047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259310566949927150932276031 388965850424890726398414047)
    ·
      refine ⟨583448775637336089597621071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388965850424890726398414047 583448775637336089597621071)
      ·
        refine ⟨875173163456004134396431607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583448775637336089597621071 875173163456004134396431607)
        ·
          refine ⟨1312759745184006201594647411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875173163456004134396431607 1312759745184006201594647411)
          ·
            refine ⟨1969139617776009302391971117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312759745184006201594647411 1969139617776009302391971117)
            ·
              refine ⟨738427356666003488396989169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1969139617776009302391971117 738427356666003488396989169)
              ·
                refine ⟨553820517499502616297741877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738427356666003488396989169 553820517499502616297741877)
                ·
                  refine ⟨51920673515578370277913301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 553820517499502616297741877 51920673515578370277913301)
                  ·
                    refine ⟨1216890785521368053388593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51920673515578370277913301 1216890785521368053388593)
                    ·
                      rfl

theorem cell23_7109659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 7].length) (baseStart_7109659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109659 prefixEnd_7109659 := by exact prefixLift 7109659
  have htrace : WordTrace (prefixWord ++ tailWord_7109659) baseStart_7109659 baseEnd_7109659 := by
    simpa [prefixWord, tailWord_7109659, baseEnd_7109659] using wordTrace_append hprefix tailTrace_7109659
  have hstable : (prefixWord ++ tailWord_7109659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109659).length < 2 ^ (prefixWord ++ tailWord_7109659).sum := by decide
  have hdescent : baseEnd_7109659 < baseStart_7109659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109674 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_7109674 : Nat := 118140960795 + 7109674 * 2 ^ 59
def prefixEnd_7109674 : Nat := 4983230072969 + 3 ^ 40 * 7109674 * 2
def baseEnd_7109674 : Nat := 3650680058773921601478211

theorem tailTrace_7109674 : CollatzResearch.WordTrace tailWord_7109674 prefixEnd_7109674 3650680058773921601478211 := by
  unfold tailWord_7109674
  simp only [CollatzResearch.WordTrace]
  refine ⟨64827778511218202123518019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172874076029915205662714717 64827778511218202123518019)
  ·
    refine ⟨97241667766827303185277029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64827778511218202123518019 97241667766827303185277029)
    ·
      refine ⟨18232812706280119347239443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97241667766827303185277029 18232812706280119347239443)
      ·
        refine ⟨27349219059420179020859165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18232812706280119347239443 27349219059420179020859165)
        ·
          refine ⟨10255957147282567132822187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27349219059420179020859165 10255957147282567132822187)
          ·
            refine ⟨15383935720923850699233281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10255957147282567132822187 15383935720923850699233281)
            ·
              refine ⟨11537951790692888024424961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15383935720923850699233281 11537951790692888024424961)
              ·
                refine ⟨8653463843019666018318721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11537951790692888024424961 8653463843019666018318721)
                ·
                  refine ⟨6490097882264749513739041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8653463843019666018318721 6490097882264749513739041)
                  ·
                    refine ⟨4867573411698562135304281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6490097882264749513739041 4867573411698562135304281)
                    ·
                      refine ⟨3650680058773921601478211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867573411698562135304281 3650680058773921601478211)
                      ·
                        rfl

theorem cell23_7109674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_7109674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109674 prefixEnd_7109674 := by exact prefixLift 7109674
  have htrace : WordTrace (prefixWord ++ tailWord_7109674) baseStart_7109674 baseEnd_7109674 := by
    simpa [prefixWord, tailWord_7109674, baseEnd_7109674] using wordTrace_append hprefix tailTrace_7109674
  have hstable : (prefixWord ++ tailWord_7109674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109674).length < 2 ^ (prefixWord ++ tailWord_7109674).sum := by decide
  have hdescent : baseEnd_7109674 < baseStart_7109674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109676 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_7109676 : Nat := 118140960795 + 7109676 * 2 ^ 59
def prefixEnd_7109676 : Nat := 4983230072969 + 3 ^ 40 * 7109676 * 2
def baseEnd_7109676 : Nat := 1216893695245076864551067

theorem tailTrace_7109676 : CollatzResearch.WordTrace tailWord_7109676 prefixEnd_7109676 1216893695245076864551067 := by
  unfold tailWord_7109676
  simp only [CollatzResearch.WordTrace]
  refine ⟨129655593495432781417822441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172874124660577041890429921 129655593495432781417822441)
  ·
    refine ⟨97241695121574586063366831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129655593495432781417822441 97241695121574586063366831)
    ·
      refine ⟨145862542682361879095050247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97241695121574586063366831 145862542682361879095050247)
      ·
        refine ⟨218793814023542818642575371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145862542682361879095050247 218793814023542818642575371)
        ·
          refine ⟨328190721035314227963863057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218793814023542818642575371 328190721035314227963863057)
          ·
            refine ⟨246143040776485670972897293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328190721035314227963863057 246143040776485670972897293)
            ·
              refine ⟨92303640291182126614836485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246143040776485670972897293 92303640291182126614836485)
              ·
                refine ⟨17306932554596648740281841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92303640291182126614836485 17306932554596648740281841)
                ·
                  refine ⟨12980199415947486555211381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17306932554596648740281841 12980199415947486555211381)
                  ·
                    refine ⟨1216893695245076864551067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12980199415947486555211381 1216893695245076864551067)
                    ·
                      rfl

theorem cell23_7109676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_7109676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109676 prefixEnd_7109676 := by exact prefixLift 7109676
  have htrace : WordTrace (prefixWord ++ tailWord_7109676) baseStart_7109676 baseEnd_7109676 := by
    simpa [prefixWord, tailWord_7109676, baseEnd_7109676] using wordTrace_append hprefix tailTrace_7109676
  have hstable : (prefixWord ++ tailWord_7109676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109676).length < 2 ^ (prefixWord ++ tailWord_7109676).sum := by decide
  have hdescent : baseEnd_7109676 < baseStart_7109676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109696 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 4]
def baseStart_7109696 : Nat := 118140960795 + 7109696 * 2 ^ 59
def prefixEnd_7109696 : Nat := 4983230072969 + 3 ^ 40 * 7109696 * 2
def baseEnd_7109696 : Nat := 3650691355348320515403109

theorem tailTrace_7109696 : CollatzResearch.WordTrace tailWord_7109696 prefixEnd_7109696 3650691355348320515403109 := by
  unfold tailWord_7109696
  simp only [CollatzResearch.WordTrace]
  refine ⟨129655958225396553125686471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172874610967195404167581961 129655958225396553125686471)
  ·
    refine ⟨194483937338094829688529707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129655958225396553125686471 194483937338094829688529707)
    ·
      refine ⟨291725906007142244532794561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194483937338094829688529707 291725906007142244532794561)
      ·
        refine ⟨218794429505356683399595921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291725906007142244532794561 218794429505356683399595921)
        ·
          refine ⟨164095822129017512549696941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218794429505356683399595921 164095822129017512549696941)
          ·
            refine ⟨61535933298381567206136353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164095822129017512549696941 61535933298381567206136353)
            ·
              refine ⟨46151949973786175404602265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61535933298381567206136353 46151949973786175404602265)
              ·
                refine ⟨34613962480339631553451699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46151949973786175404602265 34613962480339631553451699)
                ·
                  refine ⟨51920943720509447330177549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34613962480339631553451699 51920943720509447330177549)
                  ·
                    refine ⟨19470353895191042748816581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51920943720509447330177549 19470353895191042748816581)
                    ·
                      refine ⟨3650691355348320515403109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19470353895191042748816581 3650691355348320515403109)
                      ·
                        rfl

theorem cell23_7109696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_7109696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109696 prefixEnd_7109696 := by exact prefixLift 7109696
  have htrace : WordTrace (prefixWord ++ tailWord_7109696) baseStart_7109696 baseEnd_7109696 := by
    simpa [prefixWord, tailWord_7109696, baseEnd_7109696] using wordTrace_append hprefix tailTrace_7109696
  have hstable : (prefixWord ++ tailWord_7109696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109696).length < 2 ^ (prefixWord ++ tailWord_7109696).sum := by decide
  have hdescent : baseEnd_7109696 < baseStart_7109696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109713 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 4]
def baseStart_7109713 : Nat := 118140960795 + 7109713 * 2 ^ 59
def prefixEnd_7109713 : Nat := 4983230072969 + 3 ^ 40 * 7109713 * 2
def baseEnd_7109713 : Nat := 3650700084519446948890531

theorem tailTrace_7109713 : CollatzResearch.WordTrace tailWord_7109713 prefixEnd_7109713 3650700084519446948890531 := by
  unfold tailWord_7109713
  simp only [CollatzResearch.WordTrace]
  refine ⟨259312536491731518154741793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172875024327821012103161195 259312536491731518154741793)
  ·
    refine ⟨194484402368798638616056345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259312536491731518154741793 194484402368798638616056345)
    ·
      refine ⟨145863301776598978962042259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194484402368798638616056345 145863301776598978962042259)
      ·
        refine ⟨218794952664898468443063389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145863301776598978962042259 218794952664898468443063389)
        ·
          refine ⟨82048107249336925666148771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218794952664898468443063389 82048107249336925666148771)
          ·
            refine ⟨123072160874005388499223157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82048107249336925666148771 123072160874005388499223157)
            ·
              refine ⟨11538015081938005171802171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123072160874005388499223157 11538015081938005171802171)
              ·
                refine ⟨17307022622907007757703257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11538015081938005171802171 17307022622907007757703257)
                ·
                  refine ⟨12980266967180255818277443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17307022622907007757703257 12980266967180255818277443)
                  ·
                    refine ⟨19470400450770383727416165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12980266967180255818277443 19470400450770383727416165)
                    ·
                      refine ⟨3650700084519446948890531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19470400450770383727416165 3650700084519446948890531)
                      ·
                        rfl

theorem cell23_7109713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_7109713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109713 prefixEnd_7109713 := by exact prefixLift 7109713
  have htrace : WordTrace (prefixWord ++ tailWord_7109713) baseStart_7109713 baseEnd_7109713 := by
    simpa [prefixWord, tailWord_7109713, baseEnd_7109713] using wordTrace_append hprefix tailTrace_7109713
  have hstable : (prefixWord ++ tailWord_7109713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109713).length < 2 ^ (prefixWord ++ tailWord_7109713).sum := by decide
  have hdescent : baseEnd_7109713 < baseStart_7109713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109733 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 4, 2, 3]
def baseStart_7109733 : Nat := 118140960795 + 7109733 * 2 ^ 59
def prefixEnd_7109733 : Nat := 4983230072969 + 3 ^ 40 * 7109733 * 2
def baseEnd_7109733 : Nat := 3650710354132536870640439

theorem tailTrace_7109733 : CollatzResearch.WordTrace tailWord_7109733 prefixEnd_7109733 3650710354132536870640439 := by
  unfold tailWord_7109733
  simp only [CollatzResearch.WordTrace]
  refine ⟨259313265951659061570469853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172875510634439374380313235 259313265951659061570469853)
  ·
    refine ⟨97242474731872148088926195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259313265951659061570469853 97242474731872148088926195)
    ·
      refine ⟨145863712097808222133389293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97242474731872148088926195 145863712097808222133389293)
      ·
        refine ⟨54698892036678083300020985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145863712097808222133389293 54698892036678083300020985)
        ·
          refine ⟨41024169027508562475015739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54698892036678083300020985 41024169027508562475015739)
          ·
            refine ⟨61536253541262843712523609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41024169027508562475015739 61536253541262843712523609)
            ·
              refine ⟨46152190155947132784392707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61536253541262843712523609 46152190155947132784392707)
              ·
                refine ⟨69228285233920699176589061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46152190155947132784392707 69228285233920699176589061)
                ·
                  refine ⟨12980303481360131095610449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69228285233920699176589061 12980303481360131095610449)
                  ·
                    refine ⟨9735227611020098321707837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12980303481360131095610449 9735227611020098321707837)
                    ·
                      refine ⟨3650710354132536870640439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9735227611020098321707837 3650710354132536870640439)
                      ·
                        rfl

theorem cell23_7109733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_7109733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109733 prefixEnd_7109733 := by exact prefixLift 7109733
  have htrace : WordTrace (prefixWord ++ tailWord_7109733) baseStart_7109733 baseEnd_7109733 := by
    simpa [prefixWord, tailWord_7109733, baseEnd_7109733] using wordTrace_append hprefix tailTrace_7109733
  have hstable : (prefixWord ++ tailWord_7109733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109733).length < 2 ^ (prefixWord ++ tailWord_7109733).sum := by decide
  have hdescent : baseEnd_7109733 < baseStart_7109733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109740 : List Nat := [2, 2, 1, 1, 3, 2, 1, 6, 1, 4]
def baseStart_7109740 : Nat := 118140960795 + 7109740 * 2 ^ 59
def prefixEnd_7109740 : Nat := 4983230072969 + 3 ^ 40 * 7109740 * 2
def baseEnd_7109740 : Nat := 1216904649499039447750969

theorem tailTrace_7109740 : CollatzResearch.WordTrace tailWord_7109740 prefixEnd_7109740 1216904649499039447750969 := by
  unfold tailWord_7109740
  simp only [CollatzResearch.WordTrace]
  refine ⟨129656760631316850882987337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172875680841755801177316449 129656760631316850882987337)
  ·
    refine ⟨97242570473487638162240503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129656760631316850882987337 97242570473487638162240503)
    ·
      refine ⟨145863855710231457243360755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97242570473487638162240503 145863855710231457243360755)
      ·
        refine ⟨218795783565347185865041133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145863855710231457243360755 218795783565347185865041133)
        ·
          refine ⟨82048418837005194699390425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218795783565347185865041133 82048418837005194699390425)
          ·
            refine ⟨61536314127753896024542819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82048418837005194699390425 61536314127753896024542819)
            ·
              refine ⟨92304471191630844036814229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61536314127753896024542819 92304471191630844036814229)
              ·
                refine ⟨4326772087107695814225667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92304471191630844036814229 4326772087107695814225667)
                ·
                  refine ⟨6490158130661543721338501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326772087107695814225667 6490158130661543721338501)
                  ·
                    refine ⟨1216904649499039447750969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490158130661543721338501 1216904649499039447750969)
                    ·
                      rfl

theorem cell23_7109740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_7109740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109740 prefixEnd_7109740 := by exact prefixLift 7109740
  have htrace : WordTrace (prefixWord ++ tailWord_7109740) baseStart_7109740 baseEnd_7109740 := by
    simpa [prefixWord, tailWord_7109740, baseEnd_7109740] using wordTrace_append hprefix tailTrace_7109740
  have hstable : (prefixWord ++ tailWord_7109740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109740).length < 2 ^ (prefixWord ++ tailWord_7109740).sum := by decide
  have hdescent : baseEnd_7109740 < baseStart_7109740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109756 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_7109756 : Nat := 118140960795 + 7109756 * 2 ^ 59
def prefixEnd_7109756 : Nat := 4983230072969 + 3 ^ 40 * 7109756 * 2
def baseEnd_7109756 : Nat := 3650722164187590280652833

theorem tailTrace_7109756 : CollatzResearch.WordTrace tailWord_7109756 prefixEnd_7109756 3650722164187590280652833 := by
  unfold tailWord_7109756
  simp only [CollatzResearch.WordTrace]
  refine ⟨129657052415287868249278561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172876069887050490999038081 129657052415287868249278561)
  ·
    refine ⟨97242789311465901186958921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129657052415287868249278561 97242789311465901186958921)
    ·
      refine ⟨72932091983599425890219191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97242789311465901186958921 72932091983599425890219191)
      ·
        refine ⟨109398137975399138835328787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72932091983599425890219191 109398137975399138835328787)
        ·
          refine ⟨164097206963098708252993181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109398137975399138835328787 164097206963098708252993181)
          ·
            refine ⟨61536452611162015594872443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164097206963098708252993181 61536452611162015594872443)
            ·
              refine ⟨92304678916743023392308665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61536452611162015594872443 92304678916743023392308665)
              ·
                refine ⟨69228509187557267544231499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92304678916743023392308665 69228509187557267544231499)
                ·
                  refine ⟨103842763781335901316347249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69228509187557267544231499 103842763781335901316347249)
                  ·
                    refine ⟨77882072836001925987260437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103842763781335901316347249 77882072836001925987260437)
                    ·
                      refine ⟨3650722164187590280652833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77882072836001925987260437 3650722164187590280652833)
                      ·
                        rfl

theorem cell23_7109756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_7109756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109756 prefixEnd_7109756 := by exact prefixLift 7109756
  have htrace : WordTrace (prefixWord ++ tailWord_7109756) baseStart_7109756 baseEnd_7109756 := by
    simpa [prefixWord, tailWord_7109756, baseEnd_7109756] using wordTrace_append hprefix tailTrace_7109756
  have hstable : (prefixWord ++ tailWord_7109756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109756).length < 2 ^ (prefixWord ++ tailWord_7109756).sum := by decide
  have hdescent : baseEnd_7109756 < baseStart_7109756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109774 : List Nat := [4, 1, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_7109774 : Nat := 118140960795 + 7109774 * 2 ^ 59
def prefixEnd_7109774 : Nat := 4983230072969 + 3 ^ 40 * 7109774 * 2
def baseEnd_7109774 : Nat := 1216910468946457070075917

theorem tailTrace_7109774 : CollatzResearch.WordTrace tailWord_7109774 prefixEnd_7109774 1216910468946457070075917 := by
  unfold tailWord_7109774
  simp only [CollatzResearch.WordTrace]
  refine ⟨32414345168063815696589047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172876507563007017048474917 32414345168063815696589047)
  ·
    refine ⟨48621517752095723544883571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32414345168063815696589047 48621517752095723544883571)
    ·
      refine ⟨72932276628143585317325357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48621517752095723544883571 72932276628143585317325357)
      ·
        refine ⟨27349603735553844493997009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72932276628143585317325357 27349603735553844493997009)
        ·
          refine ⟨20512202801665383370497757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27349603735553844493997009 20512202801665383370497757)
          ·
            refine ⟨7692076050624518763936659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20512202801665383370497757 7692076050624518763936659)
            ·
              refine ⟨11538114075936778145904989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692076050624518763936659 11538114075936778145904989)
              ·
                refine ⟨4326792778476291804714371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11538114075936778145904989 4326792778476291804714371)
                ·
                  refine ⟨6490189167714437707071557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326792778476291804714371 6490189167714437707071557)
                  ·
                    refine ⟨1216910468946457070075917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490189167714437707071557 1216910468946457070075917)
                    ·
                      rfl

theorem cell23_7109774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_7109774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109774 prefixEnd_7109774 := by exact prefixLift 7109774
  have htrace : WordTrace (prefixWord ++ tailWord_7109774) baseStart_7109774 baseEnd_7109774 := by
    simpa [prefixWord, tailWord_7109774, baseEnd_7109774] using wordTrace_append hprefix tailTrace_7109774
  have hstable : (prefixWord ++ tailWord_7109774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109774).length < 2 ^ (prefixWord ++ tailWord_7109774).sum := by decide
  have hdescent : baseEnd_7109774 < baseStart_7109774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109797 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 3, 1, 3]
def baseStart_7109797 : Nat := 118140960795 + 7109797 * 2 ^ 59
def prefixEnd_7109797 : Nat := 4983230072969 + 3 ^ 40 * 7109797 * 2
def baseEnd_7109797 : Nat := 3650743216894424620240145

theorem tailTrace_7109797 : CollatzResearch.WordTrace tailWord_7109797 prefixEnd_7109797 3650743216894424620240145 := by
  unfold tailWord_7109797
  simp only [CollatzResearch.WordTrace]
  refine ⟨259315600223427200500799645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172877066815618133667199763 259315600223427200500799645)
  ·
    refine ⟨97243350083785200187799867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259315600223427200500799645 97243350083785200187799867)
    ·
      refine ⟨145865025125677800281699801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97243350083785200187799867 145865025125677800281699801)
      ·
        refine ⟨109398768844258350211274851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145865025125677800281699801 109398768844258350211274851)
        ·
          refine ⟨164098153266387525316912277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109398768844258350211274851 164098153266387525316912277)
          ·
            refine ⟨7692100934361915249230263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164098153266387525316912277 7692100934361915249230263)
            ·
              refine ⟨11538151401542872873845395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692100934361915249230263 11538151401542872873845395)
              ·
                refine ⟨17307227102314309310768093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11538151401542872873845395 17307227102314309310768093)
                ·
                  refine ⟨6490210163367865991538035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17307227102314309310768093 6490210163367865991538035)
                  ·
                    refine ⟨9735315245051798987307053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6490210163367865991538035 9735315245051798987307053)
                    ·
                      refine ⟨3650743216894424620240145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9735315245051798987307053 3650743216894424620240145)
                      ·
                        rfl

theorem cell23_7109797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_7109797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109797 prefixEnd_7109797 := by exact prefixLift 7109797
  have htrace : WordTrace (prefixWord ++ tailWord_7109797) baseStart_7109797 baseEnd_7109797 := by
    simpa [prefixWord, tailWord_7109797, baseEnd_7109797] using wordTrace_append hprefix tailTrace_7109797
  have hstable : (prefixWord ++ tailWord_7109797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109797).length < 2 ^ (prefixWord ++ tailWord_7109797).sum := by decide
  have hdescent : baseEnd_7109797 < baseStart_7109797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109820 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_7109820 : Nat := 118140960795 + 7109820 * 2 ^ 59
def prefixEnd_7109820 : Nat := 4983230072969 + 3 ^ 40 * 7109820 * 2
def baseEnd_7109820 : Nat := 3650755026949478030252539

theorem tailTrace_7109820 : CollatzResearch.WordTrace tailWord_7109820 prefixEnd_7109820 3650755026949478030252539 := by
  unfold tailWord_7109820
  simp only [CollatzResearch.WordTrace]
  refine ⟨129658219551171937714443457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172877626068229250285924609 129658219551171937714443457)
  ·
    refine ⟨97243664663378953285832593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129658219551171937714443457 97243664663378953285832593)
    ·
      refine ⟨72932748497534214964374445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97243664663378953285832593 72932748497534214964374445)
      ·
        refine ⟨27349780686575330611640417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72932748497534214964374445 27349780686575330611640417)
        ·
          refine ⟨20512335514931497958730313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27349780686575330611640417 20512335514931497958730313)
          ·
            refine ⟨15384251636198623469047735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20512335514931497958730313 15384251636198623469047735)
            ·
              refine ⟨23076377454297935203571603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15384251636198623469047735 23076377454297935203571603)
              ·
                refine ⟨34614566181446902805357405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23076377454297935203571603 34614566181446902805357405)
                ·
                  refine ⟨12980462318042588552009027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34614566181446902805357405 12980462318042588552009027)
                  ·
                    refine ⟨19470693477063882828013541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12980462318042588552009027 19470693477063882828013541)
                    ·
                      refine ⟨3650755026949478030252539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19470693477063882828013541 3650755026949478030252539)
                      ·
                        rfl

theorem cell23_7109820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_7109820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109820 prefixEnd_7109820 := by exact prefixLift 7109820
  have htrace : WordTrace (prefixWord ++ tailWord_7109820) baseStart_7109820 baseEnd_7109820 := by
    simpa [prefixWord, tailWord_7109820, baseEnd_7109820] using wordTrace_append hprefix tailTrace_7109820
  have hstable : (prefixWord ++ tailWord_7109820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109820).length < 2 ^ (prefixWord ++ tailWord_7109820).sum := by decide
  have hdescent : baseEnd_7109820 < baseStart_7109820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109848 : List Nat := [2, 1, 2, 2, 6, 1, 2, 2, 1, 1, 3]
def baseStart_7109848 : Nat := 118140960795 + 7109848 * 2 ^ 59
def prefixEnd_7109848 : Nat := 4983230072969 + 3 ^ 40 * 7109848 * 2
def baseEnd_7109848 : Nat := 3650769404407803920702411

theorem tailTrace_7109848 : CollatzResearch.WordTrace tailWord_7109848 prefixEnd_7109848 3650769404407803920702411 := by
  unfold tailWord_7109848
  simp only [CollatzResearch.WordTrace]
  refine ⟨129658730173121218105453099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172878306897494957473937465 129658730173121218105453099)
  ·
    refine ⟨194488095259681827158179649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129658730173121218105453099 194488095259681827158179649)
    ·
      refine ⟨145866071444761370368634737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194488095259681827158179649 145866071444761370368634737)
      ·
        refine ⟨109399553583571027776476053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145866071444761370368634737 109399553583571027776476053)
        ·
          refine ⟨5128104074229891927022315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109399553583571027776476053 5128104074229891927022315)
          ·
            refine ⟨7692156111344837890533473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128104074229891927022315 7692156111344837890533473)
            ·
              refine ⟨5769117083508628417900105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7692156111344837890533473 5769117083508628417900105)
              ·
                refine ⟨4326837812631471313425079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5769117083508628417900105 4326837812631471313425079)
                ·
                  refine ⟨6490256718947206970137619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326837812631471313425079 6490256718947206970137619)
                  ·
                    refine ⟨9735385078420810455206429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6490256718947206970137619 9735385078420810455206429)
                    ·
                      refine ⟨3650769404407803920702411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9735385078420810455206429 3650769404407803920702411)
                      ·
                        rfl

theorem cell23_7109848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_7109848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109848 prefixEnd_7109848 := by exact prefixLift 7109848
  have htrace : WordTrace (prefixWord ++ tailWord_7109848) baseStart_7109848 baseEnd_7109848 := by
    simpa [prefixWord, tailWord_7109848, baseEnd_7109848] using wordTrace_append hprefix tailTrace_7109848
  have hstable : (prefixWord ++ tailWord_7109848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109848).length < 2 ^ (prefixWord ++ tailWord_7109848).sum := by decide
  have hdescent : baseEnd_7109848 < baseStart_7109848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109870 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_7109870 : Nat := 118140960795 + 7109870 * 2 ^ 59
def prefixEnd_7109870 : Nat := 4983230072969 + 3 ^ 40 * 7109870 * 2
def baseEnd_7109870 : Nat := 3650780700982202834627309

theorem tailTrace_7109870 : CollatzResearch.WordTrace tailWord_7109870 prefixEnd_7109870 3650780700982202834627309 := by
  unfold tailWord_7109870
  simp only [CollatzResearch.WordTrace]
  refine ⟨32414782844020341746025883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172878841834775155978804709 32414782844020341746025883)
  ·
    refine ⟨48622174266030512619038825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32414782844020341746025883 48622174266030512619038825)
    ·
      refine ⟨36466630699522884464279119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48622174266030512619038825 36466630699522884464279119)
      ·
        refine ⟨54699946049284326696418679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36466630699522884464279119 54699946049284326696418679)
        ·
          refine ⟨82049919073926490044628019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54699946049284326696418679 82049919073926490044628019)
          ·
            refine ⟨123074878610889735066942029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82049919073926490044628019 123074878610889735066942029)
            ·
              refine ⟨46153079479083650650103261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123074878610889735066942029 46153079479083650650103261)
              ·
                refine ⟨17307404804656368993788723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46153079479083650650103261 17307404804656368993788723)
                ·
                  refine ⟨25961107206984553490683085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17307404804656368993788723 25961107206984553490683085)
                  ·
                    refine ⟨9735415202619207559006157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25961107206984553490683085 9735415202619207559006157)
                    ·
                      refine ⟨3650780700982202834627309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9735415202619207559006157 3650780700982202834627309)
                      ·
                        rfl

theorem cell23_7109870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_7109870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109870 prefixEnd_7109870 := by exact prefixLift 7109870
  have htrace : WordTrace (prefixWord ++ tailWord_7109870) baseStart_7109870 baseEnd_7109870 := by
    simpa [prefixWord, tailWord_7109870, baseEnd_7109870] using wordTrace_append hprefix tailTrace_7109870
  have hstable : (prefixWord ++ tailWord_7109870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109870).length < 2 ^ (prefixWord ++ tailWord_7109870).sum := by decide
  have hdescent : baseEnd_7109870 < baseStart_7109870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109897 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 1, 3, 2]
def baseStart_7109897 : Nat := 118140960795 + 7109897 * 2 ^ 59
def prefixEnd_7109897 : Nat := 4983230072969 + 3 ^ 40 * 7109897 * 2
def baseEnd_7109897 : Nat := 3650794564959874228989685

theorem tailTrace_7109897 : CollatzResearch.WordTrace tailWord_7109897 prefixEnd_7109897 3650794564959874228989685 := by
  unfold tailWord_7109897
  simp only [CollatzResearch.WordTrace]
  refine ⟨259319247523064917579439945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172879498348709945052959963 259319247523064917579439945)
  ·
    refine ⟨194489435642298688184579959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259319247523064917579439945 194489435642298688184579959)
    ·
      refine ⟨291734153463448032276869939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194489435642298688184579959 291734153463448032276869939)
      ·
        refine ⟨437601230195172048415304909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291734153463448032276869939 437601230195172048415304909)
        ·
          refine ⟨164100461323189518155739341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437601230195172048415304909 164100461323189518155739341)
          ·
            refine ⟨61537672996196069308402253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164100461323189518155739341 61537672996196069308402253)
            ·
              refine ⟨23076627373573525990650845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61537672996196069308402253 23076627373573525990650845)
              ·
                refine ⟨8653735265090072246494067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23076627373573525990650845 8653735265090072246494067)
                ·
                  refine ⟨12980602897635108369741101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8653735265090072246494067 12980602897635108369741101)
                  ·
                    refine ⟨4867726086613165638652913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12980602897635108369741101 4867726086613165638652913)
                    ·
                      refine ⟨3650794564959874228989685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867726086613165638652913 3650794564959874228989685)
                      ·
                        rfl

theorem cell23_7109897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 3, 2].length) (baseStart_7109897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109897 prefixEnd_7109897 := by exact prefixLift 7109897
  have htrace : WordTrace (prefixWord ++ tailWord_7109897) baseStart_7109897 baseEnd_7109897 := by
    simpa [prefixWord, tailWord_7109897, baseEnd_7109897] using wordTrace_append hprefix tailTrace_7109897
  have hstable : (prefixWord ++ tailWord_7109897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109897).length < 2 ^ (prefixWord ++ tailWord_7109897).sum := by decide
  have hdescent : baseEnd_7109897 < baseStart_7109897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109997 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_7109997 : Nat := 118140960795 + 7109997 * 2 ^ 59
def prefixEnd_7109997 : Nat := 4983230072969 + 3 ^ 40 * 7109997 * 2
def baseEnd_7109997 : Nat := 1216948637675107945913075

theorem tailTrace_7109997 : CollatzResearch.WordTrace tailWord_7109997 prefixEnd_7109997 1216948637675107945913075 := by
  unfold tailWord_7109997
  simp only [CollatzResearch.WordTrace]
  refine ⟨259322894822702634658080245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172881929881801756438720163 259322894822702634658080245)
  ·
    refine ⟨24311521389628371999195023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259322894822702634658080245 24311521389628371999195023)
    ·
      refine ⟨36467282084442557998792535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24311521389628371999195023 36467282084442557998792535)
      ·
        refine ⟨54700923126663836998188803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36467282084442557998792535 54700923126663836998188803)
        ·
          refine ⟨82051384689995755497283205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54700923126663836998188803 82051384689995755497283205)
          ·
            refine ⟨15384634629374204155740601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82051384689995755497283205 15384634629374204155740601)
            ·
              refine ⟨11538475972030653116805451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15384634629374204155740601 11538475972030653116805451)
              ·
                refine ⟨17307713958045979675208177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11538475972030653116805451 17307713958045979675208177)
                ·
                  refine ⟨12980785468534484756406133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17307713958045979675208177 12980785468534484756406133)
                  ·
                    refine ⟨1216948637675107945913075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12980785468534484756406133 1216948637675107945913075)
                    ·
                      rfl

theorem cell23_7109997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_7109997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109997 prefixEnd_7109997 := by exact prefixLift 7109997
  have htrace : WordTrace (prefixWord ++ tailWord_7109997) baseStart_7109997 baseEnd_7109997 := by
    simpa [prefixWord, tailWord_7109997, baseEnd_7109997] using wordTrace_append hprefix tailTrace_7109997
  have hstable : (prefixWord ++ tailWord_7109997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109997).length < 2 ^ (prefixWord ++ tailWord_7109997).sum := by decide
  have hdescent : baseEnd_7109997 < baseStart_7109997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110003 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 5]
def baseStart_7110003 : Nat := 118140960795 + 7110003 * 2 ^ 59
def prefixEnd_7110003 : Nat := 4983230072969 + 3 ^ 40 * 7110003 * 2
def baseEnd_7110003 : Nat := 3650848993909250814264197

theorem tailTrace_7110003 : CollatzResearch.WordTrace tailWord_7110003 prefixEnd_7110003 3650848993909250814264197 := by
  unfold tailWord_7110003
  simp only [CollatzResearch.WordTrace]
  refine ⟨259323113660680897682798663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172882075773787265121865775 259323113660680897682798663)
  ·
    refine ⟨388984670491021346524197995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259323113660680897682798663 388984670491021346524197995)
    ·
      refine ⟨583477005736532019786296993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388984670491021346524197995 583477005736532019786296993)
      ·
        refine ⟨437607754302399014839722745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583477005736532019786296993 437607754302399014839722745)
        ·
          refine ⟨328205815726799261129792059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437607754302399014839722745 328205815726799261129792059)
          ·
            refine ⟨492308723590198891694688089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328205815726799261129792059 492308723590198891694688089)
            ·
              refine ⟨369231542692649168771016067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492308723590198891694688089 369231542692649168771016067)
              ·
                refine ⟨553847314038973753156524101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369231542692649168771016067 553847314038973753156524101)
                ·
                  refine ⟨103846371382307578716848269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 553847314038973753156524101 103846371382307578716848269)
                  ·
                    refine ⟨38942389268365342018818101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103846371382307578716848269 38942389268365342018818101)
                    ·
                      refine ⟨3650848993909250814264197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38942389268365342018818101 3650848993909250814264197)
                      ·
                        rfl

theorem cell23_7110003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_7110003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110003 prefixEnd_7110003 := by exact prefixLift 7110003
  have htrace : WordTrace (prefixWord ++ tailWord_7110003) baseStart_7110003 baseEnd_7110003 := by
    simpa [prefixWord, tailWord_7110003, baseEnd_7110003] using wordTrace_append hprefix tailTrace_7110003
  have hstable : (prefixWord ++ tailWord_7110003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110003).length < 2 ^ (prefixWord ++ tailWord_7110003).sum := by decide
  have hdescent : baseEnd_7110003 < baseStart_7110003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110010 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 5, 4]
def baseStart_7110010 : Nat := 118140960795 + 7110010 * 2 ^ 59
def prefixEnd_7110010 : Nat := 4983230072969 + 3 ^ 40 * 7110010 * 2
def baseEnd_7110010 : Nat := 1216950862757944095625555

theorem tailTrace_7110010 : CollatzResearch.WordTrace tailWord_7110010 prefixEnd_7110010 1216950862757944095625555 := by
  unfold tailWord_7110010
  simp only [CollatzResearch.WordTrace]
  refine ⟨64830842242913884469575871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172882245981103691918868989 64830842242913884469575871)
  ·
    refine ⟨97246263364370826704363807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64830842242913884469575871 97246263364370826704363807)
    ·
      refine ⟨145869395046556240056545711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97246263364370826704363807 145869395046556240056545711)
      ·
        refine ⟨218804092569834360084818567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145869395046556240056545711 218804092569834360084818567)
        ·
          refine ⟨328206138854751540127227851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218804092569834360084818567 328206138854751540127227851)
          ·
            refine ⟨492309208282127310190841777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328206138854751540127227851 492309208282127310190841777)
            ·
              refine ⟨369231906211595482643131333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492309208282127310190841777 369231906211595482643131333)
              ·
                refine ⟨69230982414674152995587125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369231906211595482643131333 69230982414674152995587125)
                ·
                  refine ⟨6490404601375701843336293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69230982414674152995587125 6490404601375701843336293)
                  ·
                    refine ⟨1216950862757944095625555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490404601375701843336293 1216950862757944095625555)
                    ·
                      rfl

theorem cell23_7110010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_7110010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110010 prefixEnd_7110010 := by exact prefixLift 7110010
  have htrace : WordTrace (prefixWord ++ tailWord_7110010) baseStart_7110010 baseEnd_7110010 := by
    simpa [prefixWord, tailWord_7110010, baseEnd_7110010] using wordTrace_append hprefix tailTrace_7110010
  have hstable : (prefixWord ++ tailWord_7110010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110010).length < 2 ^ (prefixWord ++ tailWord_7110010).sum := by decide
  have hdescent : baseEnd_7110010 < baseStart_7110010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110018 : List Nat := [3, 4, 2, 1, 1, 3, 2, 2, 5]
def baseStart_7110018 : Nat := 118140960795 + 7110018 * 2 ^ 59
def prefixEnd_7110018 : Nat := 4983230072969 + 3 ^ 40 * 7110018 * 2
def baseEnd_7110018 : Nat := 405650744013229806175181

theorem tailTrace_7110018 : CollatzResearch.WordTrace tailWord_7110018 prefixEnd_7110018 405650744013229806175181 := by
  unfold tailWord_7110018
  simp only [CollatzResearch.WordTrace]
  refine ⟨64830915188906638811148677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172882440503751036829729805 64830915188906638811148677)
  ·
    refine ⟨12155796597919994777090377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64830915188906638811148677 12155796597919994777090377)
    ·
      refine ⟨9116847448439996082817783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12155796597919994777090377 9116847448439996082817783)
      ·
        refine ⟨13675271172659994124226675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9116847448439996082817783 13675271172659994124226675)
        ·
          refine ⟨20512906758989991186340013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13675271172659994124226675 20512906758989991186340013)
          ·
            refine ⟨7692340034621246694877505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20512906758989991186340013 7692340034621246694877505)
            ·
              refine ⟨5769255025965935021158129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7692340034621246694877505 5769255025965935021158129)
              ·
                refine ⟨4326941269474451265868597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5769255025965935021158129 4326941269474451265868597)
                ·
                  refine ⟨405650744013229806175181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4326941269474451265868597 405650744013229806175181)
                  ·
                    rfl

theorem cell23_7110018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_7110018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110018 prefixEnd_7110018 := by exact prefixLift 7110018
  have htrace : WordTrace (prefixWord ++ tailWord_7110018) baseStart_7110018 baseEnd_7110018 := by
    simpa [prefixWord, tailWord_7110018, baseEnd_7110018] using wordTrace_append hprefix tailTrace_7110018
  have hstable : (prefixWord ++ tailWord_7110018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110018).length < 2 ^ (prefixWord ++ tailWord_7110018).sum := by decide
  have hdescent : baseEnd_7110018 < baseStart_7110018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110043 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 8]
def baseStart_7110043 : Nat := 118140960795 + 7110043 * 2 ^ 59
def prefixEnd_7110043 : Nat := 4983230072969 + 3 ^ 40 * 7110043 * 2
def baseEnd_7110043 : Nat := 3650869533135430657764013

theorem tailTrace_7110043 : CollatzResearch.WordTrace tailWord_7110043 prefixEnd_7110043 3650869533135430657764013 := by
  unfold tailWord_7110043
  simp only [CollatzResearch.WordTrace]
  refine ⟨259324572580535984514254783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172883048387023989676169855 259324572580535984514254783)
  ·
    refine ⟨388986858870803976771382175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259324572580535984514254783 388986858870803976771382175)
    ·
      refine ⟨583480288306205965157073263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388986858870803976771382175 583480288306205965157073263)
      ·
        refine ⟨875220432459308947735609895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583480288306205965157073263 875220432459308947735609895)
        ·
          refine ⟨1312830648688963421603414843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875220432459308947735609895 1312830648688963421603414843)
          ·
            refine ⟨1969245973033445132405122265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312830648688963421603414843 1969245973033445132405122265)
            ·
              refine ⟨1476934479775083849303841699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1969245973033445132405122265 1476934479775083849303841699)
              ·
                refine ⟨2215401719662625773955762549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476934479775083849303841699 2215401719662625773955762549)
                ·
                  refine ⟨207693911218371166308352739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2215401719662625773955762549 207693911218371166308352739)
                  ·
                    refine ⟨311540866827556749462529109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207693911218371166308352739 311540866827556749462529109)
                    ·
                      refine ⟨3650869533135430657764013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 311540866827556749462529109 3650869533135430657764013)
                      ·
                        rfl

theorem cell23_7110043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_7110043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110043 prefixEnd_7110043 := by exact prefixLift 7110043
  have htrace : WordTrace (prefixWord ++ tailWord_7110043) baseStart_7110043 baseEnd_7110043 := by
    simpa [prefixWord, tailWord_7110043, baseEnd_7110043] using wordTrace_append hprefix tailTrace_7110043
  have hstable : (prefixWord ++ tailWord_7110043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110043).length < 2 ^ (prefixWord ++ tailWord_7110043).sum := by decide
  have hdescent : baseEnd_7110043 < baseStart_7110043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110061 : List Nat := [1, 5, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_7110061 : Nat := 118140960795 + 7110061 * 2 ^ 59
def prefixEnd_7110061 : Nat := 4983230072969 + 3 ^ 40 * 7110061 * 2
def baseEnd_7110061 : Nat := 1216959591929070529112977

theorem tailTrace_7110061 : CollatzResearch.WordTrace tailWord_7110061 prefixEnd_7110061 1216959591929070529112977 := by
  unfold tailWord_7110061
  simp only [CollatzResearch.WordTrace]
  refine ⟨259325229094470773588410037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172883486062980515725606691 259325229094470773588410037)
  ·
    refine ⟨24311740227606635023913441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259325229094470773588410037 24311740227606635023913441)
    ·
      refine ⟨18233805170704976267935081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24311740227606635023913441 18233805170704976267935081)
      ·
        refine ⟨13675353878028732200951311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18233805170704976267935081 13675353878028732200951311)
        ·
          refine ⟨20513030817043098301426967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13675353878028732200951311 20513030817043098301426967)
          ·
            refine ⟨30769546225564647452140451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20513030817043098301426967 30769546225564647452140451)
            ·
              refine ⟨46154319338346971178210677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30769546225564647452140451 46154319338346971178210677)
              ·
                refine ⟨4326967437970028547957251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46154319338346971178210677 4326967437970028547957251)
                ·
                  refine ⟨6490451156955042821935877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326967437970028547957251 6490451156955042821935877)
                  ·
                    refine ⟨1216959591929070529112977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490451156955042821935877 1216959591929070529112977)
                    ·
                      rfl

theorem cell23_7110061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_7110061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110061 prefixEnd_7110061 := by exact prefixLift 7110061
  have htrace : WordTrace (prefixWord ++ tailWord_7110061) baseStart_7110061 baseEnd_7110061 := by
    simpa [prefixWord, tailWord_7110061, baseEnd_7110061] using wordTrace_append hprefix tailTrace_7110061
  have hstable : (prefixWord ++ tailWord_7110061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110061).length < 2 ^ (prefixWord ++ tailWord_7110061).sum := by decide
  have hdescent : baseEnd_7110061 < baseStart_7110061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110134 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_7110134 : Nat := 118140960795 + 7110134 * 2 ^ 59
def prefixEnd_7110134 : Nat := 4983230072969 + 3 ^ 40 * 7110134 * 2
def baseEnd_7110134 : Nat := 1216972086624996600575365

theorem tailTrace_7110134 : CollatzResearch.WordTrace tailWord_7110134 prefixEnd_7110134 1216972086624996600575365 := by
  unfold tailWord_7110134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16207993226450394190988591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172885261082137538037211637 16207993226450394190988591)
  ·
    refine ⟨24311989839675591286482887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16207993226450394190988591 24311989839675591286482887)
    ·
      refine ⟨36467984759513386929724331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24311989839675591286482887 36467984759513386929724331)
      ·
        refine ⟨54701977139270080394586497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36467984759513386929724331 54701977139270080394586497)
        ·
          refine ⟨41026482854452560295939873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54701977139270080394586497 41026482854452560295939873)
          ·
            refine ⟨30769862140839420221954905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41026482854452560295939873 30769862140839420221954905)
            ·
              refine ⟨23077396605629565166466179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30769862140839420221954905 23077396605629565166466179)
              ·
                refine ⟨34616094908444347749699269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23077396605629565166466179 34616094908444347749699269)
                ·
                  refine ⟨6490517795333315203068613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34616094908444347749699269 6490517795333315203068613)
                  ·
                    refine ⟨1216972086624996600575365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490517795333315203068613 1216972086624996600575365)
                    ·
                      rfl

theorem cell23_7110134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_7110134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110134 prefixEnd_7110134 := by exact prefixLift 7110134
  have htrace : WordTrace (prefixWord ++ tailWord_7110134) baseStart_7110134 baseEnd_7110134 := by
    simpa [prefixWord, tailWord_7110134, baseEnd_7110134] using wordTrace_append hprefix tailTrace_7110134
  have hstable : (prefixWord ++ tailWord_7110134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110134).length < 2 ^ (prefixWord ++ tailWord_7110134).sum := by decide
  have hdescent : baseEnd_7110134 < baseStart_7110134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110141 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 3, 2, 2]
def baseStart_7110141 : Nat := 118140960795 + 7110141 * 2 ^ 59
def prefixEnd_7110141 : Nat := 4983230072969 + 3 ^ 40 * 7110141 * 2
def baseEnd_7110141 : Nat := 3650919854239571274338563

theorem tailTrace_7110141 : CollatzResearch.WordTrace tailWord_7110141 prefixEnd_7110141 3650919854239571274338563 := by
  unfold tailWord_7110141
  simp only [CollatzResearch.WordTrace]
  refine ⟨259328146934180947251322277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172885431289453964834214851 259328146934180947251322277)
  ·
    refine ⟨48624027550158927609622927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259328146934180947251322277 48624027550158927609622927)
    ·
      refine ⟨72936041325238391414434391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48624027550158927609622927 72936041325238391414434391)
      ·
        refine ⟨109404061987857587121651587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72936041325238391414434391 109404061987857587121651587)
        ·
          refine ⟨164106092981786380682477381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109404061987857587121651587 164106092981786380682477381)
          ·
            refine ⟨30769892434084946377964509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164106092981786380682477381 30769892434084946377964509)
            ·
              refine ⟨11538709662781854891736691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30769892434084946377964509 11538709662781854891736691)
              ·
                refine ⟨17308064494172782337605037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11538709662781854891736691 17308064494172782337605037)
                ·
                  refine ⟨6490524185314793376601889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17308064494172782337605037 6490524185314793376601889)
                  ·
                    refine ⟨4867893138986095032451417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6490524185314793376601889 4867893138986095032451417)
                    ·
                      refine ⟨3650919854239571274338563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867893138986095032451417 3650919854239571274338563)
                      ·
                        rfl

theorem cell23_7110141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_7110141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110141 prefixEnd_7110141 := by exact prefixLift 7110141
  have htrace : WordTrace (prefixWord ++ tailWord_7110141) baseStart_7110141 baseEnd_7110141 := by
    simpa [prefixWord, tailWord_7110141, baseEnd_7110141] using wordTrace_append hprefix tailTrace_7110141
  have hstable : (prefixWord ++ tailWord_7110141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110141).length < 2 ^ (prefixWord ++ tailWord_7110141).sum := by decide
  have hdescent : baseEnd_7110141 < baseStart_7110141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110151 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 2, 4]
def baseStart_7110151 : Nat := 118140960795 + 7110151 * 2 ^ 59
def prefixEnd_7110151 : Nat := 4983230072969 + 3 ^ 40 * 7110151 * 2
def baseEnd_7110151 : Nat := 1216974996348705411737839

theorem tailTrace_7110151 : CollatzResearch.WordTrace tailWord_7110151 prefixEnd_7110151 1216974996348705411737839 := by
  unfold tailWord_7110151
  simp only [CollatzResearch.WordTrace]
  refine ⟨259328511664144718959186307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172885674442763145972790871 259328511664144718959186307)
  ·
    refine ⟨388992767496217078438779461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259328511664144718959186307 388992767496217078438779461)
    ·
      refine ⟨72936143905540702207271149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388992767496217078438779461 72936143905540702207271149)
      ·
        refine ⟨27351053964577763327726681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72936143905540702207271149 27351053964577763327726681)
        ·
          refine ⟨20513290473433322495795011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27351053964577763327726681 20513290473433322495795011)
          ·
            refine ⟨30769935710149983743692517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20513290473433322495795011 30769935710149983743692517)
            ·
              refine ⟨5769362945653121951942347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30769935710149983743692517 5769362945653121951942347)
              ·
                refine ⟨8654044418479682927913521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5769362945653121951942347 8654044418479682927913521)
                ·
                  refine ⟨6490533313859762195935141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8654044418479682927913521 6490533313859762195935141)
                  ·
                    refine ⟨1216974996348705411737839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490533313859762195935141 1216974996348705411737839)
                    ·
                      rfl

theorem cell23_7110151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_7110151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110151 prefixEnd_7110151 := by exact prefixLift 7110151
  have htrace : WordTrace (prefixWord ++ tailWord_7110151) baseStart_7110151 baseEnd_7110151 := by
    simpa [prefixWord, tailWord_7110151, baseEnd_7110151] using wordTrace_append hprefix tailTrace_7110151
  have hstable : (prefixWord ++ tailWord_7110151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110151).length < 2 ^ (prefixWord ++ tailWord_7110151).sum := by decide
  have hdescent : baseEnd_7110151 < baseStart_7110151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110158 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4]
def baseStart_7110158 : Nat := 118140960795 + 7110158 * 2 ^ 59
def prefixEnd_7110158 : Nat := 4983230072969 + 3 ^ 40 * 7110158 * 2
def baseEnd_7110158 : Nat := 3650928583410697707825985

theorem tailTrace_7110158 : CollatzResearch.WordTrace tailWord_7110158 prefixEnd_7110158 3650928583410697707825985 := by
  unfold tailWord_7110158
  simp only [CollatzResearch.WordTrace]
  refine ⟨32416095871889919894336391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172885844650079572769794085 32416095871889919894336391)
  ·
    refine ⟨48624143807834879841504587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32416095871889919894336391 48624143807834879841504587)
    ·
      refine ⟨72936215711752319762256881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48624143807834879841504587 72936215711752319762256881)
      ·
        refine ⟨54702161783814239821692661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72936215711752319762256881 54702161783814239821692661)
        ·
          refine ⟨5128327667232584983283687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54702161783814239821692661 5128327667232584983283687)
          ·
            refine ⟨7692491500848877474925531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128327667232584983283687 7692491500848877474925531)
            ·
              refine ⟨11538737251273316212388297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692491500848877474925531 11538737251273316212388297)
              ·
                refine ⟨8654052938454987159291223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11538737251273316212388297 8654052938454987159291223)
                ·
                  refine ⟨12981079407682480738936835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8654052938454987159291223 12981079407682480738936835)
                  ·
                    refine ⟨19471619111523721108405253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12981079407682480738936835 19471619111523721108405253)
                    ·
                      refine ⟨3650928583410697707825985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19471619111523721108405253 3650928583410697707825985)
                      ·
                        rfl

theorem cell23_7110158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_7110158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110158 prefixEnd_7110158 := by exact prefixLift 7110158
  have htrace : WordTrace (prefixWord ++ tailWord_7110158) baseStart_7110158 baseEnd_7110158 := by
    simpa [prefixWord, tailWord_7110158, baseEnd_7110158] using wordTrace_append hprefix tailTrace_7110158
  have hstable : (prefixWord ++ tailWord_7110158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110158).length < 2 ^ (prefixWord ++ tailWord_7110158).sum := by decide
  have hdescent : baseEnd_7110158 < baseStart_7110158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110197 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_7110197 : Nat := 118140960795 + 7110197 * 2 ^ 59
def prefixEnd_7110197 : Nat := 4983230072969 + 3 ^ 40 * 7110197 * 2
def baseEnd_7110197 : Nat := 3650948609156223055238305

theorem tailTrace_7110197 : CollatzResearch.WordTrace tailWord_7110197 prefixEnd_7110197 3650948609156223055238305 := by
  unfold tailWord_7110197
  simp only [CollatzResearch.WordTrace]
  refine ⟨259330189421978068815360845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172886792947985379210240563 259330189421978068815360845)
  ·
    refine ⟨97248821033241775805760317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259330189421978068815360845 97248821033241775805760317)
    ·
      refine ⟨36468307887465665927160119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97248821033241775805760317 36468307887465665927160119)
      ·
        refine ⟨54702461831198498890740179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36468307887465665927160119 54702461831198498890740179)
        ·
          refine ⟨82053692746797748336110269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54702461831198498890740179 82053692746797748336110269)
          ·
            refine ⟨30770134780049155626041351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82053692746797748336110269 30770134780049155626041351)
            ·
              refine ⟨46155202170073733439062027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30770134780049155626041351 46155202170073733439062027)
              ·
                refine ⟨69232803255110600158593041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46155202170073733439062027 69232803255110600158593041)
                ·
                  refine ⟨51924602441332950118944781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69232803255110600158593041 51924602441332950118944781)
                  ·
                    refine ⟨19471725915499856294604293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51924602441332950118944781 19471725915499856294604293)
                    ·
                      refine ⟨3650948609156223055238305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19471725915499856294604293 3650948609156223055238305)
                      ·
                        rfl

theorem cell23_7110197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_7110197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110197 prefixEnd_7110197 := by exact prefixLift 7110197
  have htrace : WordTrace (prefixWord ++ tailWord_7110197) baseStart_7110197 baseEnd_7110197 := by
    simpa [prefixWord, tailWord_7110197, baseEnd_7110197] using wordTrace_append hprefix tailTrace_7110197
  have hstable : (prefixWord ++ tailWord_7110197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110197).length < 2 ^ (prefixWord ++ tailWord_7110197).sum := by decide
  have hdescent : baseEnd_7110197 < baseStart_7110197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110207 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 2, 6]
def baseStart_7110207 : Nat := 118140960795 + 7110207 * 2 ^ 59
def prefixEnd_7110207 : Nat := 4983230072969 + 3 ^ 40 * 7110207 * 2
def baseEnd_7110207 : Nat := 1216984581320922672037753

theorem tailTrace_7110207 : CollatzResearch.WordTrace tailWord_7110207 prefixEnd_7110207 1216984581320922672037753 := by
  unfold tailWord_7110207
  simp only [CollatzResearch.WordTrace]
  refine ⟨259330554151941840523224875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172887036101294560348816583 259330554151941840523224875)
  ·
    refine ⟨388995831227912760784837313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259330554151941840523224875 388995831227912760784837313)
    ·
      refine ⟨291746873420934570588627985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388995831227912760784837313 291746873420934570588627985)
      ·
        refine ⟨218810155065700927941470989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291746873420934570588627985 218810155065700927941470989)
        ·
          refine ⟨82053808149637847978051621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218810155065700927941470989 82053808149637847978051621)
          ·
            refine ⟨15385089028057096495884679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82053808149637847978051621 15385089028057096495884679)
            ·
              refine ⟨23077633542085644743827019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15385089028057096495884679 23077633542085644743827019)
              ·
                refine ⟨34616450313128467115740529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23077633542085644743827019 34616450313128467115740529)
                ·
                  refine ⟨25962337734846350336805397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34616450313128467115740529 25962337734846350336805397)
                  ·
                    refine ⟨1216984581320922672037753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25962337734846350336805397 1216984581320922672037753)
                    ·
                      rfl

theorem cell23_7110207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_7110207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110207 prefixEnd_7110207 := by exact prefixLift 7110207
  have htrace : WordTrace (prefixWord ++ tailWord_7110207) baseStart_7110207 baseEnd_7110207 := by
    simpa [prefixWord, tailWord_7110207, baseEnd_7110207] using wordTrace_append hprefix tailTrace_7110207
  have hstable : (prefixWord ++ tailWord_7110207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110207).length < 2 ^ (prefixWord ++ tailWord_7110207).sum := by decide
  have hdescent : baseEnd_7110207 < baseStart_7110207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110248 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_7110248 : Nat := 118140960795 + 7110248 * 2 ^ 59
def prefixEnd_7110248 : Nat := 4983230072969 + 3 ^ 40 * 7110248 * 2
def baseEnd_7110248 : Nat := 3650974796669602355700571

theorem tailTrace_7110248 : CollatzResearch.WordTrace tailWord_7110248 prefixEnd_7110248 3650974796669602355700571 := by
  unfold tailWord_7110248
  simp only [CollatzResearch.WordTrace]
  refine ⟨129666024772396652262733699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172888033029862203016978265 129666024772396652262733699)
  ·
    refine ⟨194499037158594978394100549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129666024772396652262733699 194499037158594978394100549)
    ·
      refine ⟨36468569467236558448893853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194499037158594978394100549 36468569467236558448893853)
      ·
        refine ⟨13675713550213709418335195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36468569467236558448893853 13675713550213709418335195)
        ·
          refine ⟨20513570325320564127502793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13675713550213709418335195 20513570325320564127502793)
          ·
            refine ⟨15385177743990423095627095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20513570325320564127502793 15385177743990423095627095)
            ·
              refine ⟨23077766615985634643440643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15385177743990423095627095 23077766615985634643440643)
              ·
                refine ⟨34616649923978451965160965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23077766615985634643440643 34616649923978451965160965)
                ·
                  refine ⟨6490621860745959743467681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34616649923978451965160965 6490621860745959743467681)
                  ·
                    refine ⟨4867966395559469807600761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6490621860745959743467681 4867966395559469807600761)
                    ·
                      refine ⟨3650974796669602355700571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867966395559469807600761 3650974796669602355700571)
                      ·
                        rfl

theorem cell23_7110248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_7110248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110248 prefixEnd_7110248 := by exact prefixLift 7110248
  have htrace : WordTrace (prefixWord ++ tailWord_7110248) baseStart_7110248 baseEnd_7110248 := by
    simpa [prefixWord, tailWord_7110248, baseEnd_7110248] using wordTrace_append hprefix tailTrace_7110248
  have hstable : (prefixWord ++ tailWord_7110248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110248).length < 2 ^ (prefixWord ++ tailWord_7110248).sum := by decide
  have hdescent : baseEnd_7110248 < baseStart_7110248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110304 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 4]
def baseStart_7110304 : Nat := 118140960795 + 7110304 * 2 ^ 59
def prefixEnd_7110304 : Nat := 4983230072969 + 3 ^ 40 * 7110304 * 2
def baseEnd_7110304 : Nat := 3651003551586254136600313

theorem tailTrace_7110304 : CollatzResearch.WordTrace tailWord_7110304 prefixEnd_7110304 3651003551586254136600313 := by
  unfold tailWord_7110304
  simp only [CollatzResearch.WordTrace]
  refine ⟨129667046016295213044752983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172889394688393617393003977 129667046016295213044752983)
  ·
    refine ⟨194500569024442819567129475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129667046016295213044752983 194500569024442819567129475)
    ·
      refine ⟨291750853536664229350694213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194500569024442819567129475 291750853536664229350694213)
      ·
        refine ⟨54703285038124543003255165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291750853536664229350694213 54703285038124543003255165)
        ·
          refine ⟨20513731889296703626220687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54703285038124543003255165 20513731889296703626220687)
          ·
            refine ⟨30770597833945055439331031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20513731889296703626220687 30770597833945055439331031)
            ·
              refine ⟨46155896750917583158996547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30770597833945055439331031 46155896750917583158996547)
              ·
                refine ⟨69233845126376374738494821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46155896750917583158996547 69233845126376374738494821)
                ·
                  refine ⟨12981345961195570263467779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69233845126376374738494821 12981345961195570263467779)
                  ·
                    refine ⟨19472018941793355395201669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12981345961195570263467779 19472018941793355395201669)
                    ·
                      refine ⟨3651003551586254136600313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19472018941793355395201669 3651003551586254136600313)
                      ·
                        rfl

theorem cell23_7110304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_7110304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110304 prefixEnd_7110304 := by exact prefixLift 7110304
  have htrace : WordTrace (prefixWord ++ tailWord_7110304) baseStart_7110304 baseEnd_7110304 := by
    simpa [prefixWord, tailWord_7110304, baseEnd_7110304] using wordTrace_append hprefix tailTrace_7110304
  have hstable : (prefixWord ++ tailWord_7110304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110304).length < 2 ^ (prefixWord ++ tailWord_7110304).sum := by decide
  have hdescent : baseEnd_7110304 < baseStart_7110304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110421 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 4, 4]
def baseStart_7110421 : Nat := 118140960795 + 7110421 * 2 ^ 59
def prefixEnd_7110421 : Nat := 4983230072969 + 3 ^ 40 * 7110421 * 2
def baseEnd_7110421 : Nat := 1217021209607610059612425

theorem tailTrace_7110421 : CollatzResearch.WordTrace tailWord_7110421 prefixEnd_7110421 1217021209607610059612425 := by
  unfold tailWord_7110421
  simp only [CollatzResearch.WordTrace]
  refine ⟨259338359373166555071515117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172892239582111036714343411 259338359373166555071515117)
  ·
    refine ⟨97251884764937458151818169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259338359373166555071515117 97251884764937458151818169)
    ·
      refine ⟨72938913573703093613863627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97251884764937458151818169 72938913573703093613863627)
      ·
        refine ⟨109408370360554640420795441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72938913573703093613863627 109408370360554640420795441)
        ·
          refine ⟨82056277770415980315596581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109408370360554640420795441 82056277770415980315596581)
          ·
            refine ⟨15385552081952996309174359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82056277770415980315596581 15385552081952996309174359)
            ·
              refine ⟨23078328122929494463761539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15385552081952996309174359 23078328122929494463761539)
              ·
                refine ⟨34617492184394241695642309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23078328122929494463761539 34617492184394241695642309)
                ·
                  refine ⟨6490779784573920317932933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34617492184394241695642309 6490779784573920317932933)
                  ·
                    refine ⟨1217021209607610059612425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490779784573920317932933 1217021209607610059612425)
                    ·
                      rfl

theorem cell23_7110421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_7110421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110421 prefixEnd_7110421 := by exact prefixLift 7110421
  have htrace : WordTrace (prefixWord ++ tailWord_7110421) baseStart_7110421 baseEnd_7110421 := by
    simpa [prefixWord, tailWord_7110421, baseEnd_7110421] using wordTrace_append hprefix tailTrace_7110421
  have hstable : (prefixWord ++ tailWord_7110421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110421).length < 2 ^ (prefixWord ++ tailWord_7110421).sum := by decide
  have hdescent : baseEnd_7110421 < baseStart_7110421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110424 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_7110424 : Nat := 118140960795 + 7110424 * 2 ^ 59
def prefixEnd_7110424 : Nat := 4983230072969 + 3 ^ 40 * 7110424 * 2
def baseEnd_7110424 : Nat := 3651065169264793667099761

theorem tailTrace_7110424 : CollatzResearch.WordTrace tailWord_7110424 prefixEnd_7110424 3651065169264793667099761 := by
  unfold tailWord_7110424
  simp only [CollatzResearch.WordTrace]
  refine ⟨129669234396077843291937163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172892312528103791055916217 129669234396077843291937163)
  ·
    refine ⟨194503851594116764937905745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129669234396077843291937163 194503851594116764937905745)
    ·
      refine ⟨145877888695587573703429309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194503851594116764937905745 145877888695587573703429309)
      ·
        refine ⟨54704208260845340138785991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145877888695587573703429309 54704208260845340138785991)
        ·
          refine ⟨82056312391268010208178987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54704208260845340138785991 82056312391268010208178987)
          ·
            refine ⟨123084468586902015312268481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82056312391268010208178987 123084468586902015312268481)
            ·
              refine ⟨92313351440176511484201361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123084468586902015312268481 92313351440176511484201361)
              ·
                refine ⟨69235013580132383613151021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92313351440176511484201361 69235013580132383613151021)
                ·
                  refine ⟨25963130092549643854931633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69235013580132383613151021 25963130092549643854931633)
                  ·
                    refine ⟨19472347569412232891198725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25963130092549643854931633 19472347569412232891198725)
                    ·
                      refine ⟨3651065169264793667099761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19472347569412232891198725 3651065169264793667099761)
                      ·
                        rfl

theorem cell23_7110424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_7110424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110424 prefixEnd_7110424 := by exact prefixLift 7110424
  have htrace : WordTrace (prefixWord ++ tailWord_7110424) baseStart_7110424 baseEnd_7110424 := by
    simpa [prefixWord, tailWord_7110424, baseEnd_7110424] using wordTrace_append hprefix tailTrace_7110424
  have hstable : (prefixWord ++ tailWord_7110424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110424).length < 2 ^ (prefixWord ++ tailWord_7110424).sum := by decide
  have hdescent : baseEnd_7110424 < baseStart_7110424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110434 : List Nat := [3, 3, 1, 1, 2, 1, 2, 10]
def baseStart_7110434 : Nat := 118140960795 + 7110434 * 2 ^ 59
def prefixEnd_7110434 : Nat := 4983230072969 + 3 ^ 40 * 7110434 * 2
def baseEnd_7110434 : Nat := 135224826076716245480545

theorem tailTrace_7110434 : CollatzResearch.WordTrace tailWord_7110434 prefixEnd_7110434 135224826076716245480545 := by
  unfold tailWord_7110434
  simp only [CollatzResearch.WordTrace]
  refine ⟨64834708380529864572934589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172892555681412972194492237 64834708380529864572934589)
  ·
    refine ⟨24313015642698699214850471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64834708380529864572934589 24313015642698699214850471)
    ·
      refine ⟨36469523464048048822275707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24313015642698699214850471 36469523464048048822275707)
      ·
        refine ⟨54704285196072073233413561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36469523464048048822275707 54704285196072073233413561)
        ·
          refine ⟨41028213897054054925060171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54704285196072073233413561 41028213897054054925060171)
          ·
            refine ⟨61542320845581082387590257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41028213897054054925060171 61542320845581082387590257)
            ·
              refine ⟨46156740634185811790692693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61542320845581082387590257 46156740634185811790692693)
              ·
                refine ⟨135224826076716245480545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46156740634185811790692693 135224826076716245480545)
                ·
                  rfl

theorem cell23_7110434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 10].length) (baseStart_7110434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110434 prefixEnd_7110434 := by exact prefixLift 7110434
  have htrace : WordTrace (prefixWord ++ tailWord_7110434) baseStart_7110434 baseEnd_7110434 := by
    simpa [prefixWord, tailWord_7110434, baseEnd_7110434] using wordTrace_append hprefix tailTrace_7110434
  have hstable : (prefixWord ++ tailWord_7110434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110434).length < 2 ^ (prefixWord ++ tailWord_7110434).sum := by decide
  have hdescent : baseEnd_7110434 < baseStart_7110434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110474 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_7110474 : Nat := 118140960795 + 7110474 * 2 ^ 59
def prefixEnd_7110474 : Nat := 4983230072969 + 3 ^ 40 * 7110474 * 2
def baseEnd_7110474 : Nat := 3651090843297518471474531

theorem tailTrace_7110474 : CollatzResearch.WordTrace tailWord_7110474 prefixEnd_7110474 3651090843297518471474531 := by
  unfold tailWord_7110474
  simp only [CollatzResearch.WordTrace]
  refine ⟨64835073110493636280798619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172893528294649696748796317 64835073110493636280798619)
  ·
    refine ⟨97252609665740454421197929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64835073110493636280798619 97252609665740454421197929)
    ·
      refine ⟨72939457249305340815898447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97252609665740454421197929 72939457249305340815898447)
      ·
        refine ⟨109409185873958011223847671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72939457249305340815898447 109409185873958011223847671)
        ·
          refine ⟨164113778810937016835771507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109409185873958011223847671 164113778810937016835771507)
          ·
            refine ⟨246170668216405525253657261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164113778810937016835771507 246170668216405525253657261)
            ·
              refine ⟨92314000581152071970121473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246170668216405525253657261 92314000581152071970121473)
              ·
                refine ⟨69235500435864053977591105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92314000581152071970121473 69235500435864053977591105)
                ·
                  refine ⟨51926625326898040483193329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69235500435864053977591105 51926625326898040483193329)
                  ·
                    refine ⟨38944968995173530362394997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51926625326898040483193329 38944968995173530362394997)
                    ·
                      refine ⟨3651090843297518471474531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38944968995173530362394997 3651090843297518471474531)
                      ·
                        rfl

theorem cell23_7110474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_7110474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110474 prefixEnd_7110474 := by exact prefixLift 7110474
  have htrace : WordTrace (prefixWord ++ tailWord_7110474) baseStart_7110474 baseEnd_7110474 := by
    simpa [prefixWord, tailWord_7110474, baseEnd_7110474] using wordTrace_append hprefix tailTrace_7110474
  have hstable : (prefixWord ++ tailWord_7110474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110474).length < 2 ^ (prefixWord ++ tailWord_7110474).sum := by decide
  have hdescent : baseEnd_7110474 < baseStart_7110474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110495 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 2, 1, 3]
def baseStart_7110495 : Nat := 118140960795 + 7110495 * 2 ^ 59
def prefixEnd_7110495 : Nat := 4983230072969 + 3 ^ 40 * 7110495 * 2
def baseEnd_7110495 : Nat := 3651101626391262889311935

theorem tailTrace_7110495 : CollatzResearch.WordTrace tailWord_7110495 prefixEnd_7110495 3651101626391262889311935 := by
  unfold tailWord_7110495
  simp only [CollatzResearch.WordTrace]
  refine ⟨259341058374898465709708939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172894038916598977139805959 259341058374898465709708939)
  ·
    refine ⟨389011587562347698564563409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259341058374898465709708939 389011587562347698564563409)
    ·
      refine ⟨291758690671760773923422557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389011587562347698564563409 291758690671760773923422557)
      ·
        refine ⟨109409509001910290221283459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291758690671760773923422557 109409509001910290221283459)
        ·
          refine ⟨164114263502865435331925189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109409509001910290221283459 164114263502865435331925189)
          ·
            refine ⟨30771424406787269124735973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164114263502865435331925189 30771424406787269124735973)
            ·
              refine ⟨5769642076272612960887995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30771424406787269124735973 5769642076272612960887995)
              ·
                refine ⟨8654463114408919441331993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5769642076272612960887995 8654463114408919441331993)
                ·
                  refine ⟨6490847335806689580998995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8654463114408919441331993 6490847335806689580998995)
                  ·
                    refine ⟨9736271003710034371498493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6490847335806689580998995 9736271003710034371498493)
                    ·
                      refine ⟨3651101626391262889311935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9736271003710034371498493 3651101626391262889311935)
                      ·
                        rfl

theorem cell23_7110495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_7110495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110495 prefixEnd_7110495 := by exact prefixLift 7110495
  have htrace : WordTrace (prefixWord ++ tailWord_7110495) baseStart_7110495 baseEnd_7110495 := by
    simpa [prefixWord, tailWord_7110495, baseEnd_7110495] using wordTrace_append hprefix tailTrace_7110495
  have hstable : (prefixWord ++ tailWord_7110495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110495).length < 2 ^ (prefixWord ++ tailWord_7110495).sum := by decide
  have hdescent : baseEnd_7110495 < baseStart_7110495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110548 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_7110548 : Nat := 118140960795 + 7110548 * 2 ^ 59
def prefixEnd_7110548 : Nat := 4983230072969 + 3 ^ 40 * 7110548 * 2
def baseEnd_7110548 : Nat := 3651128840865951181949191

theorem tailTrace_7110548 : CollatzResearch.WordTrace tailWord_7110548 prefixEnd_7110548 3651128840865951181949191 := by
  unfold tailWord_7110548
  simp only [CollatzResearch.WordTrace]
  refine ⟨129671495721853227880694149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172895327629137637174258865 129671495721853227880694149)
  ·
    refine ⟨24313405447847480227630153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129671495721853227880694149 24313405447847480227630153)
    ·
      refine ⟨18235054085885610170722615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24313405447847480227630153 18235054085885610170722615)
      ·
        refine ⟨27352581128828415256083923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18235054085885610170722615 27352581128828415256083923)
        ·
          refine ⟨41028871693242622884125885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27352581128828415256083923 41028871693242622884125885)
          ·
            refine ⟨15385826884965983581547207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41028871693242622884125885 15385826884965983581547207)
            ·
              refine ⟨23078740327448975372320811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15385826884965983581547207 23078740327448975372320811)
              ·
                refine ⟨34618110491173463058481217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23078740327448975372320811 34618110491173463058481217)
                ·
                  refine ⟨25963582868380097293860913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34618110491173463058481217 25963582868380097293860913)
                  ·
                    refine ⟨19472687151285072970395685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25963582868380097293860913 19472687151285072970395685)
                    ·
                      refine ⟨3651128840865951181949191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19472687151285072970395685 3651128840865951181949191)
                      ·
                        rfl

theorem cell23_7110548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_7110548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110548 prefixEnd_7110548 := by exact prefixLift 7110548
  have htrace : WordTrace (prefixWord ++ tailWord_7110548) baseStart_7110548 baseEnd_7110548 := by
    simpa [prefixWord, tailWord_7110548, baseEnd_7110548] using wordTrace_append hprefix tailTrace_7110548
  have hstable : (prefixWord ++ tailWord_7110548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110548).length < 2 ^ (prefixWord ++ tailWord_7110548).sum := by decide
  have hdescent : baseEnd_7110548 < baseStart_7110548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110551 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 3]
def baseStart_7110551 : Nat := 118140960795 + 7110551 * 2 ^ 59
def prefixEnd_7110551 : Nat := 4983230072969 + 3 ^ 40 * 7110551 * 2
def baseEnd_7110551 : Nat := 3651130381307914670211677

theorem tailTrace_7110551 : CollatzResearch.WordTrace tailWord_7110551 prefixEnd_7110551 3651130381307914670211677 := by
  unfold tailWord_7110551
  simp only [CollatzResearch.WordTrace]
  refine ⟨259343100862695587273747507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172895400575130391515831671 259343100862695587273747507)
  ·
    refine ⟨389014651294043380910621261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259343100862695587273747507 389014651294043380910621261)
    ·
      refine ⟨145880494235266267841482973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389014651294043380910621261 145880494235266267841482973)
      ·
        refine ⟨54705185338224850440556115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145880494235266267841482973 54705185338224850440556115)
        ·
          refine ⟨82057778007337275660834173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54705185338224850440556115 82057778007337275660834173)
          ·
            refine ⟨30771666752751478372812815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82057778007337275660834173 30771666752751478372812815)
            ·
              refine ⟨46157500129127217559219223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30771666752751478372812815 46157500129127217559219223)
              ·
                refine ⟨69236250193690826338828835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46157500129127217559219223 69236250193690826338828835)
                ·
                  refine ⟨103854375290536239508243253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69236250193690826338828835 103854375290536239508243253)
                  ·
                    refine ⟨9736347683487772453897805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103854375290536239508243253 9736347683487772453897805)
                    ·
                      refine ⟨3651130381307914670211677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9736347683487772453897805 3651130381307914670211677)
                      ·
                        rfl

theorem cell23_7110551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_7110551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110551 prefixEnd_7110551 := by exact prefixLift 7110551
  have htrace : WordTrace (prefixWord ++ tailWord_7110551) baseStart_7110551 baseEnd_7110551 := by
    simpa [prefixWord, tailWord_7110551, baseEnd_7110551] using wordTrace_append hprefix tailTrace_7110551
  have hstable : (prefixWord ++ tailWord_7110551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110551).length < 2 ^ (prefixWord ++ tailWord_7110551).sum := by decide
  have hdescent : baseEnd_7110551 < baseStart_7110551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110552 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7110552 : Nat := 118140960795 + 7110552 * 2 ^ 59
def prefixEnd_7110552 : Nat := 4983230072969 + 3 ^ 40 * 7110552 * 2
def baseEnd_7110552 : Nat := 3651130894788569166299173

theorem tailTrace_7110552 : CollatzResearch.WordTrace tailWord_7110552 prefixEnd_7110552 3651130894788569166299173 := by
  unfold tailWord_7110552
  simp only [CollatzResearch.WordTrace]
  refine ⟨129671568667845982222266955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172895424890461309629689273 129671568667845982222266955)
  ·
    refine ⟨194507353001768973333400433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129671568667845982222266955 194507353001768973333400433)
    ·
      refine ⟨145880514751326730000050325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194507353001768973333400433 145880514751326730000050325)
      ·
        refine ⟨6838149128968440468752359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 145880514751326730000050325 6838149128968440468752359)
        ·
          refine ⟨10257223693452660703128539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6838149128968440468752359 10257223693452660703128539)
          ·
            refine ⟨15385835540178991054692809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10257223693452660703128539 15385835540178991054692809)
            ·
              refine ⟨11539376655134243291019607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15385835540178991054692809 11539376655134243291019607)
              ·
                refine ⟨17309064982701364936529411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11539376655134243291019607 17309064982701364936529411)
                ·
                  refine ⟨25963597474052047404794117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17309064982701364936529411 25963597474052047404794117)
                  ·
                    refine ⟨4868174526384758888398897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25963597474052047404794117 4868174526384758888398897)
                    ·
                      refine ⟨3651130894788569166299173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4868174526384758888398897 3651130894788569166299173)
                      ·
                        rfl

theorem cell23_7110552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7110552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110552 prefixEnd_7110552 := by exact prefixLift 7110552
  have htrace : WordTrace (prefixWord ++ tailWord_7110552) baseStart_7110552 baseEnd_7110552 := by
    simpa [prefixWord, tailWord_7110552, baseEnd_7110552] using wordTrace_append hprefix tailTrace_7110552
  have hstable : (prefixWord ++ tailWord_7110552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110552).length < 2 ^ (prefixWord ++ tailWord_7110552).sum := by decide
  have hdescent : baseEnd_7110552 < baseStart_7110552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110591 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 4]
def baseStart_7110591 : Nat := 118140960795 + 7110591 * 2 ^ 59
def prefixEnd_7110591 : Nat := 4983230072969 + 3 ^ 40 * 7110591 * 2
def baseEnd_7110591 : Nat := 3651150920534094513711493

theorem tailTrace_7110591 : CollatzResearch.WordTrace tailWord_7110591 prefixEnd_7110591 3651150920534094513711493 := by
  unfold tailWord_7110591
  simp only [CollatzResearch.WordTrace]
  refine ⟨259344559782550674105203627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172896373188367116070135751 259344559782550674105203627)
  ·
    refine ⟨389016839673826011157805441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259344559782550674105203627 389016839673826011157805441)
    ·
      refine ⟨291762629755369508368354081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389016839673826011157805441 291762629755369508368354081)
      ·
        refine ⟨218821972316527131276265561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291762629755369508368354081 218821972316527131276265561)
        ·
          refine ⟨164116479237395348457199171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218821972316527131276265561 164116479237395348457199171)
          ·
            refine ⟨246174718856093022685798757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164116479237395348457199171 246174718856093022685798757)
            ·
              refine ⟨46157759785517441753587267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246174718856093022685798757 46157759785517441753587267)
              ·
                refine ⟨69236639678276162630380901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46157759785517441753587267 69236639678276162630380901)
                ·
                  refine ⟨12981869939676780493196419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69236639678276162630380901 12981869939676780493196419)
                  ·
                    refine ⟨19472804909515170739794629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12981869939676780493196419 19472804909515170739794629)
                    ·
                      refine ⟨3651150920534094513711493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19472804909515170739794629 3651150920534094513711493)
                      ·
                        rfl

theorem cell23_7110591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_7110591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110591 prefixEnd_7110591 := by exact prefixLift 7110591
  have htrace : WordTrace (prefixWord ++ tailWord_7110591) baseStart_7110591 baseEnd_7110591 := by
    simpa [prefixWord, tailWord_7110591, baseEnd_7110591] using wordTrace_append hprefix tailTrace_7110591
  have hstable : (prefixWord ++ tailWord_7110591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110591).length < 2 ^ (prefixWord ++ tailWord_7110591).sum := by decide
  have hdescent : baseEnd_7110591 < baseStart_7110591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110601 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 7, 4]
def baseStart_7110601 : Nat := 118140960795 + 7110601 * 2 ^ 59
def prefixEnd_7110601 : Nat := 4983230072969 + 3 ^ 40 * 7110601 * 2
def baseEnd_7110601 : Nat := 1217052018446879824862149

theorem tailTrace_7110601 : CollatzResearch.WordTrace tailWord_7110601 prefixEnd_7110601 1217052018446879824862149 := by
  unfold tailWord_7110601
  simp only [CollatzResearch.WordTrace]
  refine ⟨259344924512514445813067657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172896616341676297208711771 259344924512514445813067657)
  ·
    refine ⟨194508693384385834359800743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259344924512514445813067657 194508693384385834359800743)
    ·
      refine ⟨291763040076578751539701115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194508693384385834359800743 291763040076578751539701115)
      ·
        refine ⟨437644560114868127309551673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291763040076578751539701115 437644560114868127309551673)
        ·
          refine ⟨328233420086151095482163755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437644560114868127309551673 328233420086151095482163755)
          ·
            refine ⟨492350130129226643223245633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328233420086151095482163755 492350130129226643223245633)
            ·
              refine ⟨369262597596919982417434225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492350130129226643223245633 369262597596919982417434225)
              ·
                refine ⟨276946948197689986813075669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369262597596919982417434225 276946948197689986813075669)
                ·
                  refine ⟨6490944098383359065931461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 276946948197689986813075669 6490944098383359065931461)
                  ·
                    refine ⟨1217052018446879824862149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490944098383359065931461 1217052018446879824862149)
                    ·
                      rfl

theorem cell23_7110601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 4].length) (baseStart_7110601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110601 prefixEnd_7110601 := by exact prefixLift 7110601
  have htrace : WordTrace (prefixWord ++ tailWord_7110601) baseStart_7110601 baseEnd_7110601 := by
    simpa [prefixWord, tailWord_7110601, baseEnd_7110601] using wordTrace_append hprefix tailTrace_7110601
  have hstable : (prefixWord ++ tailWord_7110601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110601).length < 2 ^ (prefixWord ++ tailWord_7110601).sum := by decide
  have hdescent : baseEnd_7110601 < baseStart_7110601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110608 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 2, 4, 2]
def baseStart_7110608 : Nat := 118140960795 + 7110608 * 2 ^ 59
def prefixEnd_7110608 : Nat := 4983230072969 + 3 ^ 40 * 7110608 * 2
def baseEnd_7110608 : Nat := 3651159649705220947198915

theorem tailTrace_7110608 : CollatzResearch.WordTrace tailWord_7110608 prefixEnd_7110608 3651159649705220947198915 := by
  unfold tailWord_7110608
  simp only [CollatzResearch.WordTrace]
  refine ⟨129672589911744543004286239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172896786548992724005714985 129672589911744543004286239)
  ·
    refine ⟨194508884867616814506429359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129672589911744543004286239 194508884867616814506429359)
    ·
      refine ⟨291763327301425221759644039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194508884867616814506429359 291763327301425221759644039)
      ·
        refine ⟨437644990952137832639466059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291763327301425221759644039 437644990952137832639466059)
        ·
          refine ⟨656467486428206748959199089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437644990952137832639466059 656467486428206748959199089)
          ·
            refine ⟨492350614821155061719399317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656467486428206748959199089 492350614821155061719399317)
            ·
              refine ⟨23078935069741643518096843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 492350614821155061719399317 23078935069741643518096843)
              ·
                refine ⟨34618402604612465277145265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23078935069741643518096843 34618402604612465277145265)
                ·
                  refine ⟨25963801953459348957858949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34618402604612465277145265 25963801953459348957858949)
                  ·
                    refine ⟨4868212866273627929598553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25963801953459348957858949 4868212866273627929598553)
                    ·
                      refine ⟨3651159649705220947198915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4868212866273627929598553 3651159649705220947198915)
                      ·
                        rfl

theorem cell23_7110608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 2, 4, 2].length) (baseStart_7110608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110608 prefixEnd_7110608 := by exact prefixLift 7110608
  have htrace : WordTrace (prefixWord ++ tailWord_7110608) baseStart_7110608 baseEnd_7110608 := by
    simpa [prefixWord, tailWord_7110608, baseEnd_7110608] using wordTrace_append hprefix tailTrace_7110608
  have hstable : (prefixWord ++ tailWord_7110608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110608).length < 2 ^ (prefixWord ++ tailWord_7110608).sum := by decide
  have hdescent : baseEnd_7110608 < baseStart_7110608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110628 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_7110628 : Nat := 118140960795 + 7110628 * 2 ^ 59
def prefixEnd_7110628 : Nat := 4983230072969 + 3 ^ 40 * 7110628 * 2
def baseEnd_7110628 : Nat := 3651169919318310868948823

theorem tailTrace_7110628 : CollatzResearch.WordTrace tailWord_7110628 prefixEnd_7110628 3651169919318310868948823 := by
  unfold tailWord_7110628
  simp only [CollatzResearch.WordTrace]
  refine ⟨129672954641708314712150269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172897272855611086282867025 129672954641708314712150269)
  ·
    refine ⟨48627357990640618017056351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129672954641708314712150269 48627357990640618017056351)
    ·
      refine ⟨72941036985960927025584527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48627357990640618017056351 72941036985960927025584527)
      ·
        refine ⟨109411555478941390538376791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72941036985960927025584527 109411555478941390538376791)
        ·
          refine ⟨164117333218412085807565187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109411555478941390538376791 164117333218412085807565187)
          ·
            refine ⟨246175999827618128711347781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164117333218412085807565187 246175999827618128711347781)
            ·
              refine ⟨46157999967678399133377709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246175999827618128711347781 46157999967678399133377709)
              ·
                refine ⟨17309249987879399675016641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46157999967678399133377709 17309249987879399675016641)
                ·
                  refine ⟨12981937490909549756262481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17309249987879399675016641 12981937490909549756262481)
                  ·
                    refine ⟨9736453118182162317196861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12981937490909549756262481 9736453118182162317196861)
                    ·
                      refine ⟨3651169919318310868948823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9736453118182162317196861 3651169919318310868948823)
                      ·
                        rfl

theorem cell23_7110628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_7110628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110628 prefixEnd_7110628 := by exact prefixLift 7110628
  have htrace : WordTrace (prefixWord ++ tailWord_7110628) baseStart_7110628 baseEnd_7110628 := by
    simpa [prefixWord, tailWord_7110628, baseEnd_7110628] using wordTrace_append hprefix tailTrace_7110628
  have hstable : (prefixWord ++ tailWord_7110628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110628).length < 2 ^ (prefixWord ++ tailWord_7110628).sum := by decide
  have hdescent : baseEnd_7110628 < baseStart_7110628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110652 : List Nat := [2, 2, 2, 1, 2, 2, 5, 2, 1, 4]
def baseStart_7110652 : Nat := 118140960795 + 7110652 * 2 ^ 59
def prefixEnd_7110652 : Nat := 4983230072969 + 3 ^ 40 * 7110652 * 2
def baseEnd_7110652 : Nat := 1217060747618006258349571

theorem tailTrace_7110652 : CollatzResearch.WordTrace tailWord_7110652 prefixEnd_7110652 1217060747618006258349571 := by
  unfold tailWord_7110652
  simp only [CollatzResearch.WordTrace]
  refine ⟨129673392317664840761587105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172897856423553121015449473 129673392317664840761587105)
  ·
    refine ⟨97255044238248630571190329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129673392317664840761587105 97255044238248630571190329)
    ·
      refine ⟨72941283178686472928392747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97255044238248630571190329 72941283178686472928392747)
      ·
        refine ⟨109411924768029709392589121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72941283178686472928392747 109411924768029709392589121)
        ·
          refine ⟨82058943576022282044441841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109411924768029709392589121 82058943576022282044441841)
          ·
            refine ⟨61544207682016711533331381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82058943576022282044441841 61544207682016711533331381)
            ·
              refine ⟨5769769470189066706249817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61544207682016711533331381 5769769470189066706249817)
              ·
                refine ⟨4327327102641800029687363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5769769470189066706249817 4327327102641800029687363)
                ·
                  refine ⟨6490990653962700044531045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327327102641800029687363 6490990653962700044531045)
                  ·
                    refine ⟨1217060747618006258349571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490990653962700044531045 1217060747618006258349571)
                    ·
                      rfl

theorem cell23_7110652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_7110652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110652 prefixEnd_7110652 := by exact prefixLift 7110652
  have htrace : WordTrace (prefixWord ++ tailWord_7110652) baseStart_7110652 baseEnd_7110652 := by
    simpa [prefixWord, tailWord_7110652, baseEnd_7110652] using wordTrace_append hprefix tailTrace_7110652
  have hstable : (prefixWord ++ tailWord_7110652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110652).length < 2 ^ (prefixWord ++ tailWord_7110652).sum := by decide
  have hdescent : baseEnd_7110652 < baseStart_7110652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110702 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_7110702 : Nat := 118140960795 + 7110702 * 2 ^ 59
def prefixEnd_7110702 : Nat := 4983230072969 + 3 ^ 40 * 7110702 * 2
def baseEnd_7110702 : Nat := 3651207916886743579423483

theorem tailTrace_7110702 : CollatzResearch.WordTrace tailWord_7110702 prefixEnd_7110702 3651207916886743579423483 := by
  unfold tailWord_7110702
  simp only [CollatzResearch.WordTrace]
  refine ⟨32418576035643567507811795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172899072190099026708329573 32418576035643567507811795)
  ·
    refine ⟨48627864053465351261717693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32418576035643567507811795 48627864053465351261717693)
    ·
      refine ⟨18235449020049506723144135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48627864053465351261717693 18235449020049506723144135)
      ·
        refine ⟨27353173530074260084716203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18235449020049506723144135 27353173530074260084716203)
        ·
          refine ⟨41029760295111390127074305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27353173530074260084716203 41029760295111390127074305)
          ·
            refine ⟨30772320221333542595305729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41029760295111390127074305 30772320221333542595305729)
            ·
              refine ⟨23079240166000156946479297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30772320221333542595305729 23079240166000156946479297)
              ·
                refine ⟨17309430124500117709859473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23079240166000156946479297 17309430124500117709859473)
                ·
                  refine ⟨12982072593375088282394605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17309430124500117709859473 12982072593375088282394605)
                  ·
                    refine ⟨4868277222515658105897977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12982072593375088282394605 4868277222515658105897977)
                    ·
                      refine ⟨3651207916886743579423483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4868277222515658105897977 3651207916886743579423483)
                      ·
                        rfl

theorem cell23_7110702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_7110702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110702 prefixEnd_7110702 := by exact prefixLift 7110702
  have htrace : WordTrace (prefixWord ++ tailWord_7110702) baseStart_7110702 baseEnd_7110702 := by
    simpa [prefixWord, tailWord_7110702, baseEnd_7110702] using wordTrace_append hprefix tailTrace_7110702
  have hstable : (prefixWord ++ tailWord_7110702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110702).length < 2 ^ (prefixWord ++ tailWord_7110702).sum := by decide
  have hdescent : baseEnd_7110702 < baseStart_7110702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110709 : List Nat := [1, 3, 3, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_7110709 : Nat := 118140960795 + 7110709 * 2 ^ 59
def prefixEnd_7110709 : Nat := 4983230072969 + 3 ^ 40 * 7110709 * 2
def baseEnd_7110709 : Nat := 3651211511251325052035951

theorem tailTrace_7110709 : CollatzResearch.WordTrace tailWord_7110709 prefixEnd_7110709 3651211511251325052035951 := by
  unfold tailWord_7110709
  simp only [CollatzResearch.WordTrace]
  refine ⟨259348863596123180257999181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172899242397415453505332787 259348863596123180257999181)
  ·
    refine ⟨97255823848546192596749693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259348863596123180257999181 97255823848546192596749693)
    ·
      refine ⟨36470933943204822223781135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97255823848546192596749693 36470933943204822223781135)
      ·
        refine ⟨54706400914807233335671703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36470933943204822223781135 54706400914807233335671703)
        ·
          refine ⟨82059601372210850003507555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54706400914807233335671703 82059601372210850003507555)
          ·
            refine ⟨123089402058316275005261333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82059601372210850003507555 123089402058316275005261333)
            ·
              refine ⟨5769815721483575390871625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123089402058316275005261333 5769815721483575390871625)
              ·
                refine ⟨4327361791112681543153719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5769815721483575390871625 4327361791112681543153719)
                ·
                  refine ⟨6491042686669022314730579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327361791112681543153719 6491042686669022314730579)
                  ·
                    refine ⟨9736564030003533472095869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6491042686669022314730579 9736564030003533472095869)
                    ·
                      refine ⟨3651211511251325052035951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9736564030003533472095869 3651211511251325052035951)
                      ·
                        rfl

theorem cell23_7110709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_7110709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110709 prefixEnd_7110709 := by exact prefixLift 7110709
  have htrace : WordTrace (prefixWord ++ tailWord_7110709) baseStart_7110709 baseEnd_7110709 := by
    simpa [prefixWord, tailWord_7110709, baseEnd_7110709] using wordTrace_append hprefix tailTrace_7110709
  have hstable : (prefixWord ++ tailWord_7110709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110709).length < 2 ^ (prefixWord ++ tailWord_7110709).sum := by decide
  have hdescent : baseEnd_7110709 < baseStart_7110709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110711 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_7110711 : Nat := 118140960795 + 7110711 * 2 ^ 59
def prefixEnd_7110711 : Nat := 4983230072969 + 3 ^ 40 * 7110711 * 2
def baseEnd_7110711 : Nat := 3651212538212634044210941

theorem tailTrace_7110711 : CollatzResearch.WordTrace tailWord_7110711 prefixEnd_7110711 3651212538212634044210941 := by
  unfold tailWord_7110711
  simp only [CollatzResearch.WordTrace]
  refine ⟨259348936542115934599571987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172899291028077289733047991 259348936542115934599571987)
  ·
    refine ⟨389023404813173901899357981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259348936542115934599571987 389023404813173901899357981)
    ·
      refine ⟨145883776804940213212259243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389023404813173901899357981 145883776804940213212259243)
      ·
        refine ⟨218825665207410319818388865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145883776804940213212259243 218825665207410319818388865)
        ·
          refine ⟨164119248905557739863791649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218825665207410319818388865 164119248905557739863791649)
          ·
            refine ⟨123089436679168304897843737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164119248905557739863791649 123089436679168304897843737)
            ·
              refine ⟨92317077509376228673382803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123089436679168304897843737 92317077509376228673382803)
              ·
                refine ⟨138475616264064343010074205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92317077509376228673382803 138475616264064343010074205)
                ·
                  refine ⟨51928356099024128628777827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138475616264064343010074205 51928356099024128628777827)
                  ·
                    refine ⟨77892534148536192943166741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51928356099024128628777827 77892534148536192943166741)
                    ·
                      refine ⟨3651212538212634044210941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77892534148536192943166741 3651212538212634044210941)
                      ·
                        rfl

theorem cell23_7110711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_7110711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110711 prefixEnd_7110711 := by exact prefixLift 7110711
  have htrace : WordTrace (prefixWord ++ tailWord_7110711) baseStart_7110711 baseEnd_7110711 := by
    simpa [prefixWord, tailWord_7110711, baseEnd_7110711] using wordTrace_append hprefix tailTrace_7110711
  have hstable : (prefixWord ++ tailWord_7110711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110711).length < 2 ^ (prefixWord ++ tailWord_7110711).sum := by decide
  have hdescent : baseEnd_7110711 < baseStart_7110711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110742 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_7110742 : Nat := 118140960795 + 7110742 * 2 ^ 59
def prefixEnd_7110742 : Nat := 4983230072969 + 3 ^ 40 * 7110742 * 2
def baseEnd_7110742 : Nat := 1217076152037641140974433

theorem tailTrace_7110742 : CollatzResearch.WordTrace tailWord_7110742 prefixEnd_7110742 1217076152037641140974433 := by
  unfold tailWord_7110742
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209379200312726680871905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172900044803335751262633653 16209379200312726680871905)
  ·
    refine ⟨12157034400234545010653929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16209379200312726680871905 12157034400234545010653929)
    ·
      refine ⟨9117775800175908757990447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12157034400234545010653929 9117775800175908757990447)
      ·
        refine ⟨13676663700263863136985671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9117775800175908757990447 13676663700263863136985671)
        ·
          refine ⟨20514995550395794705478507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13676663700263863136985671 20514995550395794705478507)
          ·
            refine ⟨30772493325593692058217761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20514995550395794705478507 30772493325593692058217761)
            ·
              refine ⟨23079369994195269043663321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30772493325593692058217761 23079369994195269043663321)
              ·
                refine ⟨17309527495646451782747491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23079369994195269043663321 17309527495646451782747491)
                ·
                  refine ⟨25964291243469677674121237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17309527495646451782747491 25964291243469677674121237)
                  ·
                    refine ⟨1217076152037641140974433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25964291243469677674121237 1217076152037641140974433)
                    ·
                      rfl

theorem cell23_7110742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_7110742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110742 prefixEnd_7110742 := by exact prefixLift 7110742
  have htrace : WordTrace (prefixWord ++ tailWord_7110742) baseStart_7110742 baseEnd_7110742 := by
    simpa [prefixWord, tailWord_7110742, baseEnd_7110742] using wordTrace_append hprefix tailTrace_7110742
  have hstable : (prefixWord ++ tailWord_7110742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110742).length < 2 ^ (prefixWord ++ tailWord_7110742).sum := by decide
  have hdescent : baseEnd_7110742 < baseStart_7110742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110749 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_7110749 : Nat := 118140960795 + 7110749 * 2 ^ 59
def prefixEnd_7110749 : Nat := 4983230072969 + 3 ^ 40 * 7110749 * 2
def baseEnd_7110749 : Nat := 3651232050477504895535767

theorem tailTrace_7110749 : CollatzResearch.WordTrace tailWord_7110749 prefixEnd_7110749 3651232050477504895535767 := by
  unfold tailWord_7110749
  simp only [CollatzResearch.WordTrace]
  refine ⟨259350322515978267089455301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172900215010652178059636867 259350322515978267089455301)
  ·
    refine ⟨48628185471745925079272869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259350322515978267089455301 48628185471745925079272869)
    ·
      refine ⟨9117784775952360952363663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48628185471745925079272869 9117784775952360952363663)
      ·
        refine ⟨13676677163928541428545495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9117784775952360952363663 13676677163928541428545495)
        ·
          refine ⟨20515015745892812142818243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13676677163928541428545495 20515015745892812142818243)
          ·
            refine ⟨30772523618839218214227365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20515015745892812142818243 30772523618839218214227365)
            ·
              refine ⟨5769848178532353415167631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30772523618839218214227365 5769848178532353415167631)
              ·
                refine ⟨8654772267798530122751447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5769848178532353415167631 8654772267798530122751447)
                ·
                  refine ⟨12982158401697795184127171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8654772267798530122751447 12982158401697795184127171)
                  ·
                    refine ⟨19473237602546692776190757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12982158401697795184127171 19473237602546692776190757)
                    ·
                      refine ⟨3651232050477504895535767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19473237602546692776190757 3651232050477504895535767)
                      ·
                        rfl

theorem cell23_7110749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_7110749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110749 prefixEnd_7110749 := by exact prefixLift 7110749
  have htrace : WordTrace (prefixWord ++ tailWord_7110749) baseStart_7110749 baseEnd_7110749 := by
    simpa [prefixWord, tailWord_7110749, baseEnd_7110749] using wordTrace_append hprefix tailTrace_7110749
  have hstable : (prefixWord ++ tailWord_7110749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110749).length < 2 ^ (prefixWord ++ tailWord_7110749).sum := by decide
  have hdescent : baseEnd_7110749 < baseStart_7110749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110751 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 1, 9]
def baseStart_7110751 : Nat := 118140960795 + 7110751 * 2 ^ 59
def prefixEnd_7110751 : Nat := 4983230072969 + 3 ^ 40 * 7110751 * 2
def baseEnd_7110751 : Nat := 1217077692479604629236919

theorem tailTrace_7110751 : CollatzResearch.WordTrace tailWord_7110751 prefixEnd_7110751 1217077692479604629236919 := by
  unfold tailWord_7110751
  simp only [CollatzResearch.WordTrace]
  refine ⟨259350395461971021431028107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172900263641314014287352071 259350395461971021431028107)
  ·
    refine ⟨389025593192956532146542161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259350395461971021431028107 389025593192956532146542161)
    ·
      refine ⟨291769194894717399109906621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389025593192956532146542161 291769194894717399109906621)
      ·
        refine ⟨109413448085519024666214983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291769194894717399109906621 109413448085519024666214983)
        ·
          refine ⟨164120172128278536999322475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109413448085519024666214983 164120172128278536999322475)
          ·
            refine ⟨246180258192417805498983713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164120172128278536999322475 246180258192417805498983713)
            ·
              refine ⟨184635193644313354124237785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246180258192417805498983713 184635193644313354124237785)
              ·
                refine ⟨138476395233235015593178339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184635193644313354124237785 138476395233235015593178339)
                ·
                  refine ⟨207714592849852523389767509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138476395233235015593178339 207714592849852523389767509)
                  ·
                    refine ⟨1217077692479604629236919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 207714592849852523389767509 1217077692479604629236919)
                    ·
                      rfl

theorem cell23_7110751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_7110751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110751 prefixEnd_7110751 := by exact prefixLift 7110751
  have htrace : WordTrace (prefixWord ++ tailWord_7110751) baseStart_7110751 baseEnd_7110751 := by
    simpa [prefixWord, tailWord_7110751, baseEnd_7110751] using wordTrace_append hprefix tailTrace_7110751
  have hstable : (prefixWord ++ tailWord_7110751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110751).length < 2 ^ (prefixWord ++ tailWord_7110751).sum := by decide
  have hdescent : baseEnd_7110751 < baseStart_7110751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110752 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 1, 2, 3]
def baseStart_7110752 : Nat := 118140960795 + 7110752 * 2 ^ 59
def prefixEnd_7110752 : Nat := 4983230072969 + 3 ^ 40 * 7110752 * 2
def baseEnd_7110752 : Nat := 3651233590919468383798253

theorem tailTrace_7110752 : CollatzResearch.WordTrace tailWord_7110752 prefixEnd_7110752 3651233590919468383798253 := by
  unfold tailWord_7110752
  simp only [CollatzResearch.WordTrace]
  refine ⟨129675215967483699300907255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172900287956644932401209673 129675215967483699300907255)
  ·
    refine ⟨194512823951225548951360883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129675215967483699300907255 194512823951225548951360883)
    ·
      refine ⟨291769235926838323427041325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194512823951225548951360883 291769235926838323427041325)
      ·
        refine ⟨109413463472564371285140497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291769235926838323427041325 109413463472564371285140497)
        ·
          refine ⟨82060097604423278463855373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109413463472564371285140497 82060097604423278463855373)
          ·
            refine ⟨30772536601658729423945765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82060097604423278463855373 30772536601658729423945765)
            ·
              refine ⟨5769850612811011766989831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30772536601658729423945765 5769850612811011766989831)
              ·
                refine ⟨8654775919216517650484747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5769850612811011766989831 8654775919216517650484747)
                ·
                  refine ⟨12982163878824776475727121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8654775919216517650484747 12982163878824776475727121)
                  ·
                    refine ⟨9736622909118582356795341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12982163878824776475727121 9736622909118582356795341)
                    ·
                      refine ⟨3651233590919468383798253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9736622909118582356795341 3651233590919468383798253)
                      ·
                        rfl

theorem cell23_7110752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_7110752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110752 prefixEnd_7110752 := by exact prefixLift 7110752
  have htrace : WordTrace (prefixWord ++ tailWord_7110752) baseStart_7110752 baseEnd_7110752 := by
    simpa [prefixWord, tailWord_7110752, baseEnd_7110752] using wordTrace_append hprefix tailTrace_7110752
  have hstable : (prefixWord ++ tailWord_7110752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110752).length < 2 ^ (prefixWord ++ tailWord_7110752).sum := by decide
  have hdescent : baseEnd_7110752 < baseStart_7110752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110805 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 3, 4, 2]
def baseStart_7110805 : Nat := 118140960795 + 7110805 * 2 ^ 59
def prefixEnd_7110805 : Nat := 4983230072969 + 3 ^ 40 * 7110805 * 2
def baseEnd_7110805 : Nat := 3651260805394156676435509

theorem tailTrace_7110805 : CollatzResearch.WordTrace tailWord_7110805 prefixEnd_7110805 3651260805394156676435509 := by
  unfold tailWord_7110805
  simp only [CollatzResearch.WordTrace]
  refine ⟨259352365003775388653493869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172901576669183592435662579 259352365003775388653493869)
  ·
    refine ⟨97257136876415770745060201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259352365003775388653493869 97257136876415770745060201)
    ·
      refine ⟨72942852657311828058795151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97257136876415770745060201 72942852657311828058795151)
      ·
        refine ⟨109414278985967742088192727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72942852657311828058795151 109414278985967742088192727)
        ·
          refine ⟨164121418478951613132289091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109414278985967742088192727 164121418478951613132289091)
          ·
            refine ⟨246182127718427419698433637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164121418478951613132289091 246182127718427419698433637)
            ·
              refine ⟨46159148947205141193456307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246182127718427419698433637 46159148947205141193456307)
              ·
                refine ⟨69238723420807711790184461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46159148947205141193456307 69238723420807711790184461)
                ·
                  refine ⟨25964521282802891921319173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69238723420807711790184461 25964521282802891921319173)
                  ·
                    refine ⟨4868347740525542235247345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25964521282802891921319173 4868347740525542235247345)
                    ·
                      refine ⟨3651260805394156676435509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4868347740525542235247345 3651260805394156676435509)
                      ·
                        rfl

theorem cell23_7110805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_7110805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110805 prefixEnd_7110805 := by exact prefixLift 7110805
  have htrace : WordTrace (prefixWord ++ tailWord_7110805) baseStart_7110805 baseEnd_7110805 := by
    simpa [prefixWord, tailWord_7110805, baseEnd_7110805] using wordTrace_append hprefix tailTrace_7110805
  have hstable : (prefixWord ++ tailWord_7110805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110805).length < 2 ^ (prefixWord ++ tailWord_7110805).sum := by decide
  have hdescent : baseEnd_7110805 < baseStart_7110805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110806 : List Nat := [5, 3, 2, 1, 1, 2, 9]
def baseStart_7110806 : Nat := 118140960795 + 7110806 * 2 ^ 59
def prefixEnd_7110806 : Nat := 4983230072969 + 3 ^ 40 * 7110806 * 2
def baseEnd_7110806 : Nat := 45077300233022360154605

theorem tailTrace_7110806 : CollatzResearch.WordTrace tailWord_7110806 prefixEnd_7110806 45077300233022360154605 := by
  unfold tailWord_7110806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209525092298235364017517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172901600984514510549520181 16209525092298235364017517)
  ·
    refine ⟨6078571909611838261506569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16209525092298235364017517 6078571909611838261506569)
    ·
      refine ⟨4558928932208878696129927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6078571909611838261506569 4558928932208878696129927)
      ·
        refine ⟨6838393398313318044194891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4558928932208878696129927 6838393398313318044194891)
        ·
          refine ⟨10257590097469977066292337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6838393398313318044194891 10257590097469977066292337)
          ·
            refine ⟨7693192573102482799719253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10257590097469977066292337 7693192573102482799719253)
            ·
              refine ⟨45077300233022360154605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7693192573102482799719253 45077300233022360154605)
              ·
                rfl

theorem cell23_7110806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 9].length) (baseStart_7110806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110806 prefixEnd_7110806 := by exact prefixLift 7110806
  have htrace : WordTrace (prefixWord ++ tailWord_7110806) baseStart_7110806 baseEnd_7110806 := by
    simpa [prefixWord, tailWord_7110806, baseEnd_7110806] using wordTrace_append hprefix tailTrace_7110806
  have hstable : (prefixWord ++ tailWord_7110806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110806).length < 2 ^ (prefixWord ++ tailWord_7110806).sum := by decide
  have hdescent : baseEnd_7110806 < baseStart_7110806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110833 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 2, 1, 3]
def baseStart_7110833 : Nat := 118140960795 + 7110833 * 2 ^ 59
def prefixEnd_7110833 : Nat := 4983230072969 + 3 ^ 40 * 7110833 * 2
def baseEnd_7110833 : Nat := 3651275182852482566885381

theorem tailTrace_7110833 : CollatzResearch.WordTrace tailWord_7110833 prefixEnd_7110833 3651275182852482566885381 := by
  unfold tailWord_7110833
  simp only [CollatzResearch.WordTrace]
  refine ⟨259353386247673949435513153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172902257498449299623675435 259353386247673949435513153)
  ·
    refine ⟨194515039685755462076634865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259353386247673949435513153 194515039685755462076634865)
    ·
      refine ⟨145886279764316596557476149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194515039685755462076634865 145886279764316596557476149)
      ·
        refine ⟨13676838727904680927263389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145886279764316596557476149 13676838727904680927263389)
        ·
          refine ⟨5128814522964255347723771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13676838727904680927263389 5128814522964255347723771)
          ·
            refine ⟨7693221784446383021585657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128814522964255347723771 7693221784446383021585657)
            ·
              refine ⟨5769916338334787266189243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7693221784446383021585657 5769916338334787266189243)
              ·
                refine ⟨8654874507502180899283865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5769916338334787266189243 8654874507502180899283865)
                ·
                  refine ⟨6491155880626635674462899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8654874507502180899283865 6491155880626635674462899)
                  ·
                    refine ⟨9736733820939953511694349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6491155880626635674462899 9736733820939953511694349)
                    ·
                      refine ⟨3651275182852482566885381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9736733820939953511694349 3651275182852482566885381)
                      ·
                        rfl

theorem cell23_7110833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_7110833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110833 prefixEnd_7110833 := by exact prefixLift 7110833
  have htrace : WordTrace (prefixWord ++ tailWord_7110833) baseStart_7110833 baseEnd_7110833 := by
    simpa [prefixWord, tailWord_7110833, baseEnd_7110833] using wordTrace_append hprefix tailTrace_7110833
  have hstable : (prefixWord ++ tailWord_7110833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110833).length < 2 ^ (prefixWord ++ tailWord_7110833).sum := by decide
  have hdescent : baseEnd_7110833 < baseStart_7110833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110839 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 2, 2, 2]
def baseStart_7110839 : Nat := 118140960795 + 7110839 * 2 ^ 59
def prefixEnd_7110839 : Nat := 4983230072969 + 3 ^ 40 * 7110839 * 2
def baseEnd_7110839 : Nat := 3651278263736409543410353

theorem tailTrace_7110839 : CollatzResearch.WordTrace tailWord_7110839 prefixEnd_7110839 3651278263736409543410353 := by
  unfold tailWord_7110839
  simp only [CollatzResearch.WordTrace]
  refine ⟨259353605085652212460231571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172902403390434808306821047 259353605085652212460231571)
  ·
    refine ⟨389030407628478318690347357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259353605085652212460231571 389030407628478318690347357)
    ·
      refine ⟨145886402860679369508880259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389030407628478318690347357 145886402860679369508880259)
      ·
        refine ⟨218829604291019054263320389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145886402860679369508880259 218829604291019054263320389)
        ·
          refine ⟨41030550804566072674372573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218829604291019054263320389 41030550804566072674372573)
          ·
            refine ⟨15386456551712277252889715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41030550804566072674372573 15386456551712277252889715)
            ·
              refine ⟨23079684827568415879334573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15386456551712277252889715 23079684827568415879334573)
              ·
                refine ⟨8654881810338155954750465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23079684827568415879334573 8654881810338155954750465)
                ·
                  refine ⟨6491161357753616966062849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8654881810338155954750465 6491161357753616966062849)
                  ·
                    refine ⟨4868371018315212724547137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6491161357753616966062849 4868371018315212724547137)
                    ·
                      refine ⟨3651278263736409543410353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4868371018315212724547137 3651278263736409543410353)
                      ·
                        rfl

theorem cell23_7110839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 2, 2].length) (baseStart_7110839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110839 prefixEnd_7110839 := by exact prefixLift 7110839
  have htrace : WordTrace (prefixWord ++ tailWord_7110839) baseStart_7110839 baseEnd_7110839 := by
    simpa [prefixWord, tailWord_7110839, baseEnd_7110839] using wordTrace_append hprefix tailTrace_7110839
  have hstable : (prefixWord ++ tailWord_7110839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110839).length < 2 ^ (prefixWord ++ tailWord_7110839).sum := by decide
  have hdescent : baseEnd_7110839 < baseStart_7110839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110885 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_7110885 : Nat := 118140960795 + 7110885 * 2 ^ 59
def prefixEnd_7110885 : Nat := 4983230072969 + 3 ^ 40 * 7110885 * 2
def baseEnd_7110885 : Nat := 3651301883846516363435141

theorem tailTrace_7110885 : CollatzResearch.WordTrace tailWord_7110885 prefixEnd_7110885 3651301883846516363435141 := by
  unfold tailWord_7110885
  simp only [CollatzResearch.WordTrace]
  refine ⟨259355282843485562316406109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172903521895657041544270739 259355282843485562316406109)
  ·
    refine ⟨97258231066307085868652291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259355282843485562316406109 97258231066307085868652291)
    ·
      refine ⟨145887346599460628802978437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97258231066307085868652291 145887346599460628802978437)
      ·
        refine ⟨27353877487398867900558457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145887346599460628802978437 27353877487398867900558457)
        ·
          refine ⟨20515408115549150925418843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27353877487398867900558457 20515408115549150925418843)
          ·
            refine ⟨30773112173323726388128265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20515408115549150925418843 30773112173323726388128265)
            ·
              refine ⟨23079834129992794791096199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30773112173323726388128265 23079834129992794791096199)
              ·
                refine ⟨34619751194989192186644299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23079834129992794791096199 34619751194989192186644299)
                ·
                  refine ⟨51929626792483788279966449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34619751194989192186644299 51929626792483788279966449)
                  ·
                    refine ⟨38947220094362841209974837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51929626792483788279966449 38947220094362841209974837)
                    ·
                      refine ⟨3651301883846516363435141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38947220094362841209974837 3651301883846516363435141)
                      ·
                        rfl

theorem cell23_7110885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_7110885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110885 prefixEnd_7110885 := by exact prefixLift 7110885
  have htrace : WordTrace (prefixWord ++ tailWord_7110885) baseStart_7110885 baseEnd_7110885 := by
    simpa [prefixWord, tailWord_7110885, baseEnd_7110885] using wordTrace_append hprefix tailTrace_7110885
  have hstable : (prefixWord ++ tailWord_7110885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110885).length < 2 ^ (prefixWord ++ tailWord_7110885).sum := by decide
  have hdescent : baseEnd_7110885 < baseStart_7110885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110915 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 3]
def baseStart_7110915 : Nat := 118140960795 + 7110915 * 2 ^ 59
def prefixEnd_7110915 : Nat := 4983230072969 + 3 ^ 40 * 7110915 * 2
def baseEnd_7110915 : Nat := 3651317288266151246060003

theorem tailTrace_7110915 : CollatzResearch.WordTrace tailWord_7110915 prefixEnd_7110915 3651317288266151246060003 := by
  unfold tailWord_7110915
  simp only [CollatzResearch.WordTrace]
  refine ⟨259356377033376877439998199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172904251355584584959998799 259356377033376877439998199)
  ·
    refine ⟨389034565550065316159997299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259356377033376877439998199 389034565550065316159997299)
    ·
      refine ⟨583551848325097974239995949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389034565550065316159997299 583551848325097974239995949)
      ·
        refine ⟨218831943121911740339998481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 583551848325097974239995949 218831943121911740339998481)
        ·
          refine ⟨164123957341433805254998861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218831943121911740339998481 164123957341433805254998861)
          ·
            refine ⟨61546484003037676970624573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164123957341433805254998861 61546484003037676970624573)
            ·
              refine ⟨23079931501139128863984215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61546484003037676970624573 23079931501139128863984215)
              ·
                refine ⟨34619897251708693295976323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23079931501139128863984215 34619897251708693295976323)
                ·
                  refine ⟨51929845877563039943964485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34619897251708693295976323 51929845877563039943964485)
                  ·
                    refine ⟨9736846102043069989493341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51929845877563039943964485 9736846102043069989493341)
                    ·
                      refine ⟨3651317288266151246060003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9736846102043069989493341 3651317288266151246060003)
                      ·
                        rfl

theorem cell23_7110915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_7110915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110915 prefixEnd_7110915 := by exact prefixLift 7110915
  have htrace : WordTrace (prefixWord ++ tailWord_7110915) baseStart_7110915 baseEnd_7110915 := by
    simpa [prefixWord, tailWord_7110915, baseEnd_7110915] using wordTrace_append hprefix tailTrace_7110915
  have hstable : (prefixWord ++ tailWord_7110915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110915).length < 2 ^ (prefixWord ++ tailWord_7110915).sum := by decide
  have hdescent : baseEnd_7110915 < baseStart_7110915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110935 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 8]
def baseStart_7110935 : Nat := 118140960795 + 7110935 * 2 ^ 59
def prefixEnd_7110935 : Nat := 4983230072969 + 3 ^ 40 * 7110935 * 2
def baseEnd_7110935 : Nat := 405703061986582351978879

theorem tailTrace_7110935 : CollatzResearch.WordTrace tailWord_7110935 prefixEnd_7110935 405703061986582351978879 := by
  unfold tailWord_7110935
  simp only [CollatzResearch.WordTrace]
  refine ⟨259357106493304420855726259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172904737662202947237150839 259357106493304420855726259)
  ·
    refine ⟨389035659739956631283589389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259357106493304420855726259 389035659739956631283589389)
    ·
      refine ⟨145888372402483736731346021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389035659739956631283589389 145888372402483736731346021)
      ·
        refine ⟨27354069825465700637127379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145888372402483736731346021 27354069825465700637127379)
        ·
          refine ⟨41031104738198550955691069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27354069825465700637127379 41031104738198550955691069)
          ·
            refine ⟨15386664276824456608384151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41031104738198550955691069 15386664276824456608384151)
            ·
              refine ⟨23079996415236684912576227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15386664276824456608384151 23079996415236684912576227)
              ·
                refine ⟨34619994622855027368864341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23079996415236684912576227 34619994622855027368864341)
                ·
                  refine ⟨405703061986582351978879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34619994622855027368864341 405703061986582351978879)
                  ·
                    rfl

theorem cell23_7110935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 8].length) (baseStart_7110935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110935 prefixEnd_7110935 := by exact prefixLift 7110935
  have htrace : WordTrace (prefixWord ++ tailWord_7110935) baseStart_7110935 baseEnd_7110935 := by
    simpa [prefixWord, tailWord_7110935, baseEnd_7110935] using wordTrace_append hprefix tailTrace_7110935
  have hstable : (prefixWord ++ tailWord_7110935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110935).length < 2 ^ (prefixWord ++ tailWord_7110935).sum := by decide
  have hdescent : baseEnd_7110935 < baseStart_7110935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110972 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 1, 5, 2]
def baseStart_7110972 : Nat := 118140960795 + 7110972 * 2 ^ 59
def prefixEnd_7110972 : Nat := 4983230072969 + 3 ^ 40 * 7110972 * 2
def baseEnd_7110972 : Nat := 3651346556663457523047241

theorem tailTrace_7110972 : CollatzResearch.WordTrace tailWord_7110972 prefixEnd_7110972 3651346556663457523047241 := by
  unfold tailWord_7110972
  simp only [CollatzResearch.WordTrace]
  refine ⟨129679227997085188087411585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172905637329446917449882113 129679227997085188087411585)
  ·
    refine ⟨97259420997813891065558689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129679227997085188087411585 97259420997813891065558689)
    ·
      refine ⟨72944565748360418299169017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97259420997813891065558689 72944565748360418299169017)
      ·
        refine ⟨54708424311270313724376763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72944565748360418299169017 54708424311270313724376763)
        ·
          refine ⟨82062636466905470586565145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54708424311270313724376763 82062636466905470586565145)
          ·
            refine ⟨61546977350179102939923859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82062636466905470586565145 61546977350179102939923859)
            ·
              refine ⟨92320466025268654409885789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61546977350179102939923859 92320466025268654409885789)
              ·
                refine ⟨34620174759475745403707171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92320466025268654409885789 34620174759475745403707171)
                ·
                  refine ⟨51930262139213618105560757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34620174759475745403707171 51930262139213618105560757)
                  ·
                    refine ⟨4868462075551276697396321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51930262139213618105560757 4868462075551276697396321)
                    ·
                      refine ⟨3651346556663457523047241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4868462075551276697396321 3651346556663457523047241)
                      ·
                        rfl

theorem cell23_7110972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_7110972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110972 prefixEnd_7110972 := by exact prefixLift 7110972
  have htrace : WordTrace (prefixWord ++ tailWord_7110972) baseStart_7110972 baseEnd_7110972 := by
    simpa [prefixWord, tailWord_7110972, baseEnd_7110972] using wordTrace_append hprefix tailTrace_7110972
  have hstable : (prefixWord ++ tailWord_7110972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110972).length < 2 ^ (prefixWord ++ tailWord_7110972).sum := by decide
  have hdescent : baseEnd_7110972 < baseStart_7110972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110985 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 4]
def baseStart_7110985 : Nat := 118140960795 + 7110985 * 2 ^ 59
def prefixEnd_7110985 : Nat := 4983230072969 + 3 ^ 40 * 7110985 * 2
def baseEnd_7110985 : Nat := 3651353231911965972184681

theorem tailTrace_7110985 : CollatzResearch.WordTrace tailWord_7110985 prefixEnd_7110985 3651353231911965972184681 := by
  unfold tailWord_7110985
  simp only [CollatzResearch.WordTrace]
  refine ⟨259358930143123279395046409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172905953428748852930030939 259358930143123279395046409)
  ·
    refine ⟨194519197607342459546284807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259358930143123279395046409 194519197607342459546284807)
    ·
      refine ⟨291778796411013689319427211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194519197607342459546284807 291778796411013689319427211)
      ·
        refine ⟨437668194616520533979140817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291778796411013689319427211 437668194616520533979140817)
        ·
          refine ⟨328251145962390400484355613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437668194616520533979140817 328251145962390400484355613)
          ·
            refine ⟨123094179735896400181633355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328251145962390400484355613 123094179735896400181633355)
            ·
              refine ⟨184641269603844600272450033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123094179735896400181633355 184641269603844600272450033)
              ·
                refine ⟨138480952202883450204337525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184641269603844600272450033 138480952202883450204337525)
                ·
                  refine ⟨12982589269020323456656643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138480952202883450204337525 12982589269020323456656643)
                  ·
                    refine ⟨19473883903530485184984965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12982589269020323456656643 19473883903530485184984965)
                    ·
                      refine ⟨3651353231911965972184681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19473883903530485184984965 3651353231911965972184681)
                      ·
                        rfl

theorem cell23_7110985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_7110985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110985 prefixEnd_7110985 := by exact prefixLift 7110985
  have htrace : WordTrace (prefixWord ++ tailWord_7110985) baseStart_7110985 baseEnd_7110985 := by
    simpa [prefixWord, tailWord_7110985, baseEnd_7110985] using wordTrace_append hprefix tailTrace_7110985
  have hstable : (prefixWord ++ tailWord_7110985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110985).length < 2 ^ (prefixWord ++ tailWord_7110985).sum := by decide
  have hdescent : baseEnd_7110985 < baseStart_7110985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7110996 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_7110996 : Nat := 118140960795 + 7110996 * 2 ^ 59
def prefixEnd_7110996 : Nat := 4983230072969 + 3 ^ 40 * 7110996 * 2
def baseEnd_7110996 : Nat := 3651358880199165429147131

theorem tailTrace_7110996 : CollatzResearch.WordTrace tailWord_7110996 prefixEnd_7110996 3651358880199165429147131 := by
  unfold tailWord_7110996
  simp only [CollatzResearch.WordTrace]
  refine ⟨129679665673041714136848421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172906220897388952182464561 129679665673041714136848421)
  ·
    refine ⟨24314937313695321400659079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129679665673041714136848421 24314937313695321400659079)
    ·
      refine ⟨36472405970542982100988619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24314937313695321400659079 36472405970542982100988619)
      ·
        refine ⟨54708608955814473151482929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36472405970542982100988619 54708608955814473151482929)
        ·
          refine ⟨41031456716860854863612197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54708608955814473151482929 41031456716860854863612197)
          ·
            refine ⟨7693398134411410286927287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41031456716860854863612197 7693398134411410286927287)
            ·
              refine ⟨11540097201617115430390931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7693398134411410286927287 11540097201617115430390931)
              ·
                refine ⟨17310145802425673145586397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11540097201617115430390931 17310145802425673145586397)
                ·
                  refine ⟨6491304675909627429594899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17310145802425673145586397 6491304675909627429594899)
                  ·
                    refine ⟨9736957013864441144392349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6491304675909627429594899 9736957013864441144392349)
                    ·
                      refine ⟨3651358880199165429147131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9736957013864441144392349 3651358880199165429147131)
                      ·
                        rfl

theorem cell23_7110996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_7110996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7110996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7110996 prefixEnd_7110996 := by exact prefixLift 7110996
  have htrace : WordTrace (prefixWord ++ tailWord_7110996) baseStart_7110996 baseEnd_7110996 := by
    simpa [prefixWord, tailWord_7110996, baseEnd_7110996] using wordTrace_append hprefix tailTrace_7110996
  have hstable : (prefixWord ++ tailWord_7110996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7110996).length < 2 ^ (prefixWord ++ tailWord_7110996).sum := by decide
  have hdescent : baseEnd_7110996 < baseStart_7110996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7110996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111042 : List Nat := [3, 4, 2, 1, 13]
def baseStart_7111042 : Nat := 118140960795 + 7111042 * 2 ^ 59
def prefixEnd_7111042 : Nat := 4983230072969 + 3 ^ 40 * 7111042 * 2
def baseEnd_7111042 : Nat := 5008755144457163579111

theorem tailTrace_7111042 : CollatzResearch.WordTrace tailWord_7111042 prefixEnd_7111042 5008755144457163579111 := by
  unfold tailWord_7111042
  simp only [CollatzResearch.WordTrace]
  refine ⟨64840252275979194532467845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172907339402611185419914253 64840252275979194532467845)
  ·
    refine ⟨12157547301746098974837721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64840252275979194532467845 12157547301746098974837721)
    ·
      refine ⟨9118160476309574231128291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12157547301746098974837721 9118160476309574231128291)
      ·
        refine ⟨13677240714464361346692437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9118160476309574231128291 13677240714464361346692437)
        ·
          refine ⟨5008755144457163579111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13677240714464361346692437 5008755144457163579111)
          ·
            rfl

theorem cell23_7111042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 13].length) (baseStart_7111042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111042 prefixEnd_7111042 := by exact prefixLift 7111042
  have htrace : WordTrace (prefixWord ++ tailWord_7111042) baseStart_7111042 baseEnd_7111042 := by
    simpa [prefixWord, tailWord_7111042, baseEnd_7111042] using wordTrace_append hprefix tailTrace_7111042
  have hstable : (prefixWord ++ tailWord_7111042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111042).length < 2 ^ (prefixWord ++ tailWord_7111042).sum := by decide
  have hdescent : baseEnd_7111042 < baseStart_7111042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111102 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_7111102 : Nat := 118140960795 + 7111102 * 2 ^ 59
def prefixEnd_7111102 : Nat := 4983230072969 + 3 ^ 40 * 7111102 * 2
def baseEnd_7111102 : Nat := 1217137769716180671473881

theorem tailTrace_7111102 : CollatzResearch.WordTrace tailWord_7111102 prefixEnd_7111102 1217137769716180671473881 := by
  unfold tailWord_7111102
  simp only [CollatzResearch.WordTrace]
  refine ⟨32420399685462426047131945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172908798322466272251370373 32420399685462426047131945)
  ·
    refine ⟨24315299764096819535348959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32420399685462426047131945 24315299764096819535348959)
    ·
      refine ⟨36472949646145229303023439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24315299764096819535348959 36472949646145229303023439)
      ·
        refine ⟨54709424469217843954535159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36472949646145229303023439 54709424469217843954535159)
        ·
          refine ⟨82064136703826765931802739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54709424469217843954535159 82064136703826765931802739)
          ·
            refine ⟨123096205055740148897704109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82064136703826765931802739 123096205055740148897704109)
            ·
              refine ⟨46161076895902555836639041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123096205055740148897704109 46161076895902555836639041)
              ·
                refine ⟨34620807671926916877479281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46161076895902555836639041 34620807671926916877479281)
                ·
                  refine ⟨25965605753945187658109461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34620807671926916877479281 25965605753945187658109461)
                  ·
                    refine ⟨1217137769716180671473881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25965605753945187658109461 1217137769716180671473881)
                    ·
                      rfl

theorem cell23_7111102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_7111102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111102 prefixEnd_7111102 := by exact prefixLift 7111102
  have htrace : WordTrace (prefixWord ++ tailWord_7111102) baseStart_7111102 baseEnd_7111102 := by
    simpa [prefixWord, tailWord_7111102, baseEnd_7111102] using wordTrace_append hprefix tailTrace_7111102
  have hstable : (prefixWord ++ tailWord_7111102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111102).length < 2 ^ (prefixWord ++ tailWord_7111102).sum := by decide
  have hdescent : baseEnd_7111102 < baseStart_7111102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111199 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 4, 4, 2]
def baseStart_7111199 : Nat := 118140960795 + 7111199 * 2 ^ 59
def prefixEnd_7111199 : Nat := 4983230072969 + 3 ^ 40 * 7111199 * 2
def baseEnd_7111199 : Nat := 3651463116772028134908697

theorem tailTrace_7111199 : CollatzResearch.WordTrace tailWord_7111199 prefixEnd_7111199 3651463116772028134908697 := by
  unfold tailWord_7111199
  simp only [CollatzResearch.WordTrace]
  refine ⟨259366735364347993943336651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172911156909565329295557767 259366735364347993943336651)
  ·
    refine ⟨389050103046521990915004977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259366735364347993943336651 389050103046521990915004977)
    ·
      refine ⟨291787577284891493186253733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389050103046521990915004977 291787577284891493186253733)
      ·
        refine ⟨54710170740917154972422575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291787577284891493186253733 54710170740917154972422575)
        ·
          refine ⟨82065256111375732458633863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54710170740917154972422575 82065256111375732458633863)
          ·
            refine ⟨123097884167063598687950795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82065256111375732458633863 123097884167063598687950795)
            ·
              refine ⟨184646826250595398031926193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123097884167063598687950795 184646826250595398031926193)
              ·
                refine ⟨138485119687946548523944645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184646826250595398031926193 138485119687946548523944645)
                ·
                  refine ⟨25965959941489977848239621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138485119687946548523944645 25965959941489977848239621)
                  ·
                    refine ⟨4868617489029370846544929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25965959941489977848239621 4868617489029370846544929)
                    ·
                      refine ⟨3651463116772028134908697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4868617489029370846544929 3651463116772028134908697)
                      ·
                        rfl

theorem cell23_7111199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_7111199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111199 prefixEnd_7111199 := by exact prefixLift 7111199
  have htrace : WordTrace (prefixWord ++ tailWord_7111199) baseStart_7111199 baseEnd_7111199 := by
    simpa [prefixWord, tailWord_7111199, baseEnd_7111199] using wordTrace_append hprefix tailTrace_7111199
  have hstable : (prefixWord ++ tailWord_7111199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111199).length < 2 ^ (prefixWord ++ tailWord_7111199).sum := by decide
  have hdescent : baseEnd_7111199 < baseStart_7111199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111219 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 3]
def baseStart_7111219 : Nat := 118140960795 + 7111219 * 2 ^ 59
def prefixEnd_7111219 : Nat := 4983230072969 + 3 ^ 40 * 7111219 * 2
def baseEnd_7111219 : Nat := 3651473386385118056658605

theorem tailTrace_7111219 : CollatzResearch.WordTrace tailWord_7111219 prefixEnd_7111219 3651473386385118056658605 := by
  unfold tailWord_7111219
  simp only [CollatzResearch.WordTrace]
  refine ⟨259367464824275537359064711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172911643216183691572709807 259367464824275537359064711)
  ·
    refine ⟨389051197236413306038597067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259367464824275537359064711 389051197236413306038597067)
    ·
      refine ⟨583576795854619959057895601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389051197236413306038597067 583576795854619959057895601)
      ·
        refine ⟨437682596890964969293421701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583576795854619959057895601 437682596890964969293421701)
        ·
          refine ⟨82065486917055931742516569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 437682596890964969293421701 82065486917055931742516569)
          ·
            refine ⟨61549115187791948806887427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82065486917055931742516569 61549115187791948806887427)
            ·
              refine ⟨92323672781687923210331141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61549115187791948806887427 92323672781687923210331141)
              ·
                refine ⟨17310688646566485601937089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92323672781687923210331141 17310688646566485601937089)
                ·
                  refine ⟨12983016484924864201452817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17310688646566485601937089 12983016484924864201452817)
                  ·
                    refine ⟨9737262363693648151089613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12983016484924864201452817 9737262363693648151089613)
                    ·
                      refine ⟨3651473386385118056658605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9737262363693648151089613 3651473386385118056658605)
                      ·
                        rfl

theorem cell23_7111219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 3].length) (baseStart_7111219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111219 prefixEnd_7111219 := by exact prefixLift 7111219
  have htrace : WordTrace (prefixWord ++ tailWord_7111219) baseStart_7111219 baseEnd_7111219 := by
    simpa [prefixWord, tailWord_7111219, baseEnd_7111219] using wordTrace_append hprefix tailTrace_7111219
  have hstable : (prefixWord ++ tailWord_7111219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111219).length < 2 ^ (prefixWord ++ tailWord_7111219).sum := by decide
  have hdescent : baseEnd_7111219 < baseStart_7111219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111239 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 6]
def baseStart_7111239 : Nat := 118140960795 + 7111239 * 2 ^ 59
def prefixEnd_7111239 : Nat := 4983230072969 + 3 ^ 40 * 7111239 * 2
def baseEnd_7111239 : Nat := 405720406222023108712057

theorem tailTrace_7111239 : CollatzResearch.WordTrace tailWord_7111239 prefixEnd_7111239 405720406222023108712057 := by
  unfold tailWord_7111239
  simp only [CollatzResearch.WordTrace]
  refine ⟨259368194284203080774792771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172912129522802053849861847 259368194284203080774792771)
  ·
    refine ⟨389052291426304621162189157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259368194284203080774792771 389052291426304621162189157)
    ·
      refine ⟨72947304642432116467910467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389052291426304621162189157 72947304642432116467910467)
      ·
        refine ⟨109420956963648174701865701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72947304642432116467910467 109420956963648174701865701)
        ·
          refine ⟨20516429430684032756599819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109420956963648174701865701 20516429430684032756599819)
          ·
            refine ⟨30774644146026049134899729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20516429430684032756599819 30774644146026049134899729)
            ·
              refine ⟨23080983109519536851174797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30774644146026049134899729 23080983109519536851174797)
              ·
                refine ⟨8655368666069826319190549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23080983109519536851174797 8655368666069826319190549)
                ·
                  refine ⟨405720406222023108712057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8655368666069826319190549 405720406222023108712057)
                  ·
                    rfl

theorem cell23_7111239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 6].length) (baseStart_7111239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111239 prefixEnd_7111239 := by exact prefixLift 7111239
  have htrace : WordTrace (prefixWord ++ tailWord_7111239) baseStart_7111239 baseEnd_7111239 := by
    simpa [prefixWord, tailWord_7111239, baseEnd_7111239] using wordTrace_append hprefix tailTrace_7111239
  have hstable : (prefixWord ++ tailWord_7111239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111239).length < 2 ^ (prefixWord ++ tailWord_7111239).sum := by decide
  have hdescent : baseEnd_7111239 < baseStart_7111239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111260 : List Nat := [2, 2, 4, 1, 3, 1, 2, 3, 1, 4]
def baseStart_7111260 : Nat := 118140960795 + 7111260 * 2 ^ 59
def prefixEnd_7111260 : Nat := 4983230072969 + 3 ^ 40 * 7111260 * 2
def baseEnd_7111260 : Nat := 1217164813030650798748639

theorem tailTrace_7111260 : CollatzResearch.WordTrace tailWord_7111260 prefixEnd_7111260 1217164813030650798748639 := by
  unfold tailWord_7111260
  simp only [CollatzResearch.WordTrace]
  refine ⟨129684480108563500680653617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172912640144751334240871489 129684480108563500680653617)
  ·
    refine ⟨97263360081422625510490213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129684480108563500680653617 97263360081422625510490213)
    ·
      refine ⟨18236880015266742283216915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97263360081422625510490213 18236880015266742283216915)
      ·
        refine ⟨27355320022900113424825373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18236880015266742283216915 27355320022900113424825373)
        ·
          refine ⟨10258245008587542534309515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27355320022900113424825373 10258245008587542534309515)
          ·
            refine ⟨15387367512881313801464273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10258245008587542534309515 15387367512881313801464273)
            ·
              refine ⟨11540525634660985351098205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15387367512881313801464273 11540525634660985351098205)
              ·
                refine ⟨4327697112997869506661827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11540525634660985351098205 4327697112997869506661827)
                ·
                  refine ⟨6491545669496804259992741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327697112997869506661827 6491545669496804259992741)
                  ·
                    refine ⟨1217164813030650798748639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6491545669496804259992741 1217164813030650798748639)
                    ·
                      rfl

theorem cell23_7111260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_7111260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111260 prefixEnd_7111260 := by exact prefixLift 7111260
  have htrace : WordTrace (prefixWord ++ tailWord_7111260) baseStart_7111260 baseEnd_7111260 := by
    simpa [prefixWord, tailWord_7111260, baseEnd_7111260] using wordTrace_append hprefix tailTrace_7111260
  have hstable : (prefixWord ++ tailWord_7111260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111260).length < 2 ^ (prefixWord ++ tailWord_7111260).sum := by decide
  have hdescent : baseEnd_7111260 < baseStart_7111260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111276 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 2, 3, 2]
def baseStart_7111276 : Nat := 118140960795 + 7111276 * 2 ^ 59
def prefixEnd_7111276 : Nat := 4983230072969 + 3 ^ 40 * 7111276 * 2
def baseEnd_7111276 : Nat := 3651502654782424333645843

theorem tailTrace_7111276 : CollatzResearch.WordTrace tailWord_7111276 prefixEnd_7111276 3651502654782424333645843 := by
  unfold tailWord_7111276
  simp only [CollatzResearch.WordTrace]
  refine ⟨129684771892534518046944841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172913029190046024062593121 129684771892534518046944841)
  ·
    refine ⟨97263578919400888535208631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129684771892534518046944841 97263578919400888535208631)
    ·
      refine ⟨145895368379101332802812947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97263578919400888535208631 145895368379101332802812947)
      ·
        refine ⟨218843052568651999204219421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145895368379101332802812947 218843052568651999204219421)
        ·
          refine ⟨82066144713244499701582283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218843052568651999204219421 82066144713244499701582283)
          ·
            refine ⟨123099217069866749552373425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82066144713244499701582283 123099217069866749552373425)
            ·
              refine ⟨92324412802400062164280069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123099217069866749552373425 92324412802400062164280069)
              ·
                refine ⟨17310827400450011655802513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92324412802400062164280069 17310827400450011655802513)
                ·
                  refine ⟨12983120550337508741851885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17310827400450011655802513 12983120550337508741851885)
                  ·
                    refine ⟨4868670206376565778194457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12983120550337508741851885 4868670206376565778194457)
                    ·
                      refine ⟨3651502654782424333645843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4868670206376565778194457 3651502654782424333645843)
                      ·
                        rfl

theorem cell23_7111276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 3, 2].length) (baseStart_7111276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111276 prefixEnd_7111276 := by exact prefixLift 7111276
  have htrace : WordTrace (prefixWord ++ tailWord_7111276) baseStart_7111276 baseEnd_7111276 := by
    simpa [prefixWord, tailWord_7111276, baseEnd_7111276] using wordTrace_append hprefix tailTrace_7111276
  have hstable : (prefixWord ++ tailWord_7111276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111276).length < 2 ^ (prefixWord ++ tailWord_7111276).sum := by decide
  have hdescent : baseEnd_7111276 < baseStart_7111276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111299 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 1, 6]
def baseStart_7111299 : Nat := 118140960795 + 7111299 * 2 ^ 59
def prefixEnd_7111299 : Nat := 4983230072969 + 3 ^ 40 * 7111299 * 2
def baseEnd_7111299 : Nat := 1217171488279159247886079

theorem tailTrace_7111299 : CollatzResearch.WordTrace tailWord_7111299 prefixEnd_7111299 1217171488279159247886079 := by
  unfold tailWord_7111299
  simp only [CollatzResearch.WordTrace]
  refine ⟨259370382663985711021976951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172913588442657140681317967 259370382663985711021976951)
  ·
    refine ⟨389055573995978566532965427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259370382663985711021976951 389055573995978566532965427)
    ·
      refine ⟨583583360993967849799448141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389055573995978566532965427 583583360993967849799448141)
      ·
        refine ⟨218843760372737943674793053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 583583360993967849799448141 218843760372737943674793053)
        ·
          refine ⟨82066410139776728878047395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218843760372737943674793053 82066410139776728878047395)
          ·
            refine ⟨123099615209665093317071093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82066410139776728878047395 123099615209665093317071093)
            ·
              refine ⟨11540588925906102498475415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123099615209665093317071093 11540588925906102498475415)
              ·
                refine ⟨17310883388859153747713123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11540588925906102498475415 17310883388859153747713123)
                ·
                  refine ⟨25966325083288730621569685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17310883388859153747713123 25966325083288730621569685)
                  ·
                    refine ⟨1217171488279159247886079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25966325083288730621569685 1217171488279159247886079)
                    ·
                      rfl

theorem cell23_7111299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 6].length) (baseStart_7111299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111299 prefixEnd_7111299 := by exact prefixLift 7111299
  have htrace : WordTrace (prefixWord ++ tailWord_7111299) baseStart_7111299 baseEnd_7111299 := by
    simpa [prefixWord, tailWord_7111299, baseEnd_7111299] using wordTrace_append hprefix tailTrace_7111299
  have hstable : (prefixWord ++ tailWord_7111299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111299).length < 2 ^ (prefixWord ++ tailWord_7111299).sum := by decide
  have hdescent : baseEnd_7111299 < baseStart_7111299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111319 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_7111319 : Nat := 118140960795 + 7111319 * 2 ^ 59
def prefixEnd_7111319 : Nat := 4983230072969 + 3 ^ 40 * 7111319 * 2
def baseEnd_7111319 : Nat := 3651524734450567665408145

theorem tailTrace_7111319 : CollatzResearch.WordTrace tailWord_7111319 prefixEnd_7111319 3651524734450567665408145 := by
  unfold tailWord_7111319
  simp only [CollatzResearch.WordTrace]
  refine ⟨259371112123913254437705011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172914074749275502958470007 259371112123913254437705011)
  ·
    refine ⟨389056668185869881656557517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259371112123913254437705011 389056668185869881656557517)
    ·
      refine ⟨145896250569701205621209069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389056668185869881656557517 145896250569701205621209069)
      ·
        refine ⟨54711093963637952107953401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145896250569701205621209069 54711093963637952107953401)
        ·
          refine ⟨41033320472728464080965051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54711093963637952107953401 41033320472728464080965051)
          ·
            refine ⟨61549980709092696121447577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41033320472728464080965051 61549980709092696121447577)
            ·
              refine ⟨46162485531819522091085683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61549980709092696121447577 46162485531819522091085683)
              ·
                refine ⟨69243728297729283136628525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46162485531819522091085683 69243728297729283136628525)
                ·
                  refine ⟨25966398111648481176235697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69243728297729283136628525 25966398111648481176235697)
                  ·
                    refine ⟨19474798583736360882176773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25966398111648481176235697 19474798583736360882176773)
                    ·
                      refine ⟨3651524734450567665408145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19474798583736360882176773 3651524734450567665408145)
                      ·
                        rfl

theorem cell23_7111319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_7111319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111319 prefixEnd_7111319 := by exact prefixLift 7111319
  have htrace : WordTrace (prefixWord ++ tailWord_7111319) baseStart_7111319 baseEnd_7111319 := by
    simpa [prefixWord, tailWord_7111319, baseEnd_7111319] using wordTrace_append hprefix tailTrace_7111319
  have hstable : (prefixWord ++ tailWord_7111319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111319).length < 2 ^ (prefixWord ++ tailWord_7111319).sum := by decide
  have hdescent : baseEnd_7111319 < baseStart_7111319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111356 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_7111356 : Nat := 118140960795 + 7111356 * 2 ^ 59
def prefixEnd_7111356 : Nat := 4983230072969 + 3 ^ 40 * 7111356 * 2
def baseEnd_7111356 : Nat := 3651543733234784020645475

theorem tailTrace_7111356 : CollatzResearch.WordTrace tailWord_7111356 prefixEnd_7111356 3651543733234784020645475 := by
  unfold tailWord_7111356
  simp only [CollatzResearch.WordTrace]
  refine ⟨129686230812389604878400961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172914974416519473171201281 129686230812389604878400961)
  ·
    refine ⟨97264673109292203658800721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129686230812389604878400961 97264673109292203658800721)
    ·
      refine ⟨72948504831969152744100541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97264673109292203658800721 72948504831969152744100541)
      ·
        refine ⟨27355689311988432279037703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72948504831969152744100541 27355689311988432279037703)
        ·
          refine ⟨41033533967982648418556555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27355689311988432279037703 41033533967982648418556555)
          ·
            refine ⟨61550300951973972627834833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41033533967982648418556555 61550300951973972627834833)
            ·
              refine ⟨46162725713980479470876125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61550300951973972627834833 46162725713980479470876125)
              ·
                refine ⟨17311022142742679801578547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46162725713980479470876125 17311022142742679801578547)
                ·
                  refine ⟨25966533214114019702367821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17311022142742679801578547 25966533214114019702367821)
                  ·
                    refine ⟨9737449955292757388387933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25966533214114019702367821 9737449955292757388387933)
                    ·
                      refine ⟨3651543733234784020645475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9737449955292757388387933 3651543733234784020645475)
                      ·
                        rfl

theorem cell23_7111356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_7111356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111356 prefixEnd_7111356 := by exact prefixLift 7111356
  have htrace : WordTrace (prefixWord ++ tailWord_7111356) baseStart_7111356 baseEnd_7111356 := by
    simpa [prefixWord, tailWord_7111356, baseEnd_7111356] using wordTrace_append hprefix tailTrace_7111356
  have hstable : (prefixWord ++ tailWord_7111356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111356).length < 2 ^ (prefixWord ++ tailWord_7111356).sum := by decide
  have hdescent : baseEnd_7111356 < baseStart_7111356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111406 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_7111406 : Nat := 118140960795 + 7111406 * 2 ^ 59
def prefixEnd_7111406 : Nat := 4983230072969 + 3 ^ 40 * 7111406 * 2
def baseEnd_7111406 : Nat := 1217189802422502941673415

theorem tailTrace_7111406 : CollatzResearch.WordTrace tailWord_7111406 prefixEnd_7111406 1217189802422502941673415 := by
  unfold tailWord_7111406
  simp only [CollatzResearch.WordTrace]
  refine ⟨32421785659324758537015259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172916190183065378864081381 32421785659324758537015259)
  ·
    refine ⟨48632678488987137805522889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32421785659324758537015259 48632678488987137805522889)
    ·
      refine ⟨36474508866740353354142167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48632678488987137805522889 36474508866740353354142167)
      ·
        refine ⟨54711763300110530031213251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36474508866740353354142167 54711763300110530031213251)
        ·
          refine ⟨82067644950165795046819877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54711763300110530031213251 82067644950165795046819877)
          ·
            refine ⟨15387683428156086571278727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82067644950165795046819877 15387683428156086571278727)
            ·
              refine ⟨23081525142234129856918091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15387683428156086571278727 23081525142234129856918091)
              ·
                refine ⟨34622287713351194785377137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23081525142234129856918091 34622287713351194785377137)
                ·
                  refine ⟨25966715785013396089032853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34622287713351194785377137 25966715785013396089032853)
                  ·
                    refine ⟨1217189802422502941673415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25966715785013396089032853 1217189802422502941673415)
                    ·
                      rfl

theorem cell23_7111406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_7111406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111406 prefixEnd_7111406 := by exact prefixLift 7111406
  have htrace : WordTrace (prefixWord ++ tailWord_7111406) baseStart_7111406 baseEnd_7111406 := by
    simpa [prefixWord, tailWord_7111406, baseEnd_7111406] using wordTrace_append hprefix tailTrace_7111406
  have hstable : (prefixWord ++ tailWord_7111406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111406).length < 2 ^ (prefixWord ++ tailWord_7111406).sum := by decide
  have hdescent : baseEnd_7111406 < baseStart_7111406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111459 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 7]
def baseStart_7111459 : Nat := 118140960795 + 7111459 * 2 ^ 59
def prefixEnd_7111459 : Nat := 4983230072969 + 3 ^ 40 * 7111459 * 2
def baseEnd_7111459 : Nat := 3651596621742197117657501

theorem tailTrace_7111459 : CollatzResearch.WordTrace tailWord_7111459 prefixEnd_7111459 3651596621742197117657501 := by
  unfold tailWord_7111459
  simp only [CollatzResearch.WordTrace]
  refine ⟨259376218343406058347801431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172917478895604038898534287 259376218343406058347801431)
  ·
    refine ⟨389064327515109087521702147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259376218343406058347801431 389064327515109087521702147)
    ·
      refine ⟨583596491272663631282553221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389064327515109087521702147 583596491272663631282553221)
      ·
        refine ⟨109424342113624430865478729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 583596491272663631282553221 109424342113624430865478729)
        ·
          refine ⟨82068256585218323149109047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109424342113624430865478729 82068256585218323149109047)
          ·
            refine ⟨123102384877827484723663571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82068256585218323149109047 123102384877827484723663571)
            ·
              refine ⟨184653577316741227085495357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123102384877827484723663571 184653577316741227085495357)
              ·
                refine ⟨69245091493777960157060759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184653577316741227085495357 69245091493777960157060759)
                ·
                  refine ⟨103867637240666940235591139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69245091493777960157060759 103867637240666940235591139)
                  ·
                    refine ⟨155801455861000410353386709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103867637240666940235591139 155801455861000410353386709)
                    ·
                      refine ⟨3651596621742197117657501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155801455861000410353386709 3651596621742197117657501)
                      ·
                        rfl

theorem cell23_7111459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_7111459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111459 prefixEnd_7111459 := by exact prefixLift 7111459
  have htrace : WordTrace (prefixWord ++ tailWord_7111459) baseStart_7111459 baseEnd_7111459 := by
    simpa [prefixWord, tailWord_7111459, baseEnd_7111459] using wordTrace_append hprefix tailTrace_7111459
  have hstable : (prefixWord ++ tailWord_7111459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111459).length < 2 ^ (prefixWord ++ tailWord_7111459).sum := by decide
  have hdescent : baseEnd_7111459 < baseStart_7111459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111479 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 2, 8]
def baseStart_7111479 : Nat := 118140960795 + 7111479 * 2 ^ 59
def prefixEnd_7111479 : Nat := 4983230072969 + 3 ^ 40 * 7111479 * 2
def baseEnd_7111479 : Nat := 1217202297118429013135803

theorem tailTrace_7111479 : CollatzResearch.WordTrace tailWord_7111479 prefixEnd_7111479 1217202297118429013135803 := by
  unfold tailWord_7111479
  simp only [CollatzResearch.WordTrace]
  refine ⟨259376947803333601763529491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172917965202222401175686327 259376947803333601763529491)
  ·
    refine ⟨389065421705000402645294237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259376947803333601763529491 389065421705000402645294237)
    ·
      refine ⟨145899533139375150991985339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389065421705000402645294237 145899533139375150991985339)
      ·
        refine ⟨218849299709062726487978009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145899533139375150991985339 218849299709062726487978009)
        ·
          refine ⟨164136974781797044865983507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218849299709062726487978009 164136974781797044865983507)
          ·
            refine ⟨246205462172695567298975261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164136974781797044865983507 246205462172695567298975261)
            ·
              refine ⟨92327048314760837737115723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246205462172695567298975261 92327048314760837737115723)
              ·
                refine ⟨138490572472141256605673585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92327048314760837737115723 138490572472141256605673585)
                ·
                  refine ⟨103867929354105942454255189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138490572472141256605673585 103867929354105942454255189)
                  ·
                    refine ⟨1217202297118429013135803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103867929354105942454255189 1217202297118429013135803)
                    ·
                      rfl

theorem cell23_7111479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_7111479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111479 prefixEnd_7111479 := by exact prefixLift 7111479
  have htrace : WordTrace (prefixWord ++ tailWord_7111479) baseStart_7111479 baseEnd_7111479 := by
    simpa [prefixWord, tailWord_7111479, baseEnd_7111479] using wordTrace_append hprefix tailTrace_7111479
  have hstable : (prefixWord ++ tailWord_7111479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111479).length < 2 ^ (prefixWord ++ tailWord_7111479).sum := by decide
  have hdescent : baseEnd_7111479 < baseStart_7111479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111513 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 3, 4]
def baseStart_7111513 : Nat := 118140960795 + 7111513 * 2 ^ 59
def prefixEnd_7111513 : Nat := 4983230072969 + 3 ^ 40 * 7111513 * 2
def baseEnd_7111513 : Nat := 1217208116565846635460751

theorem tailTrace_7111513 : CollatzResearch.WordTrace tailWord_7111513 prefixEnd_7111513 1217208116565846635460751 := by
  unfold tailWord_7111513
  simp only [CollatzResearch.WordTrace]
  refine ⟨259378187885210425570267193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172918791923473617046844795 259378187885210425570267193)
  ·
    refine ⟨194533640913907819177700395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259378187885210425570267193 194533640913907819177700395)
    ·
      refine ⟨291800461370861728766550593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194533640913907819177700395 291800461370861728766550593)
      ·
        refine ⟨218850346028146296574912945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291800461370861728766550593 218850346028146296574912945)
        ·
          refine ⟨164137759521109722431184709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218850346028146296574912945 164137759521109722431184709)
          ·
            refine ⟨30775829910208072955847133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164137759521109722431184709 30775829910208072955847133)
            ·
              refine ⟨11540936216328027358442675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30775829910208072955847133 11540936216328027358442675)
              ·
                refine ⟨17311404324492041037664013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11540936216328027358442675 17311404324492041037664013)
                ·
                  refine ⟨6491776621684515389124005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17311404324492041037664013 6491776621684515389124005)
                  ·
                    refine ⟨1217208116565846635460751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6491776621684515389124005 1217208116565846635460751)
                    ·
                      rfl

theorem cell23_7111513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 4].length) (baseStart_7111513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111513 prefixEnd_7111513 := by exact prefixLift 7111513
  have htrace : WordTrace (prefixWord ++ tailWord_7111513) baseStart_7111513 baseEnd_7111513 := by
    simpa [prefixWord, tailWord_7111513, baseEnd_7111513] using wordTrace_append hprefix tailTrace_7111513
  have hstable : (prefixWord ++ tailWord_7111513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111513).length < 2 ^ (prefixWord ++ tailWord_7111513).sum := by decide
  have hdescent : baseEnd_7111513 < baseStart_7111513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111536 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 3]
def baseStart_7111536 : Nat := 118140960795 + 7111536 * 2 ^ 59
def prefixEnd_7111536 : Nat := 4983230072969 + 3 ^ 40 * 7111536 * 2
def baseEnd_7111536 : Nat := 3651636159752593316394647

theorem tailTrace_7111536 : CollatzResearch.WordTrace tailWord_7111536 prefixEnd_7111536 3651636159752593316394647 := by
  unfold tailWord_7111536
  simp only [CollatzResearch.WordTrace]
  refine ⟨129689513382063550249177231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172919351176084733665569641 129689513382063550249177231)
  ·
    refine ⟨194534270073095325373765847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129689513382063550249177231 194534270073095325373765847)
    ·
      refine ⟨291801405109642988060648771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194534270073095325373765847 291801405109642988060648771)
      ·
        refine ⟨437702107664464482090973157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291801405109642988060648771 437702107664464482090973157)
        ·
          refine ⟨82069145187087090392057467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 437702107664464482090973157 82069145187087090392057467)
          ·
            refine ⟨123103717780630635588086201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82069145187087090392057467 123103717780630635588086201)
            ·
              refine ⟨92327788335472976691064651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123103717780630635588086201 92327788335472976691064651)
              ·
                refine ⟨138491682503209465036596977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92327788335472976691064651 138491682503209465036596977)
                ·
                  refine ⟨103868761877407098777447733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138491682503209465036596977 103868761877407098777447733)
                  ·
                    refine ⟨9737696426006915510385725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103868761877407098777447733 9737696426006915510385725)
                    ·
                      refine ⟨3651636159752593316394647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9737696426006915510385725 3651636159752593316394647)
                      ·
                        rfl

theorem cell23_7111536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 3].length) (baseStart_7111536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111536 prefixEnd_7111536 := by exact prefixLift 7111536
  have htrace : WordTrace (prefixWord ++ tailWord_7111536) baseStart_7111536 baseEnd_7111536 := by
    simpa [prefixWord, tailWord_7111536, baseEnd_7111536] using wordTrace_append hprefix tailTrace_7111536
  have hstable : (prefixWord ++ tailWord_7111536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111536).length < 2 ^ (prefixWord ++ tailWord_7111536).sum := by decide
  have hdescent : baseEnd_7111536 < baseStart_7111536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111593 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 4]
def baseStart_7111593 : Nat := 118140960795 + 7111593 * 2 ^ 59
def prefixEnd_7111593 : Nat := 4983230072969 + 3 ^ 40 * 7111593 * 2
def baseEnd_7111593 : Nat := 3651665428149899593381885

theorem tailTrace_7111593 : CollatzResearch.WordTrace tailWord_7111593 prefixEnd_7111593 3651665428149899593381885 := by
  unfold tailWord_7111593
  simp only [CollatzResearch.WordTrace]
  refine ⟨259381105724920599233179433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172920737149947066155452955 259381105724920599233179433)
  ·
    refine ⟨194535829293690449424884575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259381105724920599233179433 194535829293690449424884575)
    ·
      refine ⟨291803743940535674137326863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194535829293690449424884575 291803743940535674137326863)
      ·
        refine ⟨437705615910803511205990295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291803743940535674137326863 437705615910803511205990295)
        ·
          refine ⟨656558423866205266808985443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437705615910803511205990295 656558423866205266808985443)
          ·
            refine ⟨984837635799307900213478165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656558423866205266808985443 984837635799307900213478165)
            ·
              refine ⟨46164264178092557822506789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 984837635799307900213478165 46164264178092557822506789)
              ·
                refine ⟨8655799533392354591720023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46164264178092557822506789 8655799533392354591720023)
                ·
                  refine ⟨12983699300088531887580035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8655799533392354591720023 12983699300088531887580035)
                  ·
                    refine ⟨19475548950132797831370053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12983699300088531887580035 19475548950132797831370053)
                    ·
                      refine ⟨3651665428149899593381885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19475548950132797831370053 3651665428149899593381885)
                      ·
                        rfl

theorem cell23_7111593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 4].length) (baseStart_7111593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111593 prefixEnd_7111593 := by exact prefixLift 7111593
  have htrace : WordTrace (prefixWord ++ tailWord_7111593) baseStart_7111593 baseEnd_7111593 := by
    simpa [prefixWord, tailWord_7111593, baseEnd_7111593] using wordTrace_append hprefix tailTrace_7111593
  have hstable : (prefixWord ++ tailWord_7111593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111593).length < 2 ^ (prefixWord ++ tailWord_7111593).sum := by decide
  have hdescent : baseEnd_7111593 < baseStart_7111593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111596 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_7111596 : Nat := 118140960795 + 7111596 * 2 ^ 59
def prefixEnd_7111596 : Nat := 4983230072969 + 3 ^ 40 * 7111596 * 2
def baseEnd_7111596 : Nat := 3651666968591863081644371

theorem tailTrace_7111596 : CollatzResearch.WordTrace tailWord_7111596 prefixEnd_7111596 3651666968591863081644371 := by
  unfold tailWord_7111596
  simp only [CollatzResearch.WordTrace]
  refine ⟨129690607571954865372769321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172920810095939820497025761 129690607571954865372769321)
  ·
    refine ⟨97267955678966149029576991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129690607571954865372769321 97267955678966149029576991)
    ·
      refine ⟨145901933518449223544365487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97267955678966149029576991 145901933518449223544365487)
      ·
        refine ⟨218852900277673835316548231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145901933518449223544365487 218852900277673835316548231)
        ·
          refine ⟨328279350416510752974822347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218852900277673835316548231 328279350416510752974822347)
          ·
            refine ⟨492419025624766129462233521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328279350416510752974822347 492419025624766129462233521)
            ·
              refine ⟨369314269218574597096675141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492419025624766129462233521 369314269218574597096675141)
              ·
                refine ⟨69246425478482736955626589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369314269218574597096675141 69246425478482736955626589)
                ·
                  refine ⟨25967409554431026358359971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69246425478482736955626589 25967409554431026358359971)
                  ·
                    refine ⟨38951114331646539537539957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25967409554431026358359971 38951114331646539537539957)
                    ·
                      refine ⟨3651666968591863081644371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38951114331646539537539957 3651666968591863081644371)
                      ·
                        rfl

theorem cell23_7111596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_7111596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111596 prefixEnd_7111596 := by exact prefixLift 7111596
  have htrace : WordTrace (prefixWord ++ tailWord_7111596) baseStart_7111596 baseEnd_7111596 := by
    simpa [prefixWord, tailWord_7111596, baseEnd_7111596] using wordTrace_append hprefix tailTrace_7111596
  have hstable : (prefixWord ++ tailWord_7111596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111596).length < 2 ^ (prefixWord ++ tailWord_7111596).sum := by decide
  have hdescent : baseEnd_7111596 < baseStart_7111596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111610 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2]
def baseStart_7111610 : Nat := 118140960795 + 7111610 * 2 ^ 59
def prefixEnd_7111610 : Nat := 4983230072969 + 3 ^ 40 * 7111610 * 2
def baseEnd_7111610 : Nat := 3651674157321026026869307

theorem tailTrace_7111610 : CollatzResearch.WordTrace tailWord_7111610 prefixEnd_7111610 3651674157321026026869307 := by
  unfold tailWord_7111610
  simp only [CollatzResearch.WordTrace]
  refine ⟨64845431441464752784137071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172921150510572674091032189 64845431441464752784137071)
  ·
    refine ⟨97268147162197129176205607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64845431441464752784137071 97268147162197129176205607)
    ·
      refine ⟨145902220743295693764308411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97268147162197129176205607 145902220743295693764308411)
      ·
        refine ⟨218853331114943540646462617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145902220743295693764308411 218853331114943540646462617)
        ·
          refine ⟨164139998336207655484846963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218853331114943540646462617 164139998336207655484846963)
          ·
            refine ⟨246209997504311483227270445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164139998336207655484846963 246209997504311483227270445)
            ·
              refine ⟨92328749064116806210226417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246209997504311483227270445 92328749064116806210226417)
              ·
                refine ⟨69246561798087604657669813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92328749064116806210226417 69246561798087604657669813)
                ·
                  refine ⟨6491865168570712936656545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69246561798087604657669813 6491865168570712936656545)
                  ·
                    refine ⟨4868898876428034702492409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6491865168570712936656545 4868898876428034702492409)
                    ·
                      refine ⟨3651674157321026026869307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4868898876428034702492409 3651674157321026026869307)
                      ·
                        rfl

theorem cell23_7111610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2].length) (baseStart_7111610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111610 prefixEnd_7111610 := by exact prefixLift 7111610
  have htrace : WordTrace (prefixWord ++ tailWord_7111610) baseStart_7111610 baseEnd_7111610 := by
    simpa [prefixWord, tailWord_7111610, baseEnd_7111610] using wordTrace_append hprefix tailTrace_7111610
  have hstable : (prefixWord ++ tailWord_7111610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111610).length < 2 ^ (prefixWord ++ tailWord_7111610).sum := by decide
  have hdescent : baseEnd_7111610 < baseStart_7111610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111616 : List Nat := [2, 1, 1, 2, 3, 4, 10]
def baseStart_7111616 : Nat := 118140960795 + 7111616 * 2 ^ 59
def prefixEnd_7111616 : Nat := 4983230072969 + 3 ^ 40 * 7111616 * 2
def baseEnd_7111616 : Nat := 45082435039567321029559

theorem tailTrace_7111616 : CollatzResearch.WordTrace tailWord_7111616 prefixEnd_7111616 45082435039567321029559 := by
  unfold tailWord_7111616
  simp only [CollatzResearch.WordTrace]
  refine ⟨129690972301918637080633351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172921296402558182774177801 129690972301918637080633351)
  ·
    refine ⟨194536458452877955620950027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129690972301918637080633351 194536458452877955620950027)
    ·
      refine ⟨291804687679316933431425041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194536458452877955620950027 291804687679316933431425041)
      ·
        refine ⟨218853515759487700073568781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291804687679316933431425041 218853515759487700073568781)
        ·
          refine ⟨82070068409807887527588293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218853515759487700073568781 82070068409807887527588293)
          ·
            refine ⟨15388137826838978911422805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82070068409807887527588293 15388137826838978911422805)
            ·
              refine ⟨45082435039567321029559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15388137826838978911422805 45082435039567321029559)
              ·
                rfl

theorem cell23_7111616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 10].length) (baseStart_7111616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111616 prefixEnd_7111616 := by exact prefixLift 7111616
  have htrace : WordTrace (prefixWord ++ tailWord_7111616) baseStart_7111616 baseEnd_7111616 := by
    simpa [prefixWord, tailWord_7111616, baseEnd_7111616] using wordTrace_append hprefix tailTrace_7111616
  have hstable : (prefixWord ++ tailWord_7111616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111616).length < 2 ^ (prefixWord ++ tailWord_7111616).sum := by decide
  have hdescent : baseEnd_7111616 < baseStart_7111616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111626 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_7111626 : Nat := 118140960795 + 7111626 * 2 ^ 59
def prefixEnd_7111626 : Nat := 4983230072969 + 3 ^ 40 * 7111626 * 2
def baseEnd_7111626 : Nat := 3651682373011497964269233

theorem tailTrace_7111626 : CollatzResearch.WordTrace tailWord_7111626 prefixEnd_7111626 3651682373011497964269233 := by
  unfold tailWord_7111626
  simp only [CollatzResearch.WordTrace]
  refine ⟨64845577333450261467282683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172921539555867363912753821 64845577333450261467282683)
  ·
    refine ⟨97268366000175392200924025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64845577333450261467282683 97268366000175392200924025)
    ·
      refine ⟨72951274500131544150693019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97268366000175392200924025 72951274500131544150693019)
      ·
        refine ⟨109426911750197316226039529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72951274500131544150693019 109426911750197316226039529)
        ·
          refine ⟨82070183812647987169529647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109426911750197316226039529 82070183812647987169529647)
          ·
            refine ⟨123105275718971980754294471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82070183812647987169529647 123105275718971980754294471)
            ·
              refine ⟨184657913578457971131441707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123105275718971980754294471 184657913578457971131441707)
              ·
                refine ⟨276986870367686956697162561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184657913578457971131441707 276986870367686956697162561)
                ·
                  refine ⟨207740152775765217522871921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276986870367686956697162561 207740152775765217522871921)
                  ·
                    refine ⟨155805114581823913142153941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 207740152775765217522871921 155805114581823913142153941)
                    ·
                      refine ⟨3651682373011497964269233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155805114581823913142153941 3651682373011497964269233)
                      ·
                        rfl

theorem cell23_7111626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_7111626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111626 prefixEnd_7111626 := by exact prefixLift 7111626
  have htrace : WordTrace (prefixWord ++ tailWord_7111626) baseStart_7111626 baseEnd_7111626 := by
    simpa [prefixWord, tailWord_7111626, baseEnd_7111626] using wordTrace_append hprefix tailTrace_7111626
  have hstable : (prefixWord ++ tailWord_7111626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111626).length < 2 ^ (prefixWord ++ tailWord_7111626).sum := by decide
  have hdescent : baseEnd_7111626 < baseStart_7111626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111627 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 3, 2, 2]
def baseStart_7111627 : Nat := 118140960795 + 7111627 * 2 ^ 59
def prefixEnd_7111627 : Nat := 4983230072969 + 3 ^ 40 * 7111627 * 2
def baseEnd_7111627 : Nat := 3651682886492152460356729

theorem tailTrace_7111627 : CollatzResearch.WordTrace tailWord_7111627 prefixEnd_7111627 3651682886492152460356729 := by
  unfold tailWord_7111627
  simp only [CollatzResearch.WordTrace]
  refine ⟨259382345806797423039917135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172921563871198282026611423 259382345806797423039917135)
  ·
    refine ⟨389073518710196134559875703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259382345806797423039917135 389073518710196134559875703)
    ·
      refine ⟨583610278065294201839813555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389073518710196134559875703 583610278065294201839813555)
      ·
        refine ⟨875415417097941302759720333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583610278065294201839813555 875415417097941302759720333)
        ·
          refine ⟨328280781411727988534895125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 875415417097941302759720333 328280781411727988534895125)
          ·
            refine ⟨15388161628674749462573209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 328280781411727988534895125 15388161628674749462573209)
            ·
              refine ⟨11541121221506062096929907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15388161628674749462573209 11541121221506062096929907)
              ·
                refine ⟨17311681832259093145394861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11541121221506062096929907 17311681832259093145394861)
                ·
                  refine ⟨6491880687097159929523073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17311681832259093145394861 6491880687097159929523073)
                  ·
                    refine ⟨4868910515322869947142305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6491880687097159929523073 4868910515322869947142305)
                    ·
                      refine ⟨3651682886492152460356729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4868910515322869947142305 3651682886492152460356729)
                      ·
                        rfl

theorem cell23_7111627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 2, 2].length) (baseStart_7111627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111627 prefixEnd_7111627 := by exact prefixLift 7111627
  have htrace : WordTrace (prefixWord ++ tailWord_7111627) baseStart_7111627 baseEnd_7111627 := by
    simpa [prefixWord, tailWord_7111627, baseEnd_7111627] using wordTrace_append hprefix tailTrace_7111627
  have hstable : (prefixWord ++ tailWord_7111627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111627).length < 2 ^ (prefixWord ++ tailWord_7111627).sum := by decide
  have hdescent : baseEnd_7111627 < baseStart_7111627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111637 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 1, 6]
def baseStart_7111637 : Nat := 118140960795 + 7111637 * 2 ^ 59
def prefixEnd_7111637 : Nat := 4983230072969 + 3 ^ 40 * 7111637 * 2
def baseEnd_7111637 : Nat := 1217229340432899140410561

theorem tailTrace_7111637 : CollatzResearch.WordTrace tailWord_7111637 prefixEnd_7111637 1217229340432899140410561 := by
  unfold tailWord_7111637
  simp only [CollatzResearch.WordTrace]
  refine ⟨259382710536761194747781165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172921807024507463165187443 259382710536761194747781165)
  ·
    refine ⟨97268516451285448030417937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259382710536761194747781165 97268516451285448030417937)
    ·
      refine ⟨72951387338464086022813453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97268516451285448030417937 72951387338464086022813453)
      ·
        refine ⟨27356770251924032258555045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72951387338464086022813453 27356770251924032258555045)
        ·
          refine ⟨5129394422235756048479071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27356770251924032258555045 5129394422235756048479071)
          ·
            refine ⟨7694091633353634072718607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129394422235756048479071 7694091633353634072718607)
            ·
              refine ⟨11541137450030451109077911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694091633353634072718607 11541137450030451109077911)
              ·
                refine ⟨17311706175045676663616867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11541137450030451109077911 17311706175045676663616867)
                ·
                  refine ⟨25967559262568514995425301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17311706175045676663616867 25967559262568514995425301)
                  ·
                    refine ⟨1217229340432899140410561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25967559262568514995425301 1217229340432899140410561)
                    ·
                      rfl

theorem cell23_7111637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_7111637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111637 prefixEnd_7111637 := by exact prefixLift 7111637
  have htrace : WordTrace (prefixWord ++ tailWord_7111637) baseStart_7111637 baseEnd_7111637 := by
    simpa [prefixWord, tailWord_7111637, baseEnd_7111637] using wordTrace_append hprefix tailTrace_7111637
  have hstable : (prefixWord ++ tailWord_7111637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111637).length < 2 ^ (prefixWord ++ tailWord_7111637).sum := by decide
  have hdescent : baseEnd_7111637 < baseStart_7111637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111640 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 1, 2, 4]
def baseStart_7111640 : Nat := 118140960795 + 7111640 * 2 ^ 59
def prefixEnd_7111640 : Nat := 4983230072969 + 3 ^ 40 * 7111640 * 2
def baseEnd_7111640 : Nat := 3651689561740660909494169

theorem tailTrace_7111640 : CollatzResearch.WordTrace tailWord_7111640 prefixEnd_7111640 3651689561740660909494169 := by
  unfold tailWord_7111640
  simp only [CollatzResearch.WordTrace]
  refine ⟨129691409977875163130070187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172921879970500217506760249 129691409977875163130070187)
  ·
    refine ⟨194537114966812744695105281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129691409977875163130070187 194537114966812744695105281)
    ·
      refine ⟨145902836225109558521328961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194537114966812744695105281 145902836225109558521328961)
      ·
        refine ⟨109427127168832168890996721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145902836225109558521328961 109427127168832168890996721)
        ·
          refine ⟨82070345376624126668247541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109427127168832168890996721 82070345376624126668247541)
          ·
            refine ⟨7694094879058511875148207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82070345376624126668247541 7694094879058511875148207)
            ·
              refine ⟨11541142318587767812722311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694094879058511875148207 11541142318587767812722311)
              ·
                refine ⟨17311713477881651719083467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11541142318587767812722311 17311713477881651719083467)
                ·
                  refine ⟨25967570216822477578625201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17311713477881651719083467 25967570216822477578625201)
                  ·
                    refine ⟨19475677662616858183968901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25967570216822477578625201 19475677662616858183968901)
                    ·
                      refine ⟨3651689561740660909494169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19475677662616858183968901 3651689561740660909494169)
                      ·
                        rfl

theorem cell23_7111640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_7111640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111640 prefixEnd_7111640 := by exact prefixLift 7111640
  have htrace : WordTrace (prefixWord ++ tailWord_7111640) baseStart_7111640 baseEnd_7111640 := by
    simpa [prefixWord, tailWord_7111640, baseEnd_7111640] using wordTrace_append hprefix tailTrace_7111640
  have hstable : (prefixWord ++ tailWord_7111640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111640).length < 2 ^ (prefixWord ++ tailWord_7111640).sum := by decide
  have hdescent : baseEnd_7111640 < baseStart_7111640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111647 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 1, 2, 3]
def baseStart_7111647 : Nat := 118140960795 + 7111647 * 2 ^ 59
def prefixEnd_7111647 : Nat := 4983230072969 + 3 ^ 40 * 7111647 * 2
def baseEnd_7111647 : Nat := 3651693156105242382106637

theorem tailTrace_7111647 : CollatzResearch.WordTrace tailWord_7111647 prefixEnd_7111647 3651693156105242382106637 := by
  unfold tailWord_7111647
  simp only [CollatzResearch.WordTrace]
  refine ⟨259383075266724966455645195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172922050177816644303763463 259383075266724966455645195)
  ·
    refine ⟨389074612900087449683467793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259383075266724966455645195 389074612900087449683467793)
    ·
      refine ⟨291805959675065587262600845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389074612900087449683467793 291805959675065587262600845)
      ·
        refine ⟨109427234878149595223475317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291805959675065587262600845 109427234878149595223475317)
        ·
          refine ⟨10258803269826524552200811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109427234878149595223475317 10258803269826524552200811)
          ·
            refine ⟨15388204904739786828301217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10258803269826524552200811 15388204904739786828301217)
            ·
              refine ⟨11541153678554840121225913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15388204904739786828301217 11541153678554840121225913)
              ·
                refine ⟨8655865258916130090919435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11541153678554840121225913 8655865258916130090919435)
                ·
                  refine ⟨12983797888374195136379153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8655865258916130090919435 12983797888374195136379153)
                  ·
                    refine ⟨9737848416280646352284365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12983797888374195136379153 9737848416280646352284365)
                    ·
                      refine ⟨3651693156105242382106637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9737848416280646352284365 3651693156105242382106637)
                      ·
                        rfl

theorem cell23_7111647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_7111647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111647 prefixEnd_7111647 := by exact prefixLift 7111647
  have htrace : WordTrace (prefixWord ++ tailWord_7111647) baseStart_7111647 baseEnd_7111647 := by
    simpa [prefixWord, tailWord_7111647, baseEnd_7111647] using wordTrace_append hprefix tailTrace_7111647
  have hstable : (prefixWord ++ tailWord_7111647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111647).length < 2 ^ (prefixWord ++ tailWord_7111647).sum := by decide
  have hdescent : baseEnd_7111647 < baseStart_7111647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111650 : List Nat := [3, 3, 3, 1, 1, 2, 1, 9]
def baseStart_7111650 : Nat := 118140960795 + 7111650 * 2 ^ 59
def prefixEnd_7111650 : Nat := 4983230072969 + 3 ^ 40 * 7111650 * 2
def baseEnd_7111650 : Nat := 135247951723970587791449

theorem tailTrace_7111650 : CollatzResearch.WordTrace tailWord_7111650 prefixEnd_7111650 135247951723970587791449 := by
  unfold tailWord_7111650
  simp only [CollatzResearch.WordTrace]
  refine ⟨64845796171428524492001101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172922123123809398645336269 64845796171428524492001101)
  ·
    refine ⟨24317173564285696684500413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64845796171428524492001101 24317173564285696684500413)
    ·
      refine ⟨9118940086607136256687655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24317173564285696684500413 9118940086607136256687655)
      ·
        refine ⟨13678410129910704385031483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9118940086607136256687655 13678410129910704385031483)
        ·
          refine ⟨20517615194866056577547225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13678410129910704385031483 20517615194866056577547225)
          ·
            refine ⟨15388211396149542433160419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20517615194866056577547225 15388211396149542433160419)
            ·
              refine ⟨23082317094224313649740629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15388211396149542433160419 23082317094224313649740629)
              ·
                refine ⟨135247951723970587791449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23082317094224313649740629 135247951723970587791449)
                ·
                  rfl

theorem cell23_7111650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 9].length) (baseStart_7111650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111650 prefixEnd_7111650 := by exact prefixLift 7111650
  have htrace : WordTrace (prefixWord ++ tailWord_7111650) baseStart_7111650 baseEnd_7111650 := by
    simpa [prefixWord, tailWord_7111650, baseEnd_7111650] using wordTrace_append hprefix tailTrace_7111650
  have hstable : (prefixWord ++ tailWord_7111650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111650).length < 2 ^ (prefixWord ++ tailWord_7111650).sum := by decide
  have hdescent : baseEnd_7111650 < baseStart_7111650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111678 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_7111678 : Nat := 118140960795 + 7111678 * 2 ^ 59
def prefixEnd_7111678 : Nat := 4983230072969 + 3 ^ 40 * 7111678 * 2
def baseEnd_7111678 : Nat := 3651709074005531760818995

theorem tailTrace_7111678 : CollatzResearch.WordTrace tailWord_7111678 prefixEnd_7111678 3651709074005531760818995 := by
  unfold tailWord_7111678
  simp only [CollatzResearch.WordTrace]
  refine ⟨32423025741201582343752961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172922803953075105833349125 32423025741201582343752961)
  ·
    refine ⟨24317269305901186757814721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32423025741201582343752961 24317269305901186757814721)
    ·
      refine ⟨18237951979425890068361041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24317269305901186757814721 18237951979425890068361041)
      ·
        refine ⟨13678463984569417551270781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18237951979425890068361041 13678463984569417551270781)
        ·
          refine ⟨5129423994213531581726543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13678463984569417551270781 5129423994213531581726543)
          ·
            refine ⟨7694135991320297372589815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129423994213531581726543 7694135991320297372589815)
            ·
              refine ⟨11541203986980446058884723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694135991320297372589815 11541203986980446058884723)
              ·
                refine ⟨17311805980470669088327085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11541203986980446058884723 17311805980470669088327085)
                ·
                  refine ⟨6491927242676500908122657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17311805980470669088327085 6491927242676500908122657)
                  ·
                    refine ⟨4868945432007375681091993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6491927242676500908122657 4868945432007375681091993)
                    ·
                      refine ⟨3651709074005531760818995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4868945432007375681091993 3651709074005531760818995)
                      ·
                        rfl

theorem cell23_7111678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_7111678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111678 prefixEnd_7111678 := by exact prefixLift 7111678
  have htrace : WordTrace (prefixWord ++ tailWord_7111678) baseStart_7111678 baseEnd_7111678 := by
    simpa [prefixWord, tailWord_7111678, baseEnd_7111678] using wordTrace_append hprefix tailTrace_7111678
  have hstable : (prefixWord ++ tailWord_7111678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111678).length < 2 ^ (prefixWord ++ tailWord_7111678).sum := by decide
  have hdescent : baseEnd_7111678 < baseStart_7111678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111694 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3]
def baseStart_7111694 : Nat := 118140960795 + 7111694 * 2 ^ 59
def prefixEnd_7111694 : Nat := 4983230072969 + 3 ^ 40 * 7111694 * 2
def baseEnd_7111694 : Nat := 3651717289696003698218921

theorem tailTrace_7111694 : CollatzResearch.WordTrace tailWord_7111694 prefixEnd_7111694 3651717289696003698218921 := by
  unfold tailWord_7111694
  simp only [CollatzResearch.WordTrace]
  refine ⟨32423098687194336685325767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172923192998369795655070757 32423098687194336685325767)
  ·
    refine ⟨48634648030791505027988651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32423098687194336685325767 48634648030791505027988651)
    ·
      refine ⟨72951972046187257541982977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48634648030791505027988651 72951972046187257541982977)
      ·
        refine ⟨54713979034640443156487233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72951972046187257541982977 54713979034640443156487233)
        ·
          refine ⟨41035484275980332367365425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54713979034640443156487233 41035484275980332367365425)
          ·
            refine ⟨30776613206985249275524069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41035484275980332367365425 30776613206985249275524069)
            ·
              refine ⟨5770614976309734239160763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30776613206985249275524069 5770614976309734239160763)
              ·
                refine ⟨8655922464464601358741145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5770614976309734239160763 8655922464464601358741145)
                ·
                  refine ⟨6491941848348451019055859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8655922464464601358741145 6491941848348451019055859)
                  ·
                    refine ⟨9737912772522676528583789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6491941848348451019055859 9737912772522676528583789)
                    ·
                      refine ⟨3651717289696003698218921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9737912772522676528583789 3651717289696003698218921)
                      ·
                        rfl

theorem cell23_7111694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_7111694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111694 prefixEnd_7111694 := by exact prefixLift 7111694
  have htrace : WordTrace (prefixWord ++ tailWord_7111694) baseStart_7111694 baseEnd_7111694 := by
    simpa [prefixWord, tailWord_7111694, baseEnd_7111694] using wordTrace_append hprefix tailTrace_7111694
  have hstable : (prefixWord ++ tailWord_7111694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111694).length < 2 ^ (prefixWord ++ tailWord_7111694).sum := by decide
  have hdescent : baseEnd_7111694 < baseStart_7111694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111698 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7111698 : Nat := 118140960795 + 7111698 * 2 ^ 59
def prefixEnd_7111698 : Nat := 4983230072969 + 3 ^ 40 * 7111698 * 2
def baseEnd_7111698 : Nat := 3651719343618621682568903

theorem tailTrace_7111698 : CollatzResearch.WordTrace tailWord_7111698 prefixEnd_7111698 3651719343618621682568903 := by
  unfold tailWord_7111698
  simp only [CollatzResearch.WordTrace]
  refine ⟨64846233847385050541437937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172923290259693468110501165 64846233847385050541437937)
  ·
    refine ⟨48634675385538787906078453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64846233847385050541437937 48634675385538787906078453)
    ·
      refine ⟨4559500817394261366194855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48634675385538787906078453 4559500817394261366194855)
      ·
        refine ⟨6839251226091392049292283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4559500817394261366194855 6839251226091392049292283)
        ·
          refine ⟨10258876839137088073938425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6839251226091392049292283 10258876839137088073938425)
          ·
            refine ⟨7694157629352816055453819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10258876839137088073938425 7694157629352816055453819)
            ·
              refine ⟨11541236444029224083180729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694157629352816055453819 11541236444029224083180729)
              ·
                refine ⟨8655927333021918062385547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11541236444029224083180729 8655927333021918062385547)
                ·
                  refine ⟨12983890999532877093578321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8655927333021918062385547 12983890999532877093578321)
                  ·
                    refine ⟨9737918249649657820183741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12983890999532877093578321 9737918249649657820183741)
                    ·
                      refine ⟨3651719343618621682568903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9737918249649657820183741 3651719343618621682568903)
                      ·
                        rfl

theorem cell23_7111698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7111698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111698 prefixEnd_7111698 := by exact prefixLift 7111698
  have htrace : WordTrace (prefixWord ++ tailWord_7111698) baseStart_7111698 baseEnd_7111698 := by
    simpa [prefixWord, tailWord_7111698, baseEnd_7111698] using wordTrace_append hprefix tailTrace_7111698
  have hstable : (prefixWord ++ tailWord_7111698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111698).length < 2 ^ (prefixWord ++ tailWord_7111698).sum := by decide
  have hdescent : baseEnd_7111698 < baseStart_7111698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111704 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 1, 3, 2]
def baseStart_7111704 : Nat := 118140960795 + 7111704 * 2 ^ 59
def prefixEnd_7111704 : Nat := 4983230072969 + 3 ^ 40 * 7111704 * 2
def baseEnd_7111704 : Nat := 3651722424502548659093875

theorem tailTrace_7111704 : CollatzResearch.WordTrace tailWord_7111704 prefixEnd_7111704 3651722424502548659093875 := by
  unfold tailWord_7111704
  simp only [CollatzResearch.WordTrace]
  refine ⟨129692577113759232595235083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172923436151678976793646777 129692577113759232595235083)
  ·
    refine ⟨194538865670638848892852625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129692577113759232595235083 194538865670638848892852625)
    ·
      refine ⟨145904149252979136669639469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194538865670638848892852625 145904149252979136669639469)
      ·
        refine ⟨54714055969867176251114801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145904149252979136669639469 54714055969867176251114801)
        ·
          refine ⟨41035541977400382188336101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54714055969867176251114801 41035541977400382188336101)
          ·
            refine ⟨7694164120762571660313019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41035541977400382188336101 7694164120762571660313019)
            ·
              refine ⟨11541246181143857490469529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694164120762571660313019 11541246181143857490469529)
              ·
                refine ⟨8655934635857893117852147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11541246181143857490469529 8655934635857893117852147)
                ·
                  refine ⟨12983901953786839676778221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8655934635857893117852147 12983901953786839676778221)
                  ·
                    refine ⟨4868963232670064878791833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12983901953786839676778221 4868963232670064878791833)
                    ·
                      refine ⟨3651722424502548659093875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4868963232670064878791833 3651722424502548659093875)
                      ·
                        rfl

theorem cell23_7111704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_7111704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111704 prefixEnd_7111704 := by exact prefixLift 7111704
  have htrace : WordTrace (prefixWord ++ tailWord_7111704) baseStart_7111704 baseEnd_7111704 := by
    simpa [prefixWord, tailWord_7111704, baseEnd_7111704] using wordTrace_append hprefix tailTrace_7111704
  have hstable : (prefixWord ++ tailWord_7111704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111704).length < 2 ^ (prefixWord ++ tailWord_7111704).sum := by decide
  have hdescent : baseEnd_7111704 < baseStart_7111704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111800 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 3, 4]
def baseStart_7111800 : Nat := 118140960795 + 7111800 * 2 ^ 59
def prefixEnd_7111800 : Nat := 4983230072969 + 3 ^ 40 * 7111800 * 2
def baseEnd_7111800 : Nat := 1217257239548460094497811

theorem tailTrace_7111800 : CollatzResearch.WordTrace tailWord_7111800 prefixEnd_7111800 1217257239548460094497811 := by
  unfold tailWord_7111800
  simp only [CollatzResearch.WordTrace]
  refine ⟨129694327817585336792982427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172925770423447115723976569 129694327817585336792982427)
  ·
    refine ⟨194541491726378005189473641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129694327817585336792982427 194541491726378005189473641)
    ·
      refine ⟨145906118794783503892105231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194541491726378005189473641 145906118794783503892105231)
      ·
        refine ⟨218859178192175255838157847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145906118794783503892105231 218859178192175255838157847)
        ·
          refine ⟨328288767288262883757236771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218859178192175255838157847 328288767288262883757236771)
          ·
            refine ⟨492433150932394325635855157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328288767288262883757236771 492433150932394325635855157)
            ·
              refine ⟨46165607899911968028361421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 492433150932394325635855157 46165607899911968028361421)
              ·
                refine ⟨17312102962466988010635533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46165607899911968028361421 17312102962466988010635533)
                ·
                  refine ⟨6492038610925120503988325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17312102962466988010635533 6492038610925120503988325)
                  ·
                    refine ⟨1217257239548460094497811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6492038610925120503988325 1217257239548460094497811)
                    ·
                      rfl

theorem cell23_7111800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_7111800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111800 prefixEnd_7111800 := by exact prefixLift 7111800
  have htrace : WordTrace (prefixWord ++ tailWord_7111800) baseStart_7111800 baseEnd_7111800 := by
    simpa [prefixWord, tailWord_7111800, baseEnd_7111800] using wordTrace_append hprefix tailTrace_7111800
  have hstable : (prefixWord ++ tailWord_7111800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111800).length < 2 ^ (prefixWord ++ tailWord_7111800).sum := by decide
  have hdescent : baseEnd_7111800 < baseStart_7111800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111934 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_7111934 : Nat := 118140960795 + 7111934 * 2 ^ 59
def prefixEnd_7111934 : Nat := 4983230072969 + 3 ^ 40 * 7111934 * 2
def baseEnd_7111934 : Nat := 3651840525053082759217817

theorem tailTrace_7111934 : CollatzResearch.WordTrace tailWord_7111934 prefixEnd_7111934 3651840525053082759217817 := by
  unfold tailWord_7111934
  simp only [CollatzResearch.WordTrace]
  refine ⟨32424192877085651808917857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172929028677790142980895237 32424192877085651808917857)
  ·
    refine ⟨24318144657814238856688393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32424192877085651808917857 24318144657814238856688393)
    ·
      refine ⟨18238608493360679142516295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24318144657814238856688393 18238608493360679142516295)
      ·
        refine ⟨27357912740041018713774443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18238608493360679142516295 27357912740041018713774443)
        ·
          refine ⟨41036869110061528070661665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27357912740041018713774443 41036869110061528070661665)
          ·
            refine ⟨30777651832546146052996249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41036869110061528070661665 30777651832546146052996249)
            ·
              refine ⟨23083238874409609539747187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30777651832546146052996249 23083238874409609539747187)
              ·
                refine ⟨34624858311614414309620781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23083238874409609539747187 34624858311614414309620781)
                ·
                  refine ⟨12984321866855405366107793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34624858311614414309620781 12984321866855405366107793)
                  ·
                    refine ⟨9738241400141554024580845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12984321866855405366107793 9738241400141554024580845)
                    ·
                      refine ⟨3651840525053082759217817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738241400141554024580845 3651840525053082759217817)
                      ·
                        rfl

theorem cell23_7111934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_7111934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111934 prefixEnd_7111934 := by exact prefixLift 7111934
  have htrace : WordTrace (prefixWord ++ tailWord_7111934) baseStart_7111934 baseEnd_7111934 := by
    simpa [prefixWord, tailWord_7111934, baseEnd_7111934] using wordTrace_append hprefix tailTrace_7111934
  have hstable : (prefixWord ++ tailWord_7111934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111934).length < 2 ^ (prefixWord ++ tailWord_7111934).sum := by decide
  have hdescent : baseEnd_7111934 < baseStart_7111934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111937 : List Nat := [1, 2, 4, 1, 1, 4, 3, 7]
def baseStart_7111937 : Nat := 118140960795 + 7111937 * 2 ^ 59
def prefixEnd_7111937 : Nat := 4983230072969 + 3 ^ 40 * 7111937 * 2
def baseEnd_7111937 : Nat := 135253409833149861017789

theorem tailTrace_7111937 : CollatzResearch.WordTrace tailWord_7111937 prefixEnd_7111937 135253409833149861017789 := by
  unfold tailWord_7111937
  simp only [CollatzResearch.WordTrace]
  refine ⟨259393652435674345983702065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172929101623782897322468043 259393652435674345983702065)
  ·
    refine ⟨194545239326755759487776549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259393652435674345983702065 194545239326755759487776549)
    ·
      refine ⟨36477232373766704903958103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194545239326755759487776549 36477232373766704903958103)
      ·
        refine ⟨54715848560650057355937155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36477232373766704903958103 54715848560650057355937155)
        ·
          refine ⟨82073772840975086033905733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54715848560650057355937155 82073772840975086033905733)
          ·
            refine ⟨15388832407682828631357325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82073772840975086033905733 15388832407682828631357325)
            ·
              refine ⟨5770812152881060736758997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15388832407682828631357325 5770812152881060736758997)
              ·
                refine ⟨135253409833149861017789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5770812152881060736758997 135253409833149861017789)
                ·
                  rfl

theorem cell23_7111937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 7].length) (baseStart_7111937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111937 prefixEnd_7111937 := by exact prefixLift 7111937
  have htrace : WordTrace (prefixWord ++ tailWord_7111937) baseStart_7111937 baseEnd_7111937 := by
    simpa [prefixWord, tailWord_7111937, baseEnd_7111937] using wordTrace_append hprefix tailTrace_7111937
  have hstable : (prefixWord ++ tailWord_7111937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111937).length < 2 ^ (prefixWord ++ tailWord_7111937).sum := by decide
  have hdescent : baseEnd_7111937 < baseStart_7111937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111947 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 3]
def baseStart_7111947 : Nat := 118140960795 + 7111947 * 2 ^ 59
def prefixEnd_7111947 : Nat := 4983230072969 + 3 ^ 40 * 7111947 * 2
def baseEnd_7111947 : Nat := 3651847200301591208355257

theorem tailTrace_7111947 : CollatzResearch.WordTrace tailWord_7111947 prefixEnd_7111947 3651847200301591208355257 := by
  unfold tailWord_7111947
  simp only [CollatzResearch.WordTrace]
  refine ⟨259394017165638117691566095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172929344777092078461044063 259394017165638117691566095)
  ·
    refine ⟨389091025748457176537349143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259394017165638117691566095 389091025748457176537349143)
    ·
      refine ⟨583636538622685764806023715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389091025748457176537349143 583636538622685764806023715)
      ·
        refine ⟨875454807934028647209035573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583636538622685764806023715 875454807934028647209035573)
        ·
          refine ⟨82073888243815185675847085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 875454807934028647209035573 82073888243815185675847085)
          ·
            refine ⟨30777708091430694628442657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82073888243815185675847085 30777708091430694628442657)
            ·
              refine ⟨23083281068573020971331993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30777708091430694628442657 23083281068573020971331993)
              ·
                refine ⟨17312460801429765728498995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23083281068573020971331993 17312460801429765728498995)
                ·
                  refine ⟨25968691202144648592748493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17312460801429765728498995 25968691202144648592748493)
                  ·
                    refine ⟨9738259200804243222280685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25968691202144648592748493 9738259200804243222280685)
                    ·
                      refine ⟨3651847200301591208355257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738259200804243222280685 3651847200301591208355257)
                      ·
                        rfl

theorem cell23_7111947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 3].length) (baseStart_7111947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111947 prefixEnd_7111947 := by exact prefixLift 7111947
  have htrace : WordTrace (prefixWord ++ tailWord_7111947) baseStart_7111947 baseEnd_7111947 := by
    simpa [prefixWord, tailWord_7111947, baseEnd_7111947] using wordTrace_append hprefix tailTrace_7111947
  have hstable : (prefixWord ++ tailWord_7111947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111947).length < 2 ^ (prefixWord ++ tailWord_7111947).sum := by decide
  have hdescent : baseEnd_7111947 < baseStart_7111947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111948 : List Nat := [2, 2, 1, 2, 2, 4, 2, 3, 1, 2, 2]
def baseStart_7111948 : Nat := 118140960795 + 7111948 * 2 ^ 59
def prefixEnd_7111948 : Nat := 4983230072969 + 3 ^ 40 * 7111948 * 2
def baseEnd_7111948 : Nat := 3651847713782245704442753

theorem tailTrace_7111948 : CollatzResearch.WordTrace tailWord_7111948 prefixEnd_7111948 3651847713782245704442753 := by
  unfold tailWord_7111948
  simp only [CollatzResearch.WordTrace]
  refine ⟨129697026819317247431176249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172929369092422996574901665 129697026819317247431176249)
  ·
    refine ⟨97272770114487935573382187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129697026819317247431176249 97272770114487935573382187)
    ·
      refine ⟨145909155171731903360073281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97272770114487935573382187 145909155171731903360073281)
      ·
        refine ⟨109431866378798927520054961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145909155171731903360073281 109431866378798927520054961)
        ·
          refine ⟨82073899784099195640041221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109431866378798927520054961 82073899784099195640041221)
          ·
            refine ⟨15388856209518599182507729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82073899784099195640041221 15388856209518599182507729)
            ·
              refine ⟨11541642157138949386880797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15388856209518599182507729 11541642157138949386880797)
              ·
                refine ⟨4328115808927106020080299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11541642157138949386880797 4328115808927106020080299)
                ·
                  refine ⟨6492173713390659030120449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4328115808927106020080299 6492173713390659030120449)
                  ·
                    refine ⟨4869130285042994272590337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6492173713390659030120449 4869130285042994272590337)
                    ·
                      refine ⟨3651847713782245704442753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4869130285042994272590337 3651847713782245704442753)
                      ·
                        rfl

theorem cell23_7111948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_7111948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111948 prefixEnd_7111948 := by exact prefixLift 7111948
  have htrace : WordTrace (prefixWord ++ tailWord_7111948) baseStart_7111948 baseEnd_7111948 := by
    simpa [prefixWord, tailWord_7111948, baseEnd_7111948] using wordTrace_append hprefix tailTrace_7111948
  have hstable : (prefixWord ++ tailWord_7111948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111948).length < 2 ^ (prefixWord ++ tailWord_7111948).sum := by decide
  have hdescent : baseEnd_7111948 < baseStart_7111948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111954 : List Nat := [3, 2, 4, 2, 1, 1, 10]
def baseStart_7111954 : Nat := 118140960795 + 7111954 * 2 ^ 59
def prefixEnd_7111954 : Nat := 4983230072969 + 3 ^ 40 * 7111954 * 2
def baseEnd_7111954 : Nat := 45084577711928057789725

theorem tailTrace_7111954 : CollatzResearch.WordTrace tailWord_7111954 prefixEnd_7111954 45084577711928057789725 := by
  unfold tailWord_7111954
  simp only [CollatzResearch.WordTrace]
  refine ⟨64848568119153189471767729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172929514984408505258047277 64848568119153189471767729)
  ·
    refine ⟨48636426089364892103825797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64848568119153189471767729 48636426089364892103825797)
    ·
      refine ⟨9119329891755917269467337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48636426089364892103825797 9119329891755917269467337)
      ·
        refine ⟨6839497418816937952100503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9119329891755917269467337 6839497418816937952100503)
        ·
          refine ⟨10259246128225406928150755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6839497418816937952100503 10259246128225406928150755)
          ·
            refine ⟨15388869192338110392226133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10259246128225406928150755 15388869192338110392226133)
            ·
              refine ⟨45084577711928057789725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15388869192338110392226133 45084577711928057789725)
              ·
                rfl

theorem cell23_7111954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 10].length) (baseStart_7111954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111954 prefixEnd_7111954 := by exact prefixLift 7111954
  have htrace : WordTrace (prefixWord ++ tailWord_7111954) baseStart_7111954 baseEnd_7111954 := by
    simpa [prefixWord, tailWord_7111954, baseEnd_7111954] using wordTrace_append hprefix tailTrace_7111954
  have hstable : (prefixWord ++ tailWord_7111954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111954).length < 2 ^ (prefixWord ++ tailWord_7111954).sum := by decide
  have hdescent : baseEnd_7111954 < baseStart_7111954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7111981 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_7111981 : Nat := 118140960795 + 7111981 * 2 ^ 59
def prefixEnd_7111981 : Nat := 4983230072969 + 3 ^ 40 * 7111981 * 2
def baseEnd_7111981 : Nat := 3651864658643844075330101

theorem tailTrace_7111981 : CollatzResearch.WordTrace tailWord_7111981 prefixEnd_7111981 3651864658643844075330101 := by
  unfold tailWord_7111981
  simp only [CollatzResearch.WordTrace]
  refine ⟨259395257247514941498303797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172930171498343294332202531 259395257247514941498303797)
  ·
    refine ⟨24318305366954525765465981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259395257247514941498303797 24318305366954525765465981)
    ·
      refine ⟨9119364512607947162049743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24318305366954525765465981 9119364512607947162049743)
      ·
        refine ⟨13679046768911920743074615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9119364512607947162049743 13679046768911920743074615)
        ·
          refine ⟨20518570153367881114611923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13679046768911920743074615 20518570153367881114611923)
          ·
            refine ⟨30777855230051821671917885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20518570153367881114611923 30777855230051821671917885)
            ·
              refine ⟨11541695711269433126969207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30777855230051821671917885 11541695711269433126969207)
              ·
                refine ⟨17312543566904149690453811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11541695711269433126969207 17312543566904149690453811)
                ·
                  refine ⟨25968815350356224535680717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17312543566904149690453811 25968815350356224535680717)
                  ·
                    refine ⟨9738305756383584200880269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25968815350356224535680717 9738305756383584200880269)
                    ·
                      refine ⟨3651864658643844075330101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738305756383584200880269 3651864658643844075330101)
                      ·
                        rfl

theorem cell23_7111981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_7111981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7111981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7111981 prefixEnd_7111981 := by exact prefixLift 7111981
  have htrace : WordTrace (prefixWord ++ tailWord_7111981) baseStart_7111981 baseEnd_7111981 := by
    simpa [prefixWord, tailWord_7111981, baseEnd_7111981] using wordTrace_append hprefix tailTrace_7111981
  have hstable : (prefixWord ++ tailWord_7111981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7111981).length < 2 ^ (prefixWord ++ tailWord_7111981).sum := by decide
  have hdescent : baseEnd_7111981 < baseStart_7111981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7111981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112007 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_7112007 : Nat := 118140960795 + 7112007 * 2 ^ 59
def prefixEnd_7112007 : Nat := 4983230072969 + 3 ^ 40 * 7112007 * 2
def baseEnd_7112007 : Nat := 3651878009140860973604981

theorem tailTrace_7112007 : CollatzResearch.WordTrace tailWord_7112007 prefixEnd_7112007 3651878009140860973604981 := by
  unfold tailWord_7112007
  simp only [CollatzResearch.WordTrace]
  refine ⟨259396205545420747938750275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172930803696947165292500183 259396205545420747938750275)
  ·
    refine ⟨389094308318131121908125413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259396205545420747938750275 389094308318131121908125413)
    ·
      refine ⟨72955182809649585357773515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389094308318131121908125413 72955182809649585357773515)
      ·
        refine ⟨109432774214474378036660273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72955182809649585357773515 109432774214474378036660273)
        ·
          refine ⟨82074580660855783527495205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109432774214474378036660273 82074580660855783527495205)
          ·
            refine ⟨15388983873910459411405351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82074580660855783527495205 15388983873910459411405351)
            ·
              refine ⟨23083475810865689117108027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15388983873910459411405351 23083475810865689117108027)
              ·
                refine ⟨34625213716298533675662041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23083475810865689117108027 34625213716298533675662041)
                ·
                  refine ⟨25968910287223900256746531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34625213716298533675662041 25968910287223900256746531)
                  ·
                    refine ⟨38953365430835850385119797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25968910287223900256746531 38953365430835850385119797)
                    ·
                      refine ⟨3651878009140860973604981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38953365430835850385119797 3651878009140860973604981)
                      ·
                        rfl

theorem cell23_7112007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_7112007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112007 prefixEnd_7112007 := by exact prefixLift 7112007
  have htrace : WordTrace (prefixWord ++ tailWord_7112007) baseStart_7112007 baseEnd_7112007 := by
    simpa [prefixWord, tailWord_7112007, baseEnd_7112007] using wordTrace_append hprefix tailTrace_7112007
  have hstable : (prefixWord ++ tailWord_7112007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112007).length < 2 ^ (prefixWord ++ tailWord_7112007).sum := by decide
  have hdescent : baseEnd_7112007 < baseStart_7112007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112010 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 9]
def baseStart_7112010 : Nat := 118140960795 + 7112010 * 2 ^ 59
def prefixEnd_7112010 : Nat := 4983230072969 + 3 ^ 40 * 7112010 * 2
def baseEnd_7112010 : Nat := 405764394398091606874163

theorem tailTrace_7112010 : CollatzResearch.WordTrace tailWord_7112010 prefixEnd_7112010 405764394398091606874163 := by
  unfold tailWord_7112010
  simp only [CollatzResearch.WordTrace]
  refine ⟨64849078741102469862777371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172930876642939919634072989 64849078741102469862777371)
  ·
    refine ⟨97273618111653704794166057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64849078741102469862777371 97273618111653704794166057)
    ·
      refine ⟨72955213583740278595624543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97273618111653704794166057 72955213583740278595624543)
      ·
        refine ⟨109432820375610417893436815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72955213583740278595624543 109432820375610417893436815)
        ·
          refine ⟨164149230563415626840155223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109432820375610417893436815 164149230563415626840155223)
          ·
            refine ⟨246223845845123440260232835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164149230563415626840155223 246223845845123440260232835)
            ·
              refine ⟨369335768767685160390349253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246223845845123440260232835 369335768767685160390349253)
              ·
                refine ⟨69250456643940967573190485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369335768767685160390349253 69250456643940967573190485)
                ·
                  refine ⟨405764394398091606874163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69250456643940967573190485 405764394398091606874163)
                  ·
                    rfl

theorem cell23_7112010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_7112010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112010 prefixEnd_7112010 := by exact prefixLift 7112010
  have htrace : WordTrace (prefixWord ++ tailWord_7112010) baseStart_7112010 baseEnd_7112010 := by
    simpa [prefixWord, tailWord_7112010, baseEnd_7112010] using wordTrace_append hprefix tailTrace_7112010
  have hstable : (prefixWord ++ tailWord_7112010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112010).length < 2 ^ (prefixWord ++ tailWord_7112010).sum := by decide
  have hdescent : baseEnd_7112010 < baseStart_7112010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112021 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 4, 2, 2]
def baseStart_7112021 : Nat := 118140960795 + 7112021 * 2 ^ 59
def prefixEnd_7112021 : Nat := 4983230072969 + 3 ^ 40 * 7112021 * 2
def baseEnd_7112021 : Nat := 3651885197870023918829917

theorem tailTrace_7112021 : CollatzResearch.WordTrace tailWord_7112021 prefixEnd_7112021 3651885197870023918829917 := by
  unfold tailWord_7112021
  simp only [CollatzResearch.WordTrace]
  refine ⟨259396716167370028329759917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172931144111580018886506611 259396716167370028329759917)
  ·
    refine ⟨97273768562763760623659969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259396716167370028329759917 97273768562763760623659969)
    ·
      refine ⟨72955326422072820467744977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97273768562763760623659969 72955326422072820467744977)
      ·
        refine ⟨54716494816554615350808733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72955326422072820467744977 54716494816554615350808733)
        ·
          refine ⟨20518685556207980756553275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54716494816554615350808733 20518685556207980756553275)
          ·
            refine ⟨30778028334311971134829913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20518685556207980756553275 30778028334311971134829913)
            ·
              refine ⟨23083521250733978351122435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30778028334311971134829913 23083521250733978351122435)
              ·
                refine ⟨34625281876100967526683653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23083521250733978351122435 34625281876100967526683653)
                ·
                  refine ⟨6492240351768931411253185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34625281876100967526683653 6492240351768931411253185)
                  ·
                    refine ⟨4869180263826698558439889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6492240351768931411253185 4869180263826698558439889)
                    ·
                      refine ⟨3651885197870023918829917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4869180263826698558439889 3651885197870023918829917)
                      ·
                        rfl

theorem cell23_7112021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_7112021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112021 prefixEnd_7112021 := by exact prefixLift 7112021
  have htrace : WordTrace (prefixWord ++ tailWord_7112021) baseStart_7112021 baseEnd_7112021 := by
    simpa [prefixWord, tailWord_7112021, baseEnd_7112021] using wordTrace_append hprefix tailTrace_7112021
  have hstable : (prefixWord ++ tailWord_7112021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112021).length < 2 ^ (prefixWord ++ tailWord_7112021).sum := by decide
  have hdescent : baseEnd_7112021 < baseStart_7112021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112037 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 1, 5, 3]
def baseStart_7112037 : Nat := 118140960795 + 7112037 * 2 ^ 59
def prefixEnd_7112037 : Nat := 4983230072969 + 3 ^ 40 * 7112037 * 2
def baseEnd_7112037 : Nat := 3651893413560495856229843

theorem tailTrace_7112037 : CollatzResearch.WordTrace tailWord_7112037 prefixEnd_7112037 3651893413560495856229843 := by
  unfold tailWord_7112037
  simp only [CollatzResearch.WordTrace]
  refine ⟨259397299735312063062342365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172931533156874708708228243 259397299735312063062342365)
  ·
    refine ⟨97273987400742023648378387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259397299735312063062342365 97273987400742023648378387)
    ·
      refine ⟨145910981101113035472567581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97273987400742023648378387 145910981101113035472567581)
      ·
        refine ⟨54716617912917388302212843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145910981101113035472567581 54716617912917388302212843)
        ·
          refine ⟨82074926869376082453319265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54716617912917388302212843 82074926869376082453319265)
          ·
            refine ⟨61556195152032061839989449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82074926869376082453319265 61556195152032061839989449)
            ·
              refine ⟨46167146364024046379992087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61556195152032061839989449 46167146364024046379992087)
              ·
                refine ⟨69250719546036069569988131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46167146364024046379992087 69250719546036069569988131)
                ·
                  refine ⟨103876079319054104354982197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69250719546036069569988131 103876079319054104354982197)
                  ·
                    refine ⟨9738382436161322283279581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103876079319054104354982197 9738382436161322283279581)
                    ·
                      refine ⟨3651893413560495856229843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738382436161322283279581 3651893413560495856229843)
                      ·
                        rfl

theorem cell23_7112037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_7112037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112037 prefixEnd_7112037 := by exact prefixLift 7112037
  have htrace : WordTrace (prefixWord ++ tailWord_7112037) baseStart_7112037 baseEnd_7112037 := by
    simpa [prefixWord, tailWord_7112037, baseEnd_7112037] using wordTrace_append hprefix tailTrace_7112037
  have hstable : (prefixWord ++ tailWord_7112037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112037).length < 2 ^ (prefixWord ++ tailWord_7112037).sum := by decide
  have hdescent : baseEnd_7112037 < baseStart_7112037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112057 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 2, 5]
def baseStart_7112057 : Nat := 118140960795 + 7112057 * 2 ^ 59
def prefixEnd_7112057 : Nat := 4983230072969 + 3 ^ 40 * 7112057 * 2
def baseEnd_7112057 : Nat := 1217301227724528592659917

theorem tailTrace_7112057 : CollatzResearch.WordTrace tailWord_7112057 prefixEnd_7112057 1217301227724528592659917 := by
  unfold tailWord_7112057
  simp only [CollatzResearch.WordTrace]
  refine ⟨259398029195239606478070425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172932019463493070985380283 259398029195239606478070425)
  ·
    refine ⟨194548521896429704858552819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259398029195239606478070425 194548521896429704858552819)
    ·
      refine ⟨291822782844644557287829229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194548521896429704858552819 291822782844644557287829229)
      ·
        refine ⟨109433543566741708982935961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291822782844644557287829229 109433543566741708982935961)
        ·
          refine ⟨82075157675056281737201971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109433543566741708982935961 82075157675056281737201971)
          ·
            refine ⟨123112736512584422605802957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82075157675056281737201971 123112736512584422605802957)
            ·
              refine ⟨46167276192219158477176109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123112736512584422605802957 46167276192219158477176109)
              ·
                refine ⟨17312728572082184428941041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46167276192219158477176109 17312728572082184428941041)
                ·
                  refine ⟨12984546429061638321705781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17312728572082184428941041 12984546429061638321705781)
                  ·
                    refine ⟨1217301227724528592659917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12984546429061638321705781 1217301227724528592659917)
                    ·
                      rfl

theorem cell23_7112057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_7112057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112057 prefixEnd_7112057 := by exact prefixLift 7112057
  have htrace : WordTrace (prefixWord ++ tailWord_7112057) baseStart_7112057 baseEnd_7112057 := by
    simpa [prefixWord, tailWord_7112057, baseEnd_7112057] using wordTrace_append hprefix tailTrace_7112057
  have hstable : (prefixWord ++ tailWord_7112057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112057).length < 2 ^ (prefixWord ++ tailWord_7112057).sum := by decide
  have hdescent : baseEnd_7112057 < baseStart_7112057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112067 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 5]
def baseStart_7112067 : Nat := 118140960795 + 7112067 * 2 ^ 59
def prefixEnd_7112067 : Nat := 4983230072969 + 3 ^ 40 * 7112067 * 2
def baseEnd_7112067 : Nat := 3651908817980130738854705

theorem tailTrace_7112067 : CollatzResearch.WordTrace tailWord_7112067 prefixEnd_7112067 3651908817980130738854705 := by
  unfold tailWord_7112067
  simp only [CollatzResearch.WordTrace]
  refine ⟨259398393925203378185934455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172932262616802252123956303 259398393925203378185934455)
  ·
    refine ⟨389097590887805067278901683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259398393925203378185934455 389097590887805067278901683)
    ·
      refine ⟨583646386331707600918352525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389097590887805067278901683 583646386331707600918352525)
      ·
        refine ⟨218867394874390350344382197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 583646386331707600918352525 218867394874390350344382197)
        ·
          refine ⟨20518818269474095344785831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218867394874390350344382197 20518818269474095344785831)
          ·
            refine ⟨30778227404211143017178747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20518818269474095344785831 30778227404211143017178747)
            ·
              refine ⟨46167341106316714525768121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30778227404211143017178747 46167341106316714525768121)
              ·
                refine ⟨34625505829737535894326091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46167341106316714525768121 34625505829737535894326091)
                ·
                  refine ⟨51938258744606303841489137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34625505829737535894326091 51938258744606303841489137)
                  ·
                    refine ⟨38953694058454727881116853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51938258744606303841489137 38953694058454727881116853)
                    ·
                      refine ⟨3651908817980130738854705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38953694058454727881116853 3651908817980130738854705)
                      ·
                        rfl

theorem cell23_7112067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_7112067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112067 prefixEnd_7112067 := by exact prefixLift 7112067
  have htrace : WordTrace (prefixWord ++ tailWord_7112067) baseStart_7112067 baseEnd_7112067 := by
    simpa [prefixWord, tailWord_7112067, baseEnd_7112067] using wordTrace_append hprefix tailTrace_7112067
  have hstable : (prefixWord ++ tailWord_7112067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112067).length < 2 ^ (prefixWord ++ tailWord_7112067).sum := by decide
  have hdescent : baseEnd_7112067 < baseStart_7112067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112084 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_7112084 : Nat := 118140960795 + 7112084 * 2 ^ 59
def prefixEnd_7112084 : Nat := 4983230072969 + 3 ^ 40 * 7112084 * 2
def baseEnd_7112084 : Nat := 3651917547151257172342127

theorem tailTrace_7112084 : CollatzResearch.WordTrace tailWord_7112084 prefixEnd_7112084 3651917547151257172342127 := by
  unfold tailWord_7112084
  simp only [CollatzResearch.WordTrace]
  refine ⟨129699506983070895044651653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172932675977427860059535537 129699506983070895044651653)
  ·
    refine ⟨24318657559325792820872185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129699506983070895044651653 24318657559325792820872185)
    ·
      refine ⟨18238993169494344615654139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24318657559325792820872185 18238993169494344615654139)
      ·
        refine ⟨27358489754241516923481209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18238993169494344615654139 27358489754241516923481209)
        ·
          refine ⟨20518867315681137692610907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27358489754241516923481209 20518867315681137692610907)
          ·
            refine ⟨30778300973521706538916361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20518867315681137692610907 30778300973521706538916361)
            ·
              refine ⟨23083725730141279904187271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30778300973521706538916361 23083725730141279904187271)
              ·
                refine ⟨34625588595211919856280907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23083725730141279904187271 34625588595211919856280907)
                ·
                  refine ⟨51938382892817879784421361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34625588595211919856280907 51938382892817879784421361)
                  ·
                    refine ⟨38953787169613409838316021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51938382892817879784421361 38953787169613409838316021)
                    ·
                      refine ⟨3651917547151257172342127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38953787169613409838316021 3651917547151257172342127)
                      ·
                        rfl

theorem cell23_7112084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_7112084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112084 prefixEnd_7112084 := by exact prefixLift 7112084
  have htrace : WordTrace (prefixWord ++ tailWord_7112084) baseStart_7112084 baseEnd_7112084 := by
    simpa [prefixWord, tailWord_7112084, baseEnd_7112084] using wordTrace_append hprefix tailTrace_7112084
  have hstable : (prefixWord ++ tailWord_7112084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112084).length < 2 ^ (prefixWord ++ tailWord_7112084).sum := by decide
  have hdescent : baseEnd_7112084 < baseStart_7112084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112114 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_7112114 : Nat := 118140960795 + 7112114 * 2 ^ 59
def prefixEnd_7112114 : Nat := 4983230072969 + 3 ^ 40 * 7112114 * 2
def baseEnd_7112114 : Nat := 3651932951570892054966989

theorem tailTrace_7112114 : CollatzResearch.WordTrace tailWord_7112114 prefixEnd_7112114 3651932951570892054966989 := by
  unfold tailWord_7112114
  simp only [CollatzResearch.WordTrace]
  refine ⟨64850027039008276303223849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172933405437355403475263597 64850027039008276303223849)
  ·
    refine ⟨48637520279256207227417887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64850027039008276303223849 48637520279256207227417887)
    ·
      refine ⟨72956280418884310841126831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48637520279256207227417887 72956280418884310841126831)
      ·
        refine ⟨109434420628326466261690247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72956280418884310841126831 109434420628326466261690247)
        ·
          refine ⟨164151630942489699392535371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109434420628326466261690247 164151630942489699392535371)
          ·
            refine ⟨246227446413734549088803057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164151630942489699392535371 246227446413734549088803057)
            ·
              refine ⟨184670584810300911816602293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246227446413734549088803057 184670584810300911816602293)
              ·
                refine ⟨17312867325965710482806465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184670584810300911816602293 17312867325965710482806465)
                ·
                  refine ⟨12984650494474282862104849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17312867325965710482806465 12984650494474282862104849)
                  ·
                    refine ⟨9738487870855712146578637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12984650494474282862104849 9738487870855712146578637)
                    ·
                      refine ⟨3651932951570892054966989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738487870855712146578637 3651932951570892054966989)
                      ·
                        rfl

theorem cell23_7112114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_7112114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112114 prefixEnd_7112114 := by exact prefixLift 7112114
  have htrace : WordTrace (prefixWord ++ tailWord_7112114) baseStart_7112114 baseEnd_7112114 := by
    simpa [prefixWord, tailWord_7112114, baseEnd_7112114] using wordTrace_append hprefix tailTrace_7112114
  have hstable : (prefixWord ++ tailWord_7112114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112114).length < 2 ^ (prefixWord ++ tailWord_7112114).sum := by decide
  have hdescent : baseEnd_7112114 < baseStart_7112114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112127 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 3]
def baseStart_7112127 : Nat := 118140960795 + 7112127 * 2 ^ 59
def prefixEnd_7112127 : Nat := 4983230072969 + 3 ^ 40 * 7112127 * 2
def baseEnd_7112127 : Nat := 3651939626819400504104429

theorem tailTrace_7112127 : CollatzResearch.WordTrace tailWord_7112127 prefixEnd_7112127 3651939626819400504104429 := by
  unfold tailWord_7112127
  simp only [CollatzResearch.WordTrace]
  refine ⟨259400582304986008433118635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172933721536657338955412423 259400582304986008433118635)
  ·
    refine ⟨389100873457479012649677953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259400582304986008433118635 389100873457479012649677953)
    ·
      refine ⟨291825655093109259487258465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389100873457479012649677953 291825655093109259487258465)
      ·
        refine ⟨218869241319831944615443849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291825655093109259487258465 218869241319831944615443849)
        ·
          refine ⟨164151930989873958461582887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218869241319831944615443849 164151930989873958461582887)
          ·
            refine ⟨246227896484810937692374331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164151930989873958461582887 246227896484810937692374331)
            ·
              refine ⟨369341844727216406538561497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246227896484810937692374331 369341844727216406538561497)
              ·
                refine ⟨277006383545412304903921123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369341844727216406538561497 277006383545412304903921123)
                ·
                  refine ⟨415509575318118457355881685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277006383545412304903921123 415509575318118457355881685)
                  ·
                    refine ⟨9738505671518401344278477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 415509575318118457355881685 9738505671518401344278477)
                    ·
                      refine ⟨3651939626819400504104429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738505671518401344278477 3651939626819400504104429)
                      ·
                        rfl

theorem cell23_7112127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_7112127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112127 prefixEnd_7112127 := by exact prefixLift 7112127
  have htrace : WordTrace (prefixWord ++ tailWord_7112127) baseStart_7112127 baseEnd_7112127 := by
    simpa [prefixWord, tailWord_7112127, baseEnd_7112127] using wordTrace_append hprefix tailTrace_7112127
  have hstable : (prefixWord ++ tailWord_7112127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112127).length < 2 ^ (prefixWord ++ tailWord_7112127).sum := by decide
  have hdescent : baseEnd_7112127 < baseStart_7112127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112144 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 7, 1, 3]
def baseStart_7112144 : Nat := 118140960795 + 7112144 * 2 ^ 59
def prefixEnd_7112144 : Nat := 4983230072969 + 3 ^ 40 * 7112144 * 2
def baseEnd_7112144 : Nat := 3651948355990526937591851

theorem tailTrace_7112144 : CollatzResearch.WordTrace tailWord_7112144 prefixEnd_7112144 3651948355990526937591851 := by
  unfold tailWord_7112144
  simp only [CollatzResearch.WordTrace]
  refine ⟨129700601172962210168243743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172934134897282946890991657 129700601172962210168243743)
  ·
    refine ⟨194550901759443315252365615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129700601172962210168243743 194550901759443315252365615)
    ·
      refine ⟨291826352639164972878548423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194550901759443315252365615 291826352639164972878548423)
      ·
        refine ⟨437739528958747459317822635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291826352639164972878548423 437739528958747459317822635)
        ·
          refine ⟨656609293438121188976733953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437739528958747459317822635 656609293438121188976733953)
          ·
            refine ⟨492456970078590891732550465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656609293438121188976733953 492456970078590891732550465)
            ·
              refine ⟨369342727558943168799412849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492456970078590891732550465 369342727558943168799412849)
              ·
                refine ⟨277007045669207376599559637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369342727558943168799412849 277007045669207376599559637)
                ·
                  refine ⟨6492352632872047889052179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 277007045669207376599559637 6492352632872047889052179)
                  ·
                    refine ⟨9738528949308071833578269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6492352632872047889052179 9738528949308071833578269)
                    ·
                      refine ⟨3651948355990526937591851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738528949308071833578269 3651948355990526937591851)
                      ·
                        rfl

theorem cell23_7112144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7, 1, 3].length) (baseStart_7112144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112144 prefixEnd_7112144 := by exact prefixLift 7112144
  have htrace : WordTrace (prefixWord ++ tailWord_7112144) baseStart_7112144 baseEnd_7112144 := by
    simpa [prefixWord, tailWord_7112144, baseEnd_7112144] using wordTrace_append hprefix tailTrace_7112144
  have hstable : (prefixWord ++ tailWord_7112144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112144).length < 2 ^ (prefixWord ++ tailWord_7112144).sum := by decide
  have hdescent : baseEnd_7112144 < baseStart_7112144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112161 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_7112161 : Nat := 118140960795 + 7112161 * 2 ^ 59
def prefixEnd_7112161 : Nat := 4983230072969 + 3 ^ 40 * 7112161 * 2
def baseEnd_7112161 : Nat := 3651957085161653371079273

theorem tailTrace_7112161 : CollatzResearch.WordTrace tailWord_7112161 prefixEnd_7112161 3651957085161653371079273 := by
  unfold tailWord_7112161
  simp only [CollatzResearch.WordTrace]
  refine ⟨259401822386862832239856337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172934548257908554826570891 259401822386862832239856337)
  ·
    refine ⟨194551366790147124179892253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259401822386862832239856337 194551366790147124179892253)
    ·
      refine ⟨72956762546305171567459595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194551366790147124179892253 72956762546305171567459595)
      ·
        refine ⟨109435143819457757351189393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72956762546305171567459595 109435143819457757351189393)
        ·
          refine ⟨82076357864593318013392045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109435143819457757351189393 82076357864593318013392045)
          ·
            refine ⟨30778634199222494255022017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82076357864593318013392045 30778634199222494255022017)
            ·
              refine ⟨23083975649416870691266513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30778634199222494255022017 23083975649416870691266513)
              ·
                refine ⟨17312981737062653018449885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23083975649416870691266513 17312981737062653018449885)
                ·
                  refine ⟨6492368151398494881918707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17312981737062653018449885 6492368151398494881918707)
                  ·
                    refine ⟨9738552227097742322878061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6492368151398494881918707 9738552227097742322878061)
                    ·
                      refine ⟨3651957085161653371079273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738552227097742322878061 3651957085161653371079273)
                      ·
                        rfl

theorem cell23_7112161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_7112161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112161 prefixEnd_7112161 := by exact prefixLift 7112161
  have htrace : WordTrace (prefixWord ++ tailWord_7112161) baseStart_7112161 baseEnd_7112161 := by
    simpa [prefixWord, tailWord_7112161, baseEnd_7112161] using wordTrace_append hprefix tailTrace_7112161
  have hstable : (prefixWord ++ tailWord_7112161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112161).length < 2 ^ (prefixWord ++ tailWord_7112161).sum := by decide
  have hdescent : baseEnd_7112161 < baseStart_7112161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112187 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 5]
def baseStart_7112187 : Nat := 118140960795 + 7112187 * 2 ^ 59
def prefixEnd_7112187 : Nat := 4983230072969 + 3 ^ 40 * 7112187 * 2
def baseEnd_7112187 : Nat := 3651970435658670269354153

theorem tailTrace_7112187 : CollatzResearch.WordTrace tailWord_7112187 prefixEnd_7112187 3651970435658670269354153 := by
  unfold tailWord_7112187
  simp only [CollatzResearch.WordTrace]
  refine ⟨259402770684768638680302815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172935180456512425786868543 259402770684768638680302815)
  ·
    refine ⟨389104156027152958020454223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259402770684768638680302815 389104156027152958020454223)
    ·
      refine ⟨583656234040729437030681335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389104156027152958020454223 583656234040729437030681335)
      ·
        refine ⟨875484351061094155546022003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583656234040729437030681335 875484351061094155546022003)
        ·
          refine ⟨1313226526591641233319033005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875484351061094155546022003 1313226526591641233319033005)
          ·
            refine ⟨492459947471865462494637377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1313226526591641233319033005 492459947471865462494637377)
            ·
              refine ⟨369344960603899096870978033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492459947471865462494637377 369344960603899096870978033)
              ·
                refine ⟨277008720452924322653233525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369344960603899096870978033 277008720452924322653233525)
                ·
                  refine ⟨25969567542461655248740643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 277008720452924322653233525 25969567542461655248740643)
                  ·
                    refine ⟨38954351313692482873110965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25969567542461655248740643 38954351313692482873110965)
                    ·
                      refine ⟨3651970435658670269354153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38954351313692482873110965 3651970435658670269354153)
                      ·
                        rfl

theorem cell23_7112187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 5].length) (baseStart_7112187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112187 prefixEnd_7112187 := by exact prefixLift 7112187
  have htrace : WordTrace (prefixWord ++ tailWord_7112187) baseStart_7112187 baseEnd_7112187 := by
    simpa [prefixWord, tailWord_7112187, baseEnd_7112187] using wordTrace_append hprefix tailTrace_7112187
  have hstable : (prefixWord ++ tailWord_7112187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112187).length < 2 ^ (prefixWord ++ tailWord_7112187).sum := by decide
  have hdescent : baseEnd_7112187 < baseStart_7112187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112211 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 2, 4]
def baseStart_7112211 : Nat := 118140960795 + 7112211 * 2 ^ 59
def prefixEnd_7112211 : Nat := 4983230072969 + 3 ^ 40 * 7112211 * 2
def baseEnd_7112211 : Nat := 1217327586398126058484681

theorem tailTrace_7112211 : CollatzResearch.WordTrace tailWord_7112211 prefixEnd_7112211 1217327586398126058484681 := by
  unfold tailWord_7112211
  simp only [CollatzResearch.WordTrace]
  refine ⟨259403646036681690779176487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172935764024454460519450991 259403646036681690779176487)
  ·
    refine ⟨389105469055022536168764731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259403646036681690779176487 389105469055022536168764731)
    ·
      refine ⟨583658203582533804253147097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389105469055022536168764731 583658203582533804253147097)
      ·
        refine ⟨437743652686900353189860323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583658203582533804253147097 437743652686900353189860323)
        ·
          refine ⟨656615479030350529784790485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437743652686900353189860323 656615479030350529784790485)
          ·
            refine ⟨15389425289773840541831027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 656615479030350529784790485 15389425289773840541831027)
            ·
              refine ⟨23084137934660760812746541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15389425289773840541831027 23084137934660760812746541)
              ·
                refine ⟨8656551725497785304779953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23084137934660760812746541 8656551725497785304779953)
                ·
                  refine ⟨6492413794123338978584965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8656551725497785304779953 6492413794123338978584965)
                  ·
                    refine ⟨1217327586398126058484681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6492413794123338978584965 1217327586398126058484681)
                    ·
                      rfl

theorem cell23_7112211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 4].length) (baseStart_7112211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112211 prefixEnd_7112211 := by exact prefixLift 7112211
  have htrace : WordTrace (prefixWord ++ tailWord_7112211) baseStart_7112211 baseEnd_7112211 := by
    simpa [prefixWord, tailWord_7112211, baseEnd_7112211] using wordTrace_append hprefix tailTrace_7112211
  have hstable : (prefixWord ++ tailWord_7112211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112211).length < 2 ^ (prefixWord ++ tailWord_7112211).sum := by decide
  have hdescent : baseEnd_7112211 < baseStart_7112211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112221 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_7112221 : Nat := 118140960795 + 7112221 * 2 ^ 59
def prefixEnd_7112221 : Nat := 4983230072969 + 3 ^ 40 * 7112221 * 2
def baseEnd_7112221 : Nat := 3651987894000923136328997

theorem tailTrace_7112221 : CollatzResearch.WordTrace tailWord_7112221 prefixEnd_7112221 3651987894000923136328997 := by
  unfold tailWord_7112221
  simp only [CollatzResearch.WordTrace]
  refine ⟨259404010766645462487040517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172936007177763641658027011 259404010766645462487040517)
  ·
    refine ⟨48638252018746024216320097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259404010766645462487040517 48638252018746024216320097)
    ·
      refine ⟨36478689014059518162240073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48638252018746024216320097 36478689014059518162240073)
      ·
        refine ⟨27359016760544638621680055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36478689014059518162240073 27359016760544638621680055)
        ·
          refine ⟨41038525140816957932520083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27359016760544638621680055 41038525140816957932520083)
          ·
            refine ⟨61557787711225436898780125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41038525140816957932520083 61557787711225436898780125)
            ·
              refine ⟨23084170391709538837042547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61557787711225436898780125 23084170391709538837042547)
              ·
                refine ⟨34626255587564308255563821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23084170391709538837042547 34626255587564308255563821)
                ·
                  refine ⟨12984845845336615595836433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34626255587564308255563821 12984845845336615595836433)
                  ·
                    refine ⟨9738634384002461696877325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12984845845336615595836433 9738634384002461696877325)
                    ·
                      refine ⟨3651987894000923136328997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738634384002461696877325 3651987894000923136328997)
                      ·
                        rfl

theorem cell23_7112221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_7112221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112221 prefixEnd_7112221 := by exact prefixLift 7112221
  have htrace : WordTrace (prefixWord ++ tailWord_7112221) baseStart_7112221 baseEnd_7112221 := by
    simpa [prefixWord, tailWord_7112221, baseEnd_7112221] using wordTrace_append hprefix tailTrace_7112221
  have hstable : (prefixWord ++ tailWord_7112221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112221).length < 2 ^ (prefixWord ++ tailWord_7112221).sum := by decide
  have hdescent : baseEnd_7112221 < baseStart_7112221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112224 : List Nat := [2, 1, 1, 6, 1, 1, 2, 9]
def baseStart_7112224 : Nat := 118140960795 + 7112224 * 2 ^ 59
def prefixEnd_7112224 : Nat := 4983230072969 + 3 ^ 40 * 7112224 * 2
def baseEnd_7112224 : Nat := 135258867942329134244129

theorem tailTrace_7112224 : CollatzResearch.WordTrace tailWord_7112224 prefixEnd_7112224 135258867942329134244129 := by
  unfold tailWord_7112224
  simp only [CollatzResearch.WordTrace]
  refine ⟨129702060092817296999699863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172936080123756395999599817 129702060092817296999699863)
  ·
    refine ⟨194553090139225945499549795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129702060092817296999699863 194553090139225945499549795)
    ·
      refine ⟨291829635208838918249324693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194553090139225945499549795 291829635208838918249324693)
      ·
        refine ⟨13679514150414324292937095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 291829635208838918249324693 13679514150414324292937095)
        ·
          refine ⟨20519271225621486439405643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13679514150414324292937095 20519271225621486439405643)
          ·
            refine ⟨30778906838432229659108465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20519271225621486439405643 30778906838432229659108465)
            ·
              refine ⟨23084180128824172244331349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30778906838432229659108465 23084180128824172244331349)
              ·
                refine ⟨135258867942329134244129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23084180128824172244331349 135258867942329134244129)
                ·
                  rfl

theorem cell23_7112224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 9].length) (baseStart_7112224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112224 prefixEnd_7112224 := by exact prefixLift 7112224
  have htrace : WordTrace (prefixWord ++ tailWord_7112224) baseStart_7112224 baseEnd_7112224 := by
    simpa [prefixWord, tailWord_7112224, baseEnd_7112224] using wordTrace_append hprefix tailTrace_7112224
  have hstable : (prefixWord ++ tailWord_7112224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112224).length < 2 ^ (prefixWord ++ tailWord_7112224).sum := by decide
  have hdescent : baseEnd_7112224 < baseStart_7112224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112238 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_7112238 : Nat := 118140960795 + 7112238 * 2 ^ 59
def prefixEnd_7112238 : Nat := 4983230072969 + 3 ^ 40 * 7112238 * 2
def baseEnd_7112238 : Nat := 3651996623172049569816419

theorem tailTrace_7112238 : CollatzResearch.WordTrace tailWord_7112238 prefixEnd_7112238 3651996623172049569816419 := by
  unfold tailWord_7112238
  simp only [CollatzResearch.WordTrace]
  refine ⟨32425578850947984298801171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172936420538389249593606245 32425578850947984298801171)
  ·
    refine ⟨48638368276421976448201757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32425578850947984298801171 48638368276421976448201757)
    ·
      refine ⟨18239388103658241168075659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48638368276421976448201757 18239388103658241168075659)
      ·
        refine ⟨27359082155487361752113489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18239388103658241168075659 27359082155487361752113489)
        ·
          refine ⟨20519311616615521314085117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27359082155487361752113489 20519311616615521314085117)
          ·
            refine ⟨7694741856230820492781919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20519311616615521314085117 7694741856230820492781919)
            ·
              refine ⟨11542112784346230739172879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694741856230820492781919 11542112784346230739172879)
              ·
                refine ⟨17313169176519346108759319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11542112784346230739172879 17313169176519346108759319)
                ·
                  refine ⟨25969753764779019163138979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17313169176519346108759319 25969753764779019163138979)
                  ·
                    refine ⟨38954630647168528744708469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25969753764779019163138979 38954630647168528744708469)
                    ·
                      refine ⟨3651996623172049569816419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38954630647168528744708469 3651996623172049569816419)
                      ·
                        rfl

theorem cell23_7112238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_7112238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112238 prefixEnd_7112238 := by exact prefixLift 7112238
  have htrace : WordTrace (prefixWord ++ tailWord_7112238) baseStart_7112238 baseEnd_7112238 := by
    simpa [prefixWord, tailWord_7112238, baseEnd_7112238] using wordTrace_append hprefix tailTrace_7112238
  have hstable : (prefixWord ++ tailWord_7112238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112238).length < 2 ^ (prefixWord ++ tailWord_7112238).sum := by decide
  have hdescent : baseEnd_7112238 < baseStart_7112238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112246 : List Nat := [5, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_7112246 : Nat := 118140960795 + 7112246 * 2 ^ 59
def prefixEnd_7112246 : Nat := 4983230072969 + 3 ^ 40 * 7112246 * 2
def baseEnd_7112246 : Nat := 3652000731017285538516383

theorem tailTrace_7112246 : CollatzResearch.WordTrace tailWord_7112246 prefixEnd_7112246 3652000731017285538516383 := by
  unfold tailWord_7112246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16212807661972180734793787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172936615061036594504467061 16212807661972180734793787)
  ·
    refine ⟨24319211492958271102190681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16212807661972180734793787 24319211492958271102190681)
    ·
      refine ⟨18239408619718703326643011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24319211492958271102190681 18239408619718703326643011)
      ·
        refine ⟨27359112929578054989964517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18239408619718703326643011 27359112929578054989964517)
        ·
          refine ⟨5129833674295885310618347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27359112929578054989964517 5129833674295885310618347)
          ·
            refine ⟨7694750511443827965927521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129833674295885310618347 7694750511443827965927521)
            ·
              refine ⟨5771062883582870974445641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7694750511443827965927521 5771062883582870974445641)
              ·
                refine ⟨4328297162687153230834231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5771062883582870974445641 4328297162687153230834231)
                ·
                  refine ⟨6492445744030729846251347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4328297162687153230834231 6492445744030729846251347)
                  ·
                    refine ⟨9738668616046094769377021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6492445744030729846251347 9738668616046094769377021)
                    ·
                      refine ⟨3652000731017285538516383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738668616046094769377021 3652000731017285538516383)
                      ·
                        rfl

theorem cell23_7112246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_7112246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112246 prefixEnd_7112246 := by exact prefixLift 7112246
  have htrace : WordTrace (prefixWord ++ tailWord_7112246) baseStart_7112246 baseEnd_7112246 := by
    simpa [prefixWord, tailWord_7112246, baseEnd_7112246] using wordTrace_append hprefix tailTrace_7112246
  have hstable : (prefixWord ++ tailWord_7112246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112246).length < 2 ^ (prefixWord ++ tailWord_7112246).sum := by decide
  have hdescent : baseEnd_7112246 < baseStart_7112246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112252 : List Nat := [2, 2, 2, 2, 4, 1, 1, 4, 1, 2, 2]
def baseStart_7112252 : Nat := 118140960795 + 7112252 * 2 ^ 59
def prefixEnd_7112252 : Nat := 4983230072969 + 3 ^ 40 * 7112252 * 2
def baseEnd_7112252 : Nat := 3652003811901212515041355

theorem tailTrace_7112252 : CollatzResearch.WordTrace tailWord_7112252 prefixEnd_7112252 3652003811901212515041355 := by
  unfold tailWord_7112252
  simp only [CollatzResearch.WordTrace]
  refine ⟨129702570714766577390709505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172936760953022103187612673 129702570714766577390709505)
  ·
    refine ⟨97276928036074933043032129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129702570714766577390709505 97276928036074933043032129)
    ·
      refine ⟨72957696027056199782274097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97276928036074933043032129 72957696027056199782274097)
      ·
        refine ⟨54718272020292149836705573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72957696027056199782274097 54718272020292149836705573)
        ·
          refine ⟨10259676003804778094382295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54718272020292149836705573 10259676003804778094382295)
          ·
            refine ⟨15389514005707167141573443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10259676003804778094382295 15389514005707167141573443)
            ·
              refine ⟨23084271008560750712360165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15389514005707167141573443 23084271008560750712360165)
              ·
                refine ⟨4328300814105140758567531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23084271008560750712360165 4328300814105140758567531)
                ·
                  refine ⟨6492451221157711137851297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4328300814105140758567531 6492451221157711137851297)
                  ·
                    refine ⟨4869338415868283353388473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6492451221157711137851297 4869338415868283353388473)
                    ·
                      refine ⟨3652003811901212515041355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4869338415868283353388473 3652003811901212515041355)
                      ·
                        rfl

theorem cell23_7112252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_7112252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112252 prefixEnd_7112252 := by exact prefixLift 7112252
  have htrace : WordTrace (prefixWord ++ tailWord_7112252) baseStart_7112252 baseEnd_7112252 := by
    simpa [prefixWord, tailWord_7112252, baseEnd_7112252] using wordTrace_append hprefix tailTrace_7112252
  have hstable : (prefixWord ++ tailWord_7112252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112252).length < 2 ^ (prefixWord ++ tailWord_7112252).sum := by decide
  have hdescent : baseEnd_7112252 < baseStart_7112252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112261 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 5, 3, 2]
def baseStart_7112261 : Nat := 118140960795 + 7112261 * 2 ^ 59
def prefixEnd_7112261 : Nat := 4983230072969 + 3 ^ 40 * 7112261 * 2
def baseEnd_7112261 : Nat := 3652008433227102979828813

theorem tailTrace_7112261 : CollatzResearch.WordTrace tailWord_7112261 prefixEnd_7112261 3652008433227102979828813 := by
  unfold tailWord_7112261
  simp only [CollatzResearch.WordTrace]
  refine ⟨259405469686500549318496637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172936979791000366212331091 259405469686500549318496637)
  ·
    refine ⟨97277051132437705994436239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259405469686500549318496637 97277051132437705994436239)
    ·
      refine ⟨145915576698656558991654359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97277051132437705994436239 145915576698656558991654359)
      ·
        refine ⟨218873365047984838487481539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145915576698656558991654359 218873365047984838487481539)
        ·
          refine ⟨328310047571977257731222309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218873365047984838487481539 328310047571977257731222309)
          ·
            refine ⟨61558133919745735824604183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 328310047571977257731222309 61558133919745735824604183)
            ·
              refine ⟨92337200879618603736906275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61558133919745735824604183 92337200879618603736906275)
              ·
                refine ⟨138505801319427905605359413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92337200879618603736906275 138505801319427905605359413)
                ·
                  refine ⟨12984918873696366150502445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138505801319427905605359413 12984918873696366150502445)
                  ·
                    refine ⟨4869344577636137306438417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12984918873696366150502445 4869344577636137306438417)
                    ·
                      refine ⟨3652008433227102979828813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4869344577636137306438417 3652008433227102979828813)
                      ·
                        rfl

theorem cell23_7112261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 3, 2].length) (baseStart_7112261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112261 prefixEnd_7112261 := by exact prefixLift 7112261
  have htrace : WordTrace (prefixWord ++ tailWord_7112261) baseStart_7112261 baseEnd_7112261 := by
    simpa [prefixWord, tailWord_7112261, baseEnd_7112261] using wordTrace_append hprefix tailTrace_7112261
  have hstable : (prefixWord ++ tailWord_7112261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112261).length < 2 ^ (prefixWord ++ tailWord_7112261).sum := by decide
  have hdescent : baseEnd_7112261 < baseStart_7112261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112268 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 2, 1, 3]
def baseStart_7112268 : Nat := 118140960795 + 7112268 * 2 ^ 59
def prefixEnd_7112268 : Nat := 4983230072969 + 3 ^ 40 * 7112268 * 2
def baseEnd_7112268 : Nat := 3652012027591684452441281

theorem tailTrace_7112268 : CollatzResearch.WordTrace tailWord_7112268 prefixEnd_7112268 3652012027591684452441281 := by
  unfold tailWord_7112268
  simp only [CollatzResearch.WordTrace]
  refine ⟨129702862498737594757000729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172937149998316793009334305 129702862498737594757000729)
  ·
    refine ⟨97277146874053196067750547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129702862498737594757000729 97277146874053196067750547)
    ·
      refine ⟨145915720311079794101625821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97277146874053196067750547 145915720311079794101625821)
      ·
        refine ⟨54718395116654922788109683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145915720311079794101625821 54718395116654922788109683)
        ·
          refine ⟨82077592674982384182164525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54718395116654922788109683 82077592674982384182164525)
          ·
            refine ⟨30779097253118394068311697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82077592674982384182164525 30779097253118394068311697)
            ·
              refine ⟨23084322939838795551233773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30779097253118394068311697 23084322939838795551233773)
              ·
                refine ⟨8656621102439548331712665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23084322939838795551233773 8656621102439548331712665)
                ·
                  refine ⟨6492465826829661248784499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8656621102439548331712665 6492465826829661248784499)
                  ·
                    refine ⟨9738698740244491873176749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6492465826829661248784499 9738698740244491873176749)
                    ·
                      refine ⟨3652012027591684452441281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738698740244491873176749 3652012027591684452441281)
                      ·
                        rfl

theorem cell23_7112268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_7112268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112268 prefixEnd_7112268 := by exact prefixLift 7112268
  have htrace : WordTrace (prefixWord ++ tailWord_7112268) baseStart_7112268 baseEnd_7112268 := by
    simpa [prefixWord, tailWord_7112268, baseEnd_7112268] using wordTrace_append hprefix tailTrace_7112268
  have hstable : (prefixWord ++ tailWord_7112268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112268).length < 2 ^ (prefixWord ++ tailWord_7112268).sum := by decide
  have hdescent : baseEnd_7112268 < baseStart_7112268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112295 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_7112295 : Nat := 118140960795 + 7112295 * 2 ^ 59
def prefixEnd_7112295 : Nat := 4983230072969 + 3 ^ 40 * 7112295 * 2
def baseEnd_7112295 : Nat := 3652025891569355846803657

theorem tailTrace_7112295 : CollatzResearch.WordTrace tailWord_7112295 prefixEnd_7112295 3652025891569355846803657 := by
  unfold tailWord_7112295
  simp only [CollatzResearch.WordTrace]
  refine ⟨259406709768377373125234339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172937806512251582083489559 259406709768377373125234339)
  ·
    refine ⟨389110064652566059687851509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259406709768377373125234339 389110064652566059687851509)
    ·
      refine ⟨36479068561178068095736079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 389110064652566059687851509 36479068561178068095736079)
      ·
        refine ⟨54718602841767102143604119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36479068561178068095736079 54718602841767102143604119)
        ·
          refine ⟨82077904262650653215406179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54718602841767102143604119 82077904262650653215406179)
          ·
            refine ⟨123116856393975979823109269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82077904262650653215406179 123116856393975979823109269)
            ·
              refine ⟨5771102643467624054208247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123116856393975979823109269 5771102643467624054208247)
              ·
                refine ⟨8656653965201436081312371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5771102643467624054208247 8656653965201436081312371)
                ·
                  refine ⟨12984980947802154121968557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8656653965201436081312371 12984980947802154121968557)
                  ·
                    refine ⟨4869367855425807795738209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12984980947802154121968557 4869367855425807795738209)
                    ·
                      refine ⟨3652025891569355846803657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4869367855425807795738209 3652025891569355846803657)
                      ·
                        rfl

theorem cell23_7112295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_7112295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112295 prefixEnd_7112295 := by exact prefixLift 7112295
  have htrace : WordTrace (prefixWord ++ tailWord_7112295) baseStart_7112295 baseEnd_7112295 := by
    simpa [prefixWord, tailWord_7112295, baseEnd_7112295] using wordTrace_append hprefix tailTrace_7112295
  have hstable : (prefixWord ++ tailWord_7112295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112295).length < 2 ^ (prefixWord ++ tailWord_7112295).sum := by decide
  have hdescent : baseEnd_7112295 < baseStart_7112295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112302 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_7112302 : Nat := 118140960795 + 7112302 * 2 ^ 59
def prefixEnd_7112302 : Nat := 4983230072969 + 3 ^ 40 * 7112302 * 2
def baseEnd_7112302 : Nat := 3652029485933937319416125

theorem tailTrace_7112302 : CollatzResearch.WordTrace tailWord_7112302 prefixEnd_7112302 3652029485933937319416125 := by
  unfold tailWord_7112302
  simp only [CollatzResearch.WordTrace]
  refine ⟨32425870634919001665092395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172937976719568008880492773 32425870634919001665092395)
  ·
    refine ⟨48638805952378502497638593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32425870634919001665092395 48638805952378502497638593)
    ·
      refine ⟨36479104464283876873228945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48638805952378502497638593 36479104464283876873228945)
      ·
        refine ⟨27359328348212907654921709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36479104464283876873228945 27359328348212907654921709)
        ·
          refine ⟨10259748130579840370595641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27359328348212907654921709 10259748130579840370595641)
          ·
            refine ⟨7694811097934880277946731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10259748130579840370595641 7694811097934880277946731)
            ·
              refine ⟨11542216646902320416920097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694811097934880277946731 11542216646902320416920097)
              ·
                refine ⟨8656662485176740312690073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11542216646902320416920097 8656662485176740312690073)
                ·
                  refine ⟨6492496863882555234517555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8656662485176740312690073 6492496863882555234517555)
                  ·
                    refine ⟨9738745295823832851776333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6492496863882555234517555 9738745295823832851776333)
                    ·
                      refine ⟨3652029485933937319416125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738745295823832851776333 3652029485933937319416125)
                      ·
                        rfl

theorem cell23_7112302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_7112302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112302 prefixEnd_7112302 := by exact prefixLift 7112302
  have htrace : WordTrace (prefixWord ++ tailWord_7112302) baseStart_7112302 baseEnd_7112302 := by
    simpa [prefixWord, tailWord_7112302, baseEnd_7112302] using wordTrace_append hprefix tailTrace_7112302
  have hstable : (prefixWord ++ tailWord_7112302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112302).length < 2 ^ (prefixWord ++ tailWord_7112302).sum := by decide
  have hdescent : baseEnd_7112302 < baseStart_7112302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112321 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_7112321 : Nat := 118140960795 + 7112321 * 2 ^ 59
def prefixEnd_7112321 : Nat := 4983230072969 + 3 ^ 40 * 7112321 * 2
def baseEnd_7112321 : Nat := 3652039242066372745078537

theorem tailTrace_7112321 : CollatzResearch.WordTrace tailWord_7112321 prefixEnd_7112321 3652039242066372745078537 := by
  unfold tailWord_7112321
  simp only [CollatzResearch.WordTrace]
  refine ⟨259407658066283179565680817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172938438710855453043787211 259407658066283179565680817)
  ·
    refine ⟨194555743549712384674260613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259407658066283179565680817 194555743549712384674260613)
    ·
      refine ⟨36479201915571072126423865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194555743549712384674260613 36479201915571072126423865)
      ·
        refine ⟨27359401436678304094817899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36479201915571072126423865 27359401436678304094817899)
        ·
          refine ⟨41039102155017456142226849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27359401436678304094817899 41039102155017456142226849)
          ·
            refine ⟨30779326616263092106670137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41039102155017456142226849 30779326616263092106670137)
            ·
              refine ⟨23084494962197319080002603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30779326616263092106670137 23084494962197319080002603)
              ·
                refine ⟨34626742443295978620003905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23084494962197319080002603 34626742443295978620003905)
                ·
                  refine ⟨25970056832471983965002929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34626742443295978620003905 25970056832471983965002929)
                  ·
                    refine ⟨19477542624353987973752197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25970056832471983965002929 19477542624353987973752197)
                    ·
                      refine ⟨3652039242066372745078537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19477542624353987973752197 3652039242066372745078537)
                      ·
                        rfl

theorem cell23_7112321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_7112321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112321 prefixEnd_7112321 := by exact prefixLift 7112321
  have htrace : WordTrace (prefixWord ++ tailWord_7112321) baseStart_7112321 baseEnd_7112321 := by
    simpa [prefixWord, tailWord_7112321, baseEnd_7112321] using wordTrace_append hprefix tailTrace_7112321
  have hstable : (prefixWord ++ tailWord_7112321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112321).length < 2 ^ (prefixWord ++ tailWord_7112321).sum := by decide
  have hdescent : baseEnd_7112321 < baseStart_7112321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112364 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_7112364 : Nat := 118140960795 + 7112364 * 2 ^ 59
def prefixEnd_7112364 : Nat := 4983230072969 + 3 ^ 40 * 7112364 * 2
def baseEnd_7112364 : Nat := 3652061321734516076840839

theorem tailTrace_7112364 : CollatzResearch.WordTrace tailWord_7112364 prefixEnd_7112364 3652061321734516076840839 := by
  unfold tailWord_7112364
  simp only [CollatzResearch.WordTrace]
  refine ⟨129704613202563698954748073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172939484270084931939664097 129704613202563698954748073)
  ·
    refine ⟨97278459901922774216061055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129704613202563698954748073 97278459901922774216061055)
    ·
      refine ⟨145917689852884161324091583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97278459901922774216061055 145917689852884161324091583)
      ·
        refine ⟨218876534779326241986137375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145917689852884161324091583 218876534779326241986137375)
        ·
          refine ⟨328314802168989362979206063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218876534779326241986137375 328314802168989362979206063)
          ·
            refine ⟨492472203253484044468809095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328314802168989362979206063 492472203253484044468809095)
            ·
              refine ⟨738708304880226066703213643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492472203253484044468809095 738708304880226066703213643)
              ·
                refine ⟨1108062457320339100054820465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738708304880226066703213643 1108062457320339100054820465)
                ·
                  refine ⟨831046842990254325041115349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108062457320339100054820465 831046842990254325041115349)
                  ·
                    refine ⟨19477660382584085743151141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 831046842990254325041115349 19477660382584085743151141)
                    ·
                      refine ⟨3652061321734516076840839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19477660382584085743151141 3652061321734516076840839)
                      ·
                        rfl

theorem cell23_7112364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_7112364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112364 prefixEnd_7112364 := by exact prefixLift 7112364
  have htrace : WordTrace (prefixWord ++ tailWord_7112364) baseStart_7112364 baseEnd_7112364 := by
    simpa [prefixWord, tailWord_7112364, baseEnd_7112364] using wordTrace_append hprefix tailTrace_7112364
  have hstable : (prefixWord ++ tailWord_7112364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112364).length < 2 ^ (prefixWord ++ tailWord_7112364).sum := by decide
  have hdescent : baseEnd_7112364 < baseStart_7112364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112365 : List Nat := [1, 5, 2, 1, 1, 1, 5, 2, 5]
def baseStart_7112365 : Nat := 118140960795 + 7112365 * 2 ^ 59
def prefixEnd_7112365 : Nat := 4983230072969 + 3 ^ 40 * 7112365 * 2
def baseEnd_7112365 : Nat := 405784648357241174769815

theorem tailTrace_7112365 : CollatzResearch.WordTrace tailWord_7112365 prefixEnd_7112365 405784648357241174769815 := by
  unfold tailWord_7112365
  simp only [CollatzResearch.WordTrace]
  refine ⟨259409262878123775080282549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172939508585415850053521699 259409262878123775080282549)
  ·
    refine ⟨24319618394824103913776489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259409262878123775080282549 24319618394824103913776489)
    ·
      refine ⟨18239713796118077935332367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24319618394824103913776489 18239713796118077935332367)
      ·
        refine ⟨27359570694177116902998551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18239713796118077935332367 27359570694177116902998551)
        ·
          refine ⟨41039356041265675354497827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27359570694177116902998551 41039356041265675354497827)
          ·
            refine ⟨61559034061898513031746741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41039356041265675354497827 61559034061898513031746741)
            ·
              refine ⟨5771159443302985596726257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61559034061898513031746741 5771159443302985596726257)
              ·
                refine ⟨4328369582477239197544693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5771159443302985596726257 4328369582477239197544693)
                ·
                  refine ⟨405784648357241174769815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4328369582477239197544693 405784648357241174769815)
                  ·
                    rfl

theorem cell23_7112365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_7112365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112365 prefixEnd_7112365 := by exact prefixLift 7112365
  have htrace : WordTrace (prefixWord ++ tailWord_7112365) baseStart_7112365 baseEnd_7112365 := by
    simpa [prefixWord, tailWord_7112365, baseEnd_7112365] using wordTrace_append hprefix tailTrace_7112365
  have hstable : (prefixWord ++ tailWord_7112365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112365).length < 2 ^ (prefixWord ++ tailWord_7112365).sum := by decide
  have hdescent : baseEnd_7112365 < baseStart_7112365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112381 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_7112381 : Nat := 118140960795 + 7112381 * 2 ^ 59
def prefixEnd_7112381 : Nat := 4983230072969 + 3 ^ 40 * 7112381 * 2
def baseEnd_7112381 : Nat := 3652070050905642510328261

theorem tailTrace_7112381 : CollatzResearch.WordTrace tailWord_7112381 prefixEnd_7112381 3652070050905642510328261 := by
  unfold tailWord_7112381
  simp only [CollatzResearch.WordTrace]
  refine ⟨259409846446065809812864997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172939897630710539875243331 259409846446065809812864997)
  ·
    refine ⟨48639346208637339339912187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259409846446065809812864997 48639346208637339339912187)
    ·
      refine ⟨72959019312956009009868281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48639346208637339339912187 72959019312956009009868281)
      ·
        refine ⟨54719264484717006757401211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72959019312956009009868281 54719264484717006757401211)
        ·
          refine ⟨82078896727075510136101817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54719264484717006757401211 82078896727075510136101817)
          ·
            refine ⟨61559172545306632602076363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82078896727075510136101817 61559172545306632602076363)
            ·
              refine ⟨92338758817959948903114545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61559172545306632602076363 92338758817959948903114545)
              ·
                refine ⟨69254069113469961677335909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92338758817959948903114545 69254069113469961677335909)
                ·
                  refine ⟨12985137958775617814500483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69254069113469961677335909 12985137958775617814500483)
                  ·
                    refine ⟨19477706938163426721750725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12985137958775617814500483 19477706938163426721750725)
                    ·
                      refine ⟨3652070050905642510328261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19477706938163426721750725 3652070050905642510328261)
                      ·
                        rfl

theorem cell23_7112381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_7112381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112381 prefixEnd_7112381 := by exact prefixLift 7112381
  have htrace : WordTrace (prefixWord ++ tailWord_7112381) baseStart_7112381 baseEnd_7112381 := by
    simpa [prefixWord, tailWord_7112381, baseEnd_7112381] using wordTrace_append hprefix tailTrace_7112381
  have hstable : (prefixWord ++ tailWord_7112381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112381).length < 2 ^ (prefixWord ++ tailWord_7112381).sum := by decide
  have hdescent : baseEnd_7112381 < baseStart_7112381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112391 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 5, 4]
def baseStart_7112391 : Nat := 118140960795 + 7112391 * 2 ^ 59
def prefixEnd_7112391 : Nat := 4983230072969 + 3 ^ 40 * 7112391 * 2
def baseEnd_7112391 : Nat := 1217358395237395823734405

theorem tailTrace_7112391 : CollatzResearch.WordTrace tailWord_7112391 prefixEnd_7112391 1217358395237395823734405 := by
  unfold tailWord_7112391
  simp only [CollatzResearch.WordTrace]
  refine ⟨259410211176029581520729027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172940140784019721013819351 259410211176029581520729027)
  ·
    refine ⟨389115316764044372281093541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259410211176029581520729027 389115316764044372281093541)
    ·
      refine ⟨72959121893258319802705039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389115316764044372281093541 72959121893258319802705039)
      ·
        refine ⟨109438682839887479704057559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72959121893258319802705039 109438682839887479704057559)
        ·
          refine ⟨164158024259831219556086339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109438682839887479704057559 164158024259831219556086339)
          ·
            refine ⟨246237036389746829334129509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164158024259831219556086339 246237036389746829334129509)
            ·
              refine ⟨46169444323077530500149283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246237036389746829334129509 46169444323077530500149283)
              ·
                refine ⟨69254166484616295750223925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46169444323077530500149283 69254166484616295750223925)
                ·
                  refine ⟨6492578107932777726583493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69254166484616295750223925 6492578107932777726583493)
                  ·
                    refine ⟨1217358395237395823734405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6492578107932777726583493 1217358395237395823734405)
                    ·
                      rfl

theorem cell23_7112391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_7112391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112391 prefixEnd_7112391 := by exact prefixLift 7112391
  have htrace : WordTrace (prefixWord ++ tailWord_7112391) baseStart_7112391 baseEnd_7112391 := by
    simpa [prefixWord, tailWord_7112391, baseEnd_7112391] using wordTrace_append hprefix tailTrace_7112391
  have hstable : (prefixWord ++ tailWord_7112391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112391).length < 2 ^ (prefixWord ++ tailWord_7112391).sum := by decide
  have hdescent : baseEnd_7112391 < baseStart_7112391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112398 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_7112398 : Nat := 118140960795 + 7112398 * 2 ^ 59
def prefixEnd_7112398 : Nat := 4983230072969 + 3 ^ 40 * 7112398 * 2
def baseEnd_7112398 : Nat := 3652078780076768943815683

theorem tailTrace_7112398 : CollatzResearch.WordTrace tailWord_7112398 prefixEnd_7112398 3652078780076768943815683 := by
  unfold tailWord_7112398
  simp only [CollatzResearch.WordTrace]
  refine ⟨32426308310875527714529231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172940310991336147810822565 32426308310875527714529231)
  ·
    refine ⟨48639462466313291571793847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32426308310875527714529231 48639462466313291571793847)
    ·
      refine ⟨72959193699469937357690771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48639462466313291571793847 72959193699469937357690771)
      ·
        refine ⟨109438790549204906036536157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72959193699469937357690771 109438790549204906036536157)
        ·
          refine ⟨41039546455951839763701059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109438790549204906036536157 41039546455951839763701059)
          ·
            refine ⟨61559319683927759645551589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41039546455951839763701059 61559319683927759645551589)
            ·
              refine ⟨11542372440736454933540923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61559319683927759645551589 11542372440736454933540923)
              ·
                refine ⟨17313558661104682400311385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11542372440736454933540923 17313558661104682400311385)
                ·
                  refine ⟨12985168995828511800233539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17313558661104682400311385 12985168995828511800233539)
                  ·
                    refine ⟨19477753493742767700350309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12985168995828511800233539 19477753493742767700350309)
                    ·
                      refine ⟨3652078780076768943815683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19477753493742767700350309 3652078780076768943815683)
                      ·
                        rfl

theorem cell23_7112398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_7112398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112398 prefixEnd_7112398 := by exact prefixLift 7112398
  have htrace : WordTrace (prefixWord ++ tailWord_7112398) baseStart_7112398 baseEnd_7112398 := by
    simpa [prefixWord, tailWord_7112398, baseEnd_7112398] using wordTrace_append hprefix tailTrace_7112398
  have hstable : (prefixWord ++ tailWord_7112398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112398).length < 2 ^ (prefixWord ++ tailWord_7112398).sum := by decide
  have hdescent : baseEnd_7112398 < baseStart_7112398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112438 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_7112438 : Nat := 118140960795 + 7112438 * 2 ^ 59
def prefixEnd_7112438 : Nat := 4983230072969 + 3 ^ 40 * 7112438 * 2
def baseEnd_7112438 : Nat := 405788813255883198590611

theorem tailTrace_7112438 : CollatzResearch.WordTrace tailWord_7112438 prefixEnd_7112438 405788813255883198590611 := by
  unfold tailWord_7112438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16213245337928706784230623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172941283604572872365126645 16213245337928706784230623)
  ·
    refine ⟨24319868006893060176345935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16213245337928706784230623 24319868006893060176345935)
    ·
      refine ⟨36479802010339590264518903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24319868006893060176345935 36479802010339590264518903)
      ·
        refine ⟨54719703015509385396778355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36479802010339590264518903 54719703015509385396778355)
        ·
          refine ⟨82079554523264078095167533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54719703015509385396778355 82079554523264078095167533)
          ·
            refine ⟨30779832946224029285687825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82079554523264078095167533 30779832946224029285687825)
            ·
              refine ⟨23084874709668021964265869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30779832946224029285687825 23084874709668021964265869)
              ·
                refine ⟨8656828016125508236599701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23084874709668021964265869 8656828016125508236599701)
                ·
                  refine ⟨405788813255883198590611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8656828016125508236599701 405788813255883198590611)
                  ·
                    rfl

theorem cell23_7112438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_7112438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112438 prefixEnd_7112438 := by exact prefixLift 7112438
  have htrace : WordTrace (prefixWord ++ tailWord_7112438) baseStart_7112438 baseEnd_7112438 := by
    simpa [prefixWord, tailWord_7112438, baseEnd_7112438] using wordTrace_append hprefix tailTrace_7112438
  have hstable : (prefixWord ++ tailWord_7112438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112438).length < 2 ^ (prefixWord ++ tailWord_7112438).sum := by decide
  have hdescent : baseEnd_7112438 < baseStart_7112438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112448 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 3, 1, 3]
def baseStart_7112448 : Nat := 118140960795 + 7112448 * 2 ^ 59
def prefixEnd_7112448 : Nat := 4983230072969 + 3 ^ 40 * 7112448 * 2
def baseEnd_7112448 : Nat := 3652104454109493748190453

theorem tailTrace_7112448 : CollatzResearch.WordTrace tailWord_7112448 prefixEnd_7112448 3652104454109493748190453 := by
  unfold tailWord_7112448
  simp only [CollatzResearch.WordTrace]
  refine ⟨129706145068411540127776999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172941526757882053503702665 129706145068411540127776999)
  ·
    refine ⟨194559217602617310191665499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129706145068411540127776999 194559217602617310191665499)
    ·
      refine ⟨291838826403925965287498249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194559217602617310191665499 291838826403925965287498249)
      ·
        refine ⟨218879119802944473965623687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291838826403925965287498249 218879119802944473965623687)
        ·
          refine ⟨328318679704416710948435531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218879119802944473965623687 328318679704416710948435531)
          ·
            refine ⟨492478019556625066422653297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328318679704416710948435531 492478019556625066422653297)
            ·
              refine ⟨369358514667468799816989973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492478019556625066422653297 369358514667468799816989973)
              ·
                refine ⟨17313680375037599991421405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 369358514667468799816989973 17313680375037599991421405)
                ·
                  refine ⟨6492630140639099996783027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17313680375037599991421405 6492630140639099996783027)
                  ·
                    refine ⟨9738945210958649995174541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6492630140639099996783027 9738945210958649995174541)
                    ·
                      refine ⟨3652104454109493748190453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738945210958649995174541 3652104454109493748190453)
                      ·
                        rfl

theorem cell23_7112448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_7112448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112448 prefixEnd_7112448 := by exact prefixLift 7112448
  have htrace : WordTrace (prefixWord ++ tailWord_7112448) baseStart_7112448 baseEnd_7112448 := by
    simpa [prefixWord, tailWord_7112448, baseEnd_7112448] using wordTrace_append hprefix tailTrace_7112448
  have hstable : (prefixWord ++ tailWord_7112448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112448).length < 2 ^ (prefixWord ++ tailWord_7112448).sum := by decide
  have hdescent : baseEnd_7112448 < baseStart_7112448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112451 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 3, 5]
def baseStart_7112451 : Nat := 118140960795 + 7112451 * 2 ^ 59
def prefixEnd_7112451 : Nat := 4983230072969 + 3 ^ 40 * 7112451 * 2
def baseEnd_7112451 : Nat := 1217368664850485745484313

theorem tailTrace_7112451 : CollatzResearch.WordTrace tailWord_7112451 prefixEnd_7112451 1217368664850485745484313 := by
  unfold tailWord_7112451
  simp only [CollatzResearch.WordTrace]
  refine ⟨259412399555812211767913207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172941599703874807845275471 259412399555812211767913207)
  ·
    refine ⟨389118599333718317651869811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259412399555812211767913207 389118599333718317651869811)
    ·
      refine ⟨583677899000577476477804717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389118599333718317651869811 583677899000577476477804717)
      ·
        refine ⟨218879212125216553679176769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 583677899000577476477804717 218879212125216553679176769)
        ·
          refine ⟨164159409093912415259382577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218879212125216553679176769 164159409093912415259382577)
          ·
            refine ⟨123119556820434311444536933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164159409093912415259382577 123119556820434311444536933)
            ·
              refine ⟨23084916903831433395850675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123119556820434311444536933 23084916903831433395850675)
              ·
                refine ⟨34627375355747150093776013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23084916903831433395850675 34627375355747150093776013)
                ·
                  refine ⟨12985265758405181285166005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34627375355747150093776013 12985265758405181285166005)
                  ·
                    refine ⟨1217368664850485745484313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12985265758405181285166005 1217368664850485745484313)
                    ·
                      rfl

theorem cell23_7112451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 5].length) (baseStart_7112451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112451 prefixEnd_7112451 := by exact prefixLift 7112451
  have htrace : WordTrace (prefixWord ++ tailWord_7112451) baseStart_7112451 baseEnd_7112451 := by
    simpa [prefixWord, tailWord_7112451, baseEnd_7112451] using wordTrace_append hprefix tailTrace_7112451
  have hstable : (prefixWord ++ tailWord_7112451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112451).length < 2 ^ (prefixWord ++ tailWord_7112451).sum := by decide
  have hdescent : baseEnd_7112451 < baseStart_7112451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112482 : List Nat := [3, 3, 1, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_7112482 : Nat := 118140960795 + 7112482 * 2 ^ 59
def prefixEnd_7112482 : Nat := 4983230072969 + 3 ^ 40 * 7112482 * 2
def baseEnd_7112482 : Nat := 3652121912451746615165297

theorem tailTrace_7112482 : CollatzResearch.WordTrace tailWord_7112482 prefixEnd_7112482 3652121912451746615165297 := by
  unfold tailWord_7112482
  simp only [CollatzResearch.WordTrace]
  refine ⟨64853382554674976015572925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172942353479133269374861133 64853382554674976015572925)
  ·
    refine ⟨24320018458003116005839847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64853382554674976015572925 24320018458003116005839847)
    ·
      refine ⟨36480027687004674008759771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24320018458003116005839847 36480027687004674008759771)
      ·
        refine ⟨54720041530507011013139657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36480027687004674008759771 54720041530507011013139657)
        ·
          refine ⟨41040031147880258259854743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54720041530507011013139657 41040031147880258259854743)
          ·
            refine ⟨61560046721820387389782115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41040031147880258259854743 61560046721820387389782115)
            ·
              refine ⟨92340070082730581084673173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61560046721820387389782115 92340070082730581084673173)
              ·
                refine ⟨4328440785127995988344055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92340070082730581084673173 4328440785127995988344055)
                ·
                  refine ⟨6492661177691993982516083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4328440785127995988344055 6492661177691993982516083)
                  ·
                    refine ⟨9738991766537990973774125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6492661177691993982516083 9738991766537990973774125)
                    ·
                      refine ⟨3652121912451746615165297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9738991766537990973774125 3652121912451746615165297)
                      ·
                        rfl

theorem cell23_7112482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_7112482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112482 prefixEnd_7112482 := by exact prefixLift 7112482
  have htrace : WordTrace (prefixWord ++ tailWord_7112482) baseStart_7112482 baseEnd_7112482 := by
    simpa [prefixWord, tailWord_7112482, baseEnd_7112482] using wordTrace_append hprefix tailTrace_7112482
  have hstable : (prefixWord ++ tailWord_7112482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112482).length < 2 ^ (prefixWord ++ tailWord_7112482).sum := by decide
  have hdescent : baseEnd_7112482 < baseStart_7112482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112498 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_7112498 : Nat := 118140960795 + 7112498 * 2 ^ 59
def prefixEnd_7112498 : Nat := 4983230072969 + 3 ^ 40 * 7112498 * 2
def baseEnd_7112498 : Nat := 1217376709380739517521741

theorem tailTrace_7112498 : CollatzResearch.WordTrace tailWord_7112498 prefixEnd_7112498 1217376709380739517521741 := by
  unfold tailWord_7112498
  simp only [CollatzResearch.WordTrace]
  refine ⟨64853528446660484698718537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172942742524427959196582765 64853528446660484698718537)
  ·
    refine ⟨48640146334995363524038903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64853528446660484698718537 48640146334995363524038903)
    ·
      refine ⟨72960219502493045286058355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48640146334995363524038903 72960219502493045286058355)
      ·
        refine ⟨109440329253739567929087533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72960219502493045286058355 109440329253739567929087533)
        ·
          refine ⟨41040123470152337973407825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109440329253739567929087533 41040123470152337973407825)
          ·
            refine ⟨30780092602614253480055869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41040123470152337973407825 30780092602614253480055869)
            ·
              refine ⟨11542534725980345055020951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30780092602614253480055869 11542534725980345055020951)
              ·
                refine ⟨17313802088970517582531427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11542534725980345055020951 17313802088970517582531427)
                ·
                  refine ⟨25970703133455776373797141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17313802088970517582531427 25970703133455776373797141)
                  ·
                    refine ⟨1217376709380739517521741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25970703133455776373797141 1217376709380739517521741)
                    ·
                      rfl

theorem cell23_7112498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_7112498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112498 prefixEnd_7112498 := by exact prefixLift 7112498
  have htrace : WordTrace (prefixWord ++ tailWord_7112498) baseStart_7112498 baseEnd_7112498 := by
    simpa [prefixWord, tailWord_7112498, baseEnd_7112498] using wordTrace_append hprefix tailTrace_7112498
  have hstable : (prefixWord ++ tailWord_7112498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112498).length < 2 ^ (prefixWord ++ tailWord_7112498).sum := by decide
  have hdescent : baseEnd_7112498 < baseStart_7112498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112502 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_7112502 : Nat := 118140960795 + 7112502 * 2 ^ 59
def prefixEnd_7112502 : Nat := 4983230072969 + 3 ^ 40 * 7112502 * 2
def baseEnd_7112502 : Nat := 1217377394021612178971735

theorem tailTrace_7112502 : CollatzResearch.WordTrace tailWord_7112502 prefixEnd_7112502 1217377394021612178971735 := by
  unfold tailWord_7112502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16213391229914215467376235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172942839785751631652013173 16213391229914215467376235)
  ·
    refine ⟨24320086844871323201064353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16213391229914215467376235 24320086844871323201064353)
    ·
      refine ⟨18240065133653492400798265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24320086844871323201064353 18240065133653492400798265)
      ·
        refine ⟨13680048850240119300598699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18240065133653492400798265 13680048850240119300598699)
        ·
          refine ⟨20520073275360178950898049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13680048850240119300598699 20520073275360178950898049)
          ·
            refine ⟨15390054956520134213173537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20520073275360178950898049 15390054956520134213173537)
            ·
              refine ⟨11542541217390100659880153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15390054956520134213173537 11542541217390100659880153)
              ·
                refine ⟨8656905913042575494910115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11542541217390100659880153 8656905913042575494910115)
                ·
                  refine ⟨12985358869563863242365173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8656905913042575494910115 12985358869563863242365173)
                  ·
                    refine ⟨1217377394021612178971735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12985358869563863242365173 1217377394021612178971735)
                    ·
                      rfl

theorem cell23_7112502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_7112502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112502 prefixEnd_7112502 := by exact prefixLift 7112502
  have htrace : WordTrace (prefixWord ++ tailWord_7112502) baseStart_7112502 baseEnd_7112502 := by
    simpa [prefixWord, tailWord_7112502, baseEnd_7112502] using wordTrace_append hprefix tailTrace_7112502
  have hstable : (prefixWord ++ tailWord_7112502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112502).length < 2 ^ (prefixWord ++ tailWord_7112502).sum := by decide
  have hdescent : baseEnd_7112502 < baseStart_7112502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112508 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_7112508 : Nat := 118140960795 + 7112508 * 2 ^ 59
def prefixEnd_7112508 : Nat := 4983230072969 + 3 ^ 40 * 7112508 * 2
def baseEnd_7112508 : Nat := 3652135262948763513440177

theorem tailTrace_7112508 : CollatzResearch.WordTrace tailWord_7112508 prefixEnd_7112508 3652135262948763513440177 := by
  unfold tailWord_7112508
  simp only [CollatzResearch.WordTrace]
  refine ⟨129707239258302855251369089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172942985677737140335158785 129707239258302855251369089)
  ·
    refine ⟨97280429443727141438526817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129707239258302855251369089 97280429443727141438526817)
    ·
      refine ⟨72960322082795356078895113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97280429443727141438526817 72960322082795356078895113)
      ·
        refine ⟨54720241562096517059171335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72960322082795356078895113 54720241562096517059171335)
        ·
          refine ⟨82080362343144775588757003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54720241562096517059171335 82080362343144775588757003)
          ·
            refine ⟨123120543514717163383135505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82080362343144775588757003 123120543514717163383135505)
            ·
              refine ⟨92340407636037872537351629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123120543514717163383135505 92340407636037872537351629)
              ·
                refine ⟨34627652863514202201506861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92340407636037872537351629 34627652863514202201506861)
                ·
                  refine ⟨12985369823817825825565073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34627652863514202201506861 12985369823817825825565073)
                  ·
                    refine ⟨9739027367863369369173805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12985369823817825825565073 9739027367863369369173805)
                    ·
                      refine ⟨3652135262948763513440177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9739027367863369369173805 3652135262948763513440177)
                      ·
                        rfl

theorem cell23_7112508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_7112508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112508 prefixEnd_7112508 := by exact prefixLift 7112508
  have htrace : WordTrace (prefixWord ++ tailWord_7112508) baseStart_7112508 baseEnd_7112508 := by
    simpa [prefixWord, tailWord_7112508, baseEnd_7112508] using wordTrace_append hprefix tailTrace_7112508
  have hstable : (prefixWord ++ tailWord_7112508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112508).length < 2 ^ (prefixWord ++ tailWord_7112508).sum := by decide
  have hdescent : baseEnd_7112508 < baseStart_7112508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112525 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7112525 : Nat := 118140960795 + 7112525 * 2 ^ 59
def prefixEnd_7112525 : Nat := 4983230072969 + 3 ^ 40 * 7112525 * 2
def baseEnd_7112525 : Nat := 3652143992119889946927599

theorem tailTrace_7112525 : CollatzResearch.WordTrace tailWord_7112525 prefixEnd_7112525 3652143992119889946927599 := by
  unfold tailWord_7112525
  simp only [CollatzResearch.WordTrace]
  refine ⟨259415098557544122406107029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172943399038362748270738019 259415098557544122406107029)
  ·
    refine ⟨12160082744884880737786267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 259415098557544122406107029 12160082744884880737786267)
    ·
      refine ⟨18240124117327321106679401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12160082744884880737786267 18240124117327321106679401)
      ·
        refine ⟨13680093087995490830009551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18240124117327321106679401 13680093087995490830009551)
        ·
          refine ⟨20520139631993236245014327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13680093087995490830009551 20520139631993236245014327)
          ·
            refine ⟨30780209447989854367521491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20520139631993236245014327 30780209447989854367521491)
            ·
              refine ⟨46170314171984781551282237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30780209447989854367521491 46170314171984781551282237)
              ·
                refine ⟨17313867814494293081730839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46170314171984781551282237 17313867814494293081730839)
                ·
                  refine ⟨25970801721741439622596259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17313867814494293081730839 25970801721741439622596259)
                  ·
                    refine ⟨38956202582612159433894389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25970801721741439622596259 38956202582612159433894389)
                    ·
                      refine ⟨3652143992119889946927599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38956202582612159433894389 3652143992119889946927599)
                      ·
                        rfl

theorem cell23_7112525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7112525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112525 prefixEnd_7112525 := by exact prefixLift 7112525
  have htrace : WordTrace (prefixWord ++ tailWord_7112525) baseStart_7112525 baseEnd_7112525 := by
    simpa [prefixWord, tailWord_7112525, baseEnd_7112525] using wordTrace_append hprefix tailTrace_7112525
  have hstable : (prefixWord ++ tailWord_7112525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112525).length < 2 ^ (prefixWord ++ tailWord_7112525).sum := by decide
  have hdescent : baseEnd_7112525 < baseStart_7112525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112571 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 4, 6]
def baseStart_7112571 : Nat := 118140960795 + 7112571 * 2 ^ 59
def prefixEnd_7112571 : Nat := 4983230072969 + 3 ^ 40 * 7112571 * 2
def baseEnd_7112571 : Nat := 1217389204076665588984129

theorem tailTrace_7112571 : CollatzResearch.WordTrace tailWord_7112571 prefixEnd_7112571 1217389204076665588984129 := by
  unfold tailWord_7112571
  simp only [CollatzResearch.WordTrace]
  refine ⟨259416776315377472262281567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172944517543584981508187711 259416776315377472262281567)
  ·
    refine ⟨389125164473066208393422351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259416776315377472262281567 389125164473066208393422351)
    ·
      refine ⟨583687746709599312590133527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389125164473066208393422351 583687746709599312590133527)
      ·
        refine ⟨875531620064398968885200291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583687746709599312590133527 875531620064398968885200291)
        ·
          refine ⟨1313297430096598453327800437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875531620064398968885200291 1313297430096598453327800437)
          ·
            refine ⟨123121634071556104999481291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1313297430096598453327800437 123121634071556104999481291)
            ·
              refine ⟨184682451107334157499221937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123121634071556104999481291 184682451107334157499221937)
              ·
                refine ⟨138511838330500618124416453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184682451107334157499221937 138511838330500618124416453)
                ·
                  refine ⟨25970969686968865898328085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138511838330500618124416453 25970969686968865898328085)
                  ·
                    refine ⟨1217389204076665588984129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25970969686968865898328085 1217389204076665588984129)
                    ·
                      rfl

theorem cell23_7112571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 6].length) (baseStart_7112571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112571 prefixEnd_7112571 := by exact prefixLift 7112571
  have htrace : WordTrace (prefixWord ++ tailWord_7112571) baseStart_7112571 baseEnd_7112571 := by
    simpa [prefixWord, tailWord_7112571, baseEnd_7112571] using wordTrace_append hprefix tailTrace_7112571
  have hstable : (prefixWord ++ tailWord_7112571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112571).length < 2 ^ (prefixWord ++ tailWord_7112571).sum := by decide
  have hdescent : baseEnd_7112571 < baseStart_7112571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112590 : List Nat := [4, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7112590 : Nat := 118140960795 + 7112590 * 2 ^ 59
def prefixEnd_7112590 : Nat := 4983230072969 + 3 ^ 40 * 7112590 * 2
def baseEnd_7112590 : Nat := 3652177368362432192614801

theorem tailTrace_7112590 : CollatzResearch.WordTrace tailWord_7112590 prefixEnd_7112590 3652177368362432192614801 := by
  unfold tailWord_7112590
  simp only [CollatzResearch.WordTrace]
  refine ⟨32427183662788579813402903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172944979534872425671482149 32427183662788579813402903)
  ·
    refine ⟨48640775494182869720104355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32427183662788579813402903 48640775494182869720104355)
    ·
      refine ⟨72961163241274304580156533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48640775494182869720104355 72961163241274304580156533)
      ·
        refine ⟨6840109053869466054389675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72961163241274304580156533 6840109053869466054389675)
        ·
          refine ⟨10260163580804199081584513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840109053869466054389675 10260163580804199081584513)
          ·
            refine ⟨7695122685603149311188385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10260163580804199081584513 7695122685603149311188385)
            ·
              refine ⟨5771342014202361983391289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7695122685603149311188385 5771342014202361983391289)
              ·
                refine ⟨4328506510651771487543467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5771342014202361983391289 4328506510651771487543467)
                ·
                  refine ⟨6492759765977657231315201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4328506510651771487543467 6492759765977657231315201)
                  ·
                    refine ⟨4869569824483242923486401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6492759765977657231315201 4869569824483242923486401)
                    ·
                      refine ⟨3652177368362432192614801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4869569824483242923486401 3652177368362432192614801)
                      ·
                        rfl

theorem cell23_7112590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7112590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112590 prefixEnd_7112590 := by exact prefixLift 7112590
  have htrace : WordTrace (prefixWord ++ tailWord_7112590) baseStart_7112590 baseEnd_7112590 := by
    simpa [prefixWord, tailWord_7112590, baseEnd_7112590] using wordTrace_append hprefix tailTrace_7112590
  have hstable : (prefixWord ++ tailWord_7112590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112590).length < 2 ^ (prefixWord ++ tailWord_7112590).sum := by decide
  have hdescent : baseEnd_7112590 < baseStart_7112590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112595 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 8, 2, 2]
def baseStart_7112595 : Nat := 118140960795 + 7112595 * 2 ^ 59
def prefixEnd_7112595 : Nat := 4983230072969 + 3 ^ 40 * 7112595 * 2
def baseEnd_7112595 : Nat := 3652179935765704673052277

theorem tailTrace_7112595 : CollatzResearch.WordTrace tailWord_7112595 prefixEnd_7112595 3652179935765704673052277 := by
  unfold tailWord_7112595
  simp only [CollatzResearch.WordTrace]
  refine ⟨259417651667290524361155239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172945101111527016240770159 259417651667290524361155239)
  ·
    refine ⟨389126477500935786541732859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259417651667290524361155239 389126477500935786541732859)
    ·
      refine ⟨583689716251403679812599289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389126477500935786541732859 583689716251403679812599289)
      ·
        refine ⟨437767287188552759859449467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583689716251403679812599289 437767287188552759859449467)
        ·
          refine ⟨656650930782829139789174201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437767287188552759859449467 656650930782829139789174201)
          ·
            refine ⟨492488198087121854841880651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656650930782829139789174201 492488198087121854841880651)
            ·
              refine ⟨738732297130682782262820977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492488198087121854841880651 738732297130682782262820977)
              ·
                refine ⟨554049222848012086697115733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738732297130682782262820977 554049222848012086697115733)
                ·
                  refine ⟨6492764330250141640981825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 554049222848012086697115733 6492764330250141640981825)
                  ·
                    refine ⟨4869573247687606230736369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6492764330250141640981825 4869573247687606230736369)
                    ·
                      refine ⟨3652179935765704673052277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4869573247687606230736369 3652179935765704673052277)
                      ·
                        rfl

theorem cell23_7112595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 2, 2].length) (baseStart_7112595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112595 prefixEnd_7112595 := by exact prefixLift 7112595
  have htrace : WordTrace (prefixWord ++ tailWord_7112595) baseStart_7112595 baseEnd_7112595 := by
    simpa [prefixWord, tailWord_7112595, baseEnd_7112595] using wordTrace_append hprefix tailTrace_7112595
  have hstable : (prefixWord ++ tailWord_7112595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112595).length < 2 ^ (prefixWord ++ tailWord_7112595).sum := by decide
  have hdescent : baseEnd_7112595 < baseStart_7112595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112612 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 1, 4, 2]
def baseStart_7112612 : Nat := 118140960795 + 7112612 * 2 ^ 59
def prefixEnd_7112612 : Nat := 4983230072969 + 3 ^ 40 * 7112612 * 2
def baseEnd_7112612 : Nat := 3652188664936831106539699

theorem tailTrace_7112612 : CollatzResearch.WordTrace tailWord_7112612 prefixEnd_7112612 3652188664936831106539699 := by
  unfold tailWord_7112612
  simp only [CollatzResearch.WordTrace]
  refine ⟨129709135854114468132262045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172945514472152624176349393 129709135854114468132262045)
  ·
    refine ⟨48640925945292925549598267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129709135854114468132262045 48640925945292925549598267)
    ·
      refine ⟨72961388917939388324397401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48640925945292925549598267 72961388917939388324397401)
      ·
        refine ⟨54721041688454541243298051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72961388917939388324397401 54721041688454541243298051)
        ·
          refine ⟨82081562532681811864947077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54721041688454541243298051 82081562532681811864947077)
          ·
            refine ⟨15390292974877839724677577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82081562532681811864947077 15390292974877839724677577)
            ·
              refine ⟨11542719731158379793508183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15390292974877839724677577 11542719731158379793508183)
              ·
                refine ⟨17314079596737569690262275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11542719731158379793508183 17314079596737569690262275)
                ·
                  refine ⟨25971119395106354535393413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17314079596737569690262275 25971119395106354535393413)
                  ·
                    refine ⟨4869584886582441475386265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25971119395106354535393413 4869584886582441475386265)
                    ·
                      refine ⟨3652188664936831106539699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4869584886582441475386265 3652188664936831106539699)
                      ·
                        rfl

theorem cell23_7112612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_7112612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112612 prefixEnd_7112612 := by exact prefixLift 7112612
  have htrace : WordTrace (prefixWord ++ tailWord_7112612) baseStart_7112612 baseEnd_7112612 := by
    simpa [prefixWord, tailWord_7112612, baseEnd_7112612] using wordTrace_append hprefix tailTrace_7112612
  have hstable : (prefixWord ++ tailWord_7112612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112612).length < 2 ^ (prefixWord ++ tailWord_7112612).sum := by decide
  have hdescent : baseEnd_7112612 < baseStart_7112612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112702 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7112702 : Nat := 118140960795 + 7112702 * 2 ^ 59
def prefixEnd_7112702 : Nat := 4983230072969 + 3 ^ 40 * 7112702 * 2
def baseEnd_7112702 : Nat := 3652234878195735754414285

theorem tailTrace_7112702 : CollatzResearch.WordTrace tailWord_7112702 prefixEnd_7112702 3652234878195735754414285 := by
  unfold tailWord_7112702
  simp only [CollatzResearch.WordTrace]
  refine ⟨32427694284737860204412545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172947702851935254423533573 32427694284737860204412545)
  ·
    refine ⟨24320770713553395153309409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32427694284737860204412545 24320770713553395153309409)
    ·
      refine ⟨18240578035165046364982057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24320770713553395153309409 18240578035165046364982057)
      ·
        refine ⟨13680433526373784773736543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18240578035165046364982057 13680433526373784773736543)
        ·
          refine ⟨20520650289560677160604815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13680433526373784773736543 20520650289560677160604815)
          ·
            refine ⟨30780975434341015740907223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20520650289560677160604815 30780975434341015740907223)
            ·
              refine ⟨46171463151511523611360835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30780975434341015740907223 46171463151511523611360835)
              ·
                refine ⟨69257194727267285417041253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46171463151511523611360835 69257194727267285417041253)
                ·
                  refine ⟨12985724011362616015695235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69257194727267285417041253 12985724011362616015695235)
                  ·
                    refine ⟨19478586017043924023542853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12985724011362616015695235 19478586017043924023542853)
                    ·
                      refine ⟨3652234878195735754414285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19478586017043924023542853 3652234878195735754414285)
                      ·
                        rfl

theorem cell23_7112702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7112702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112702 prefixEnd_7112702 := by exact prefixLift 7112702
  have htrace : WordTrace (prefixWord ++ tailWord_7112702) baseStart_7112702 baseEnd_7112702 := by
    simpa [prefixWord, tailWord_7112702, baseEnd_7112702] using wordTrace_append hprefix tailTrace_7112702
  have hstable : (prefixWord ++ tailWord_7112702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112702).length < 2 ^ (prefixWord ++ tailWord_7112702).sum := by decide
  have hdescent : baseEnd_7112702 < baseStart_7112702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112745 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 7, 5, 2]
def baseStart_7112745 : Nat := 118140960795 + 7112745 * 2 ^ 59
def prefixEnd_7112745 : Nat := 4983230072969 + 3 ^ 40 * 7112745 * 2
def baseEnd_7112745 : Nat := 3652256957863879086176587

theorem tailTrace_7112745 : CollatzResearch.WordTrace tailWord_7112745 prefixEnd_7112745 3652256957863879086176587 := by
  unfold tailWord_7112745
  simp only [CollatzResearch.WordTrace]
  refine ⟨259423122616747099979115689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172948748411164733319410459 259423122616747099979115689)
  ·
    refine ⟨194567341962560324984336767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259423122616747099979115689 194567341962560324984336767)
    ·
      refine ⟨291851012943840487476505151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194567341962560324984336767 291851012943840487476505151)
      ·
        refine ⟨437776519415760731214757727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291851012943840487476505151 437776519415760731214757727)
        ·
          refine ⟨656664779123641096822136591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437776519415760731214757727 656664779123641096822136591)
          ·
            refine ⟨984997168685461645233204887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656664779123641096822136591 984997168685461645233204887)
            ·
              refine ⟨1477495753028192467849807331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984997168685461645233204887 1477495753028192467849807331)
              ·
                refine ⟨2216243629542288701774710997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477495753028192467849807331 2216243629542288701774710997)
                ·
                  refine ⟨51943210067397391447844789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2216243629542288701774710997 51943210067397391447844789)
                  ·
                    refine ⟨4869675943818505448235449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51943210067397391447844789 4869675943818505448235449)
                    ·
                      refine ⟨3652256957863879086176587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4869675943818505448235449 3652256957863879086176587)
                      ·
                        rfl

theorem cell23_7112745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 5, 2].length) (baseStart_7112745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112745 prefixEnd_7112745 := by exact prefixLift 7112745
  have htrace : WordTrace (prefixWord ++ tailWord_7112745) baseStart_7112745 baseEnd_7112745 := by
    simpa [prefixWord, tailWord_7112745, baseEnd_7112745] using wordTrace_append hprefix tailTrace_7112745
  have hstable : (prefixWord ++ tailWord_7112745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112745).length < 2 ^ (prefixWord ++ tailWord_7112745).sum := by decide
  have hdescent : baseEnd_7112745 < baseStart_7112745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112748 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_7112748 : Nat := 118140960795 + 7112748 * 2 ^ 59
def prefixEnd_7112748 : Nat := 4983230072969 + 3 ^ 40 * 7112748 * 2
def baseEnd_7112748 : Nat := 3652258498305842574439073

theorem tailTrace_7112748 : CollatzResearch.WordTrace tailWord_7112748 prefixEnd_7112748 3652258498305842574439073 := by
  unfold tailWord_7112748
  simp only [CollatzResearch.WordTrace]
  refine ⟨129711616017868115745737449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172948821357157487660983265 129711616017868115745737449)
  ·
    refine ⟨97283712013401086809303087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129711616017868115745737449 97283712013401086809303087)
    ·
      refine ⟨145925568020101630213954631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97283712013401086809303087 145925568020101630213954631)
      ·
        refine ⟨218888352030152445320931947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145925568020101630213954631 218888352030152445320931947)
        ·
          refine ⟨328332528045228667981397921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218888352030152445320931947 328332528045228667981397921)
          ·
            refine ⟨246249396033921500986048441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328332528045228667981397921 246249396033921500986048441)
            ·
              refine ⟨184687047025441125739536331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246249396033921500986048441 184687047025441125739536331)
              ·
                refine ⟨277030570538161688609304497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184687047025441125739536331 277030570538161688609304497)
                ·
                  refine ⟨207772927903621266456978373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277030570538161688609304497 207772927903621266456978373)
                  ·
                    refine ⟨38957423981928987460683445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207772927903621266456978373 38957423981928987460683445)
                    ·
                      refine ⟨3652258498305842574439073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38957423981928987460683445 3652258498305842574439073)
                      ·
                        rfl

theorem cell23_7112748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_7112748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112748 prefixEnd_7112748 := by exact prefixLift 7112748
  have htrace : WordTrace (prefixWord ++ tailWord_7112748) baseStart_7112748 baseEnd_7112748 := by
    simpa [prefixWord, tailWord_7112748, baseEnd_7112748] using wordTrace_append hprefix tailTrace_7112748
  have hstable : (prefixWord ++ tailWord_7112748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112748).length < 2 ^ (prefixWord ++ tailWord_7112748).sum := by decide
  have hdescent : baseEnd_7112748 < baseStart_7112748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112755 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 1, 5]
def baseStart_7112755 : Nat := 118140960795 + 7112755 * 2 ^ 59
def prefixEnd_7112755 : Nat := 4983230072969 + 3 ^ 40 * 7112755 * 2
def baseEnd_7112755 : Nat := 1217420697556808015683847

theorem tailTrace_7112755 : CollatzResearch.WordTrace tailWord_7112755 prefixEnd_7112755 1217420697556808015683847 := by
  unfold tailWord_7112755
  simp only [CollatzResearch.WordTrace]
  refine ⟨259423487346710871686979719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172948991564473914457986479 259423487346710871686979719)
  ·
    refine ⟨389135231020066307530469579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259423487346710871686979719 389135231020066307530469579)
    ·
      refine ⟨583702846530099461295704369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389135231020066307530469579 583702846530099461295704369)
      ·
        refine ⟨437777134897574595971778277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583702846530099461295704369 437777134897574595971778277)
        ·
          refine ⟨82083212793295236744708427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 437777134897574595971778277 82083212793295236744708427)
          ·
            refine ⟨123124819189942855117062641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82083212793295236744708427 123124819189942855117062641)
            ·
              refine ⟨92343614392457141337796981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123124819189942855117062641 92343614392457141337796981)
              ·
                refine ⟨8657213849292857000418467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92343614392457141337796981 8657213849292857000418467)
                ·
                  refine ⟨12985820773939285500627701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8657213849292857000418467 12985820773939285500627701)
                  ·
                    refine ⟨1217420697556808015683847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12985820773939285500627701 1217420697556808015683847)
                    ·
                      rfl

theorem cell23_7112755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 5].length) (baseStart_7112755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112755 prefixEnd_7112755 := by exact prefixLift 7112755
  have htrace : WordTrace (prefixWord ++ tailWord_7112755) baseStart_7112755 baseEnd_7112755 := by
    simpa [prefixWord, tailWord_7112755, baseEnd_7112755] using wordTrace_append hprefix tailTrace_7112755
  have hstable : (prefixWord ++ tailWord_7112755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112755).length < 2 ^ (prefixWord ++ tailWord_7112755).sum := by decide
  have hdescent : baseEnd_7112755 < baseStart_7112755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112775 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_7112775 : Nat := 118140960795 + 7112775 * 2 ^ 59
def prefixEnd_7112775 : Nat := 4983230072969 + 3 ^ 40 * 7112775 * 2
def baseEnd_7112775 : Nat := 3652272362283513968801449

theorem tailTrace_7112775 : CollatzResearch.WordTrace tailWord_7112775 prefixEnd_7112775 3652272362283513968801449 := by
  unfold tailWord_7112775
  simp only [CollatzResearch.WordTrace]
  refine ⟨259424216806638415102707779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172949477871092276735138519 259424216806638415102707779)
  ·
    refine ⟨389136325209957622654061669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259424216806638415102707779 389136325209957622654061669)
    ·
      refine ⟨72963060976867054247636563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389136325209957622654061669 72963060976867054247636563)
      ·
        refine ⟨109444591465300581371454845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72963060976867054247636563 109444591465300581371454845)
        ·
          refine ⟨41041721799487718014295567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109444591465300581371454845 41041721799487718014295567)
          ·
            refine ⟨61562582699231577021443351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41041721799487718014295567 61562582699231577021443351)
            ·
              refine ⟨92343874048847365532165027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61562582699231577021443351 92343874048847365532165027)
              ·
                refine ⟨138515811073271048298247541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92343874048847365532165027 138515811073271048298247541)
                ·
                  refine ⟨12985857288119160777960707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138515811073271048298247541 12985857288119160777960707)
                  ·
                    refine ⟨19478785932178741166941061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12985857288119160777960707 19478785932178741166941061)
                    ·
                      refine ⟨3652272362283513968801449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19478785932178741166941061 3652272362283513968801449)
                      ·
                        rfl

theorem cell23_7112775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_7112775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112775 prefixEnd_7112775 := by exact prefixLift 7112775
  have htrace : WordTrace (prefixWord ++ tailWord_7112775) baseStart_7112775 baseEnd_7112775 := by
    simpa [prefixWord, tailWord_7112775, baseEnd_7112775] using wordTrace_append hprefix tailTrace_7112775
  have hstable : (prefixWord ++ tailWord_7112775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112775).length < 2 ^ (prefixWord ++ tailWord_7112775).sum := by decide
  have hdescent : baseEnd_7112775 < baseStart_7112775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112785 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 6, 4]
def baseStart_7112785 : Nat := 118140960795 + 7112785 * 2 ^ 59
def prefixEnd_7112785 : Nat := 4983230072969 + 3 ^ 40 * 7112785 * 2
def baseEnd_7112785 : Nat := 1217425832363352976558801

theorem tailTrace_7112785 : CollatzResearch.WordTrace tailWord_7112785 prefixEnd_7112785 1217425832363352976558801 := by
  unfold tailWord_7112785
  simp only [CollatzResearch.WordTrace]
  refine ⟨259424581536602186810571809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172949721024401457873714539 259424581536602186810571809)
  ·
    refine ⟨194568436152451640107928857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259424581536602186810571809 194568436152451640107928857)
    ·
      refine ⟨145926327114338730080946643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194568436152451640107928857 145926327114338730080946643)
      ·
        refine ⟨218889490671508095121419965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145926327114338730080946643 218889490671508095121419965)
        ·
          refine ⟨82083559001815535670532487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218889490671508095121419965 82083559001815535670532487)
          ·
            refine ⟨123125338502723303505798731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82083559001815535670532487 123125338502723303505798731)
            ·
              refine ⟨184688007754084955258698097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123125338502723303505798731 184688007754084955258698097)
              ·
                refine ⟨138516005815563716444023573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184688007754084955258698097 138516005815563716444023573)
                ·
                  refine ⟨6492937772604549208313605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138516005815563716444023573 6492937772604549208313605)
                  ·
                    refine ⟨1217425832363352976558801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6492937772604549208313605 1217425832363352976558801)
                    ·
                      rfl

theorem cell23_7112785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_7112785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112785 prefixEnd_7112785 := by exact prefixLift 7112785
  have htrace : WordTrace (prefixWord ++ tailWord_7112785) baseStart_7112785 baseEnd_7112785 := by
    simpa [prefixWord, tailWord_7112785, baseEnd_7112785] using wordTrace_append hprefix tailTrace_7112785
  have hstable : (prefixWord ++ tailWord_7112785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112785).length < 2 ^ (prefixWord ++ tailWord_7112785).sum := by decide
  have hdescent : baseEnd_7112785 < baseStart_7112785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112796 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_7112796 : Nat := 118140960795 + 7112796 * 2 ^ 59
def prefixEnd_7112796 : Nat := 4983230072969 + 3 ^ 40 * 7112796 * 2
def baseEnd_7112796 : Nat := 3652283145377258386638853

theorem tailTrace_7112796 : CollatzResearch.WordTrace tailWord_7112796 prefixEnd_7112796 3652283145377258386638853 := by
  unfold tailWord_7112796
  simp only [CollatzResearch.WordTrace]
  refine ⟨129712491369781167844611121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172949988493041557126148161 129712491369781167844611121)
  ·
    refine ⟨97284368527335875883458341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129712491369781167844611121 97284368527335875883458341)
    ·
      refine ⟨18240819098875476728148439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97284368527335875883458341 18240819098875476728148439)
      ·
        refine ⟨27361228648313215092222659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18240819098875476728148439 27361228648313215092222659)
        ·
          refine ⟨41041842972469822638333989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27361228648313215092222659 41041842972469822638333989)
          ·
            refine ⟨7695345557338091744687623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41041842972469822638333989 7695345557338091744687623)
            ·
              refine ⟨11543018336007137617031435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7695345557338091744687623 11543018336007137617031435)
              ·
                refine ⟨17314527504010706425547153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11543018336007137617031435 17314527504010706425547153)
                ·
                  refine ⟨12985895628008029819160365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17314527504010706425547153 12985895628008029819160365)
                  ·
                    refine ⟨4869710860503011182185137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12985895628008029819160365 4869710860503011182185137)
                    ·
                      refine ⟨3652283145377258386638853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4869710860503011182185137 3652283145377258386638853)
                      ·
                        rfl

theorem cell23_7112796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_7112796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112796 prefixEnd_7112796 := by exact prefixLift 7112796
  have htrace : WordTrace (prefixWord ++ tailWord_7112796) baseStart_7112796 baseEnd_7112796 := by
    simpa [prefixWord, tailWord_7112796, baseEnd_7112796] using wordTrace_append hprefix tailTrace_7112796
  have hstable : (prefixWord ++ tailWord_7112796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112796).length < 2 ^ (prefixWord ++ tailWord_7112796).sum := by decide
  have hdescent : baseEnd_7112796 < baseStart_7112796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112846 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_7112846 : Nat := 118140960795 + 7112846 * 2 ^ 59
def prefixEnd_7112846 : Nat := 4983230072969 + 3 ^ 40 * 7112846 * 2
def baseEnd_7112846 : Nat := 3652308819409983191013623

theorem tailTrace_7112846 : CollatzResearch.WordTrace tailWord_7112846 prefixEnd_7112846 3652308819409983191013623 := by
  unfold tailWord_7112846
  simp only [CollatzResearch.WordTrace]
  refine ⟨32428350798672649278567799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172951204259587462819028261 32428350798672649278567799)
  ·
    refine ⟨48642526198008973917851699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32428350798672649278567799 48642526198008973917851699)
    ·
      refine ⟨72963789297013460876777549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48642526198008973917851699 72963789297013460876777549)
      ·
        refine ⟨27361420986380047828791581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72963789297013460876777549 27361420986380047828791581)
        ·
          refine ⟨10260532869892517935796843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27361420986380047828791581 10260532869892517935796843)
          ·
            refine ⟨15390799304838776903695265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10260532869892517935796843 15390799304838776903695265)
            ·
              refine ⟨11543099478629082677771449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15390799304838776903695265 11543099478629082677771449)
              ·
                refine ⟨8657324608971812008328587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11543099478629082677771449 8657324608971812008328587)
                ·
                  refine ⟨12985986913457718012492881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8657324608971812008328587 12985986913457718012492881)
                  ·
                    refine ⟨9739490185093288509369661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12985986913457718012492881 9739490185093288509369661)
                    ·
                      refine ⟨3652308819409983191013623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9739490185093288509369661 3652308819409983191013623)
                      ·
                        rfl

theorem cell23_7112846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_7112846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112846 prefixEnd_7112846 := by exact prefixLift 7112846
  have htrace : WordTrace (prefixWord ++ tailWord_7112846) baseStart_7112846 baseEnd_7112846 := by
    simpa [prefixWord, tailWord_7112846, baseEnd_7112846] using wordTrace_append hprefix tailTrace_7112846
  have hstable : (prefixWord ++ tailWord_7112846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112846).length < 2 ^ (prefixWord ++ tailWord_7112846).sum := by decide
  have hdescent : baseEnd_7112846 < baseStart_7112846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112869 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 1, 3, 2]
def baseStart_7112869 : Nat := 118140960795 + 7112869 * 2 ^ 59
def prefixEnd_7112869 : Nat := 4983230072969 + 3 ^ 40 * 7112869 * 2
def baseEnd_7112869 : Nat := 3652320629465036601026017

theorem tailTrace_7112869 : CollatzResearch.WordTrace tailWord_7112869 prefixEnd_7112869 3652320629465036601026017 := by
  unfold tailWord_7112869
  simp only [CollatzResearch.WordTrace]
  refine ⟨259427645268297869156629661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172951763512198579437753107 259427645268297869156629661)
  ·
    refine ⟨97285366975611700933736123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259427645268297869156629661 97285366975611700933736123)
    ·
      refine ⟨145928050463417551400604185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97285366975611700933736123 145928050463417551400604185)
      ·
        refine ⟨109446037847563163550453139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145928050463417551400604185 109446037847563163550453139)
        ·
          refine ⟨164169056771344745325679709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109446037847563163550453139 164169056771344745325679709)
          ·
            refine ⟨61563396289254279497129891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164169056771344745325679709 61563396289254279497129891)
            ·
              refine ⟨92345094433881419245694837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61563396289254279497129891 92345094433881419245694837)
              ·
                refine ⟨8657352603176383054283891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92345094433881419245694837 8657352603176383054283891)
                ·
                  refine ⟨12986028904764574581425837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8657352603176383054283891 12986028904764574581425837)
                  ·
                    refine ⟨4869760839286715468034689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12986028904764574581425837 4869760839286715468034689)
                    ·
                      refine ⟨3652320629465036601026017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4869760839286715468034689 3652320629465036601026017)
                      ·
                        rfl

theorem cell23_7112869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_7112869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112869 prefixEnd_7112869 := by exact prefixLift 7112869
  have htrace : WordTrace (prefixWord ++ tailWord_7112869) baseStart_7112869 baseEnd_7112869 := by
    simpa [prefixWord, tailWord_7112869, baseEnd_7112869] using wordTrace_append hprefix tailTrace_7112869
  have hstable : (prefixWord ++ tailWord_7112869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112869).length < 2 ^ (prefixWord ++ tailWord_7112869).sum := by decide
  have hdescent : baseEnd_7112869 < baseStart_7112869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112895 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 4]
def baseStart_7112895 : Nat := 118140960795 + 7112895 * 2 ^ 59
def prefixEnd_7112895 : Nat := 4983230072969 + 3 ^ 40 * 7112895 * 2
def baseEnd_7112895 : Nat := 3652333979962053499300897

theorem tailTrace_7112895 : CollatzResearch.WordTrace tailWord_7112895 prefixEnd_7112895 3652333979962053499300897 := by
  unfold tailWord_7112895
  simp only [CollatzResearch.WordTrace]
  refine ⟨259428593566203675597076139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172952395710802450398050759 259428593566203675597076139)
  ·
    refine ⟨389142890349305513395614209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259428593566203675597076139 389142890349305513395614209)
    ·
      refine ⟨291857167761979135046710657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389142890349305513395614209 291857167761979135046710657)
      ·
        refine ⟨218892875821484351285032993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291857167761979135046710657 218892875821484351285032993)
        ·
          refine ⟨164169656866113263463774745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218892875821484351285032993 164169656866113263463774745)
          ·
            refine ⟨123127242649584947597831059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164169656866113263463774745 123127242649584947597831059)
            ·
              refine ⟨184690863974377421396746589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123127242649584947597831059 184690863974377421396746589)
              ·
                refine ⟨69259073990391533023779971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184690863974377421396746589 69259073990391533023779971)
                ·
                  refine ⟨103888610985587299535669957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69259073990391533023779971 103888610985587299535669957)
                  ·
                    refine ⟨19479114559797618662938117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103888610985587299535669957 19479114559797618662938117)
                    ·
                      refine ⟨3652333979962053499300897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19479114559797618662938117 3652333979962053499300897)
                      ·
                        rfl

theorem cell23_7112895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_7112895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112895 prefixEnd_7112895 := by exact prefixLift 7112895
  have htrace : WordTrace (prefixWord ++ tailWord_7112895) baseStart_7112895 baseEnd_7112895 := by
    simpa [prefixWord, tailWord_7112895, baseEnd_7112895] using wordTrace_append hprefix tailTrace_7112895
  have hstable : (prefixWord ++ tailWord_7112895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112895).length < 2 ^ (prefixWord ++ tailWord_7112895).sum := by decide
  have hdescent : baseEnd_7112895 < baseStart_7112895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112932 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_7112932 : Nat := 118140960795 + 7112932 * 2 ^ 59
def prefixEnd_7112932 : Nat := 4983230072969 + 3 ^ 40 * 7112932 * 2
def baseEnd_7112932 : Nat := 3652352978746269854538227

theorem tailTrace_7112932 : CollatzResearch.WordTrace tailWord_7112932 prefixEnd_7112932 3652352978746269854538227 := by
  unfold tailWord_7112932
  simp only [CollatzResearch.WordTrace]
  refine ⟨129714971533534815458086525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172953295378046420610782033 129714971533534815458086525)
  ·
    refine ⟨48643114325075555796782447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129714971533534815458086525 48643114325075555796782447)
    ·
      refine ⟨72964671487613333695173671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48643114325075555796782447 72964671487613333695173671)
      ·
        refine ⟨109447007231420000542760507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72964671487613333695173671 109447007231420000542760507)
        ·
          refine ⟨164170510847130000814140761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109447007231420000542760507 164170510847130000814140761)
          ·
            refine ⟨123127883135347500610605571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164170510847130000814140761 123127883135347500610605571)
            ·
              refine ⟨184691824703021250915908357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123127883135347500610605571 184691824703021250915908357)
              ·
                refine ⟨34629717131816484546732817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184691824703021250915908357 34629717131816484546732817)
                ·
                  refine ⟨25972287848862363410049613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34629717131816484546732817 25972287848862363410049613)
                  ·
                    refine ⟨9739607943323386278768605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25972287848862363410049613 9739607943323386278768605)
                    ·
                      refine ⟨3652352978746269854538227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9739607943323386278768605 3652352978746269854538227)
                      ·
                        rfl

theorem cell23_7112932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_7112932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112932 prefixEnd_7112932 := by exact prefixLift 7112932
  have htrace : WordTrace (prefixWord ++ tailWord_7112932) baseStart_7112932 baseEnd_7112932 := by
    simpa [prefixWord, tailWord_7112932, baseEnd_7112932] using wordTrace_append hprefix tailTrace_7112932
  have hstable : (prefixWord ++ tailWord_7112932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112932).length < 2 ^ (prefixWord ++ tailWord_7112932).sum := by decide
  have hdescent : baseEnd_7112932 < baseStart_7112932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112933 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 2, 2, 2]
def baseStart_7112933 : Nat := 118140960795 + 7112933 * 2 ^ 59
def prefixEnd_7112933 : Nat := 4983230072969 + 3 ^ 40 * 7112933 * 2
def baseEnd_7112933 : Nat := 3652353492226924350625723

theorem tailTrace_7112933 : CollatzResearch.WordTrace tailWord_7112933 prefixEnd_7112933 3652353492226924350625723 := by
  unfold tailWord_7112933
  simp only [CollatzResearch.WordTrace]
  refine ⟨259429979540066008086959453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172953319693377338724639635 259429979540066008086959453)
  ·
    refine ⟨97286242327524753032609795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259429979540066008086959453 97286242327524753032609795)
    ·
      refine ⟨145929363491287129548914693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97286242327524753032609795 145929363491287129548914693)
      ·
        refine ⟨27361755654616336790421505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145929363491287129548914693 27361755654616336790421505)
        ·
          refine ⟨20521316740962252592816129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27361755654616336790421505 20521316740962252592816129)
          ·
            refine ⟨15390987555721689444612097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20521316740962252592816129 15390987555721689444612097)
            ·
              refine ⟨11543240666791267083459073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15390987555721689444612097 11543240666791267083459073)
              ·
                refine ⟨8657430500093450312594305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11543240666791267083459073 8657430500093450312594305)
                ·
                  refine ⟨6493072875070087734445729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8657430500093450312594305 6493072875070087734445729)
                  ·
                    refine ⟨4869804656302565800834297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6493072875070087734445729 4869804656302565800834297)
                    ·
                      refine ⟨3652353492226924350625723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4869804656302565800834297 3652353492226924350625723)
                      ·
                        rfl

theorem cell23_7112933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_7112933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112933 prefixEnd_7112933 := by exact prefixLift 7112933
  have htrace : WordTrace (prefixWord ++ tailWord_7112933) baseStart_7112933 baseEnd_7112933 := by
    simpa [prefixWord, tailWord_7112933, baseEnd_7112933] using wordTrace_append hprefix tailTrace_7112933
  have hstable : (prefixWord ++ tailWord_7112933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112933).length < 2 ^ (prefixWord ++ tailWord_7112933).sum := by decide
  have hdescent : baseEnd_7112933 < baseStart_7112933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112965 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_7112965 : Nat := 118140960795 + 7112965 * 2 ^ 59
def prefixEnd_7112965 : Nat := 4983230072969 + 3 ^ 40 * 7112965 * 2
def baseEnd_7112965 : Nat := 1217456641202622741808525

theorem tailTrace_7112965 : CollatzResearch.WordTrace tailWord_7112965 prefixEnd_7112965 1217456641202622741808525 := by
  unfold tailWord_7112965
  simp only [CollatzResearch.WordTrace]
  refine ⟨259431146675950077552124349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172954097783966718368082899 259431146675950077552124349)
  ·
    refine ⟨97286680003481279082046631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259431146675950077552124349 97286680003481279082046631)
    ·
      refine ⟨145930020005221918623069947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97286680003481279082046631 145930020005221918623069947)
      ·
        refine ⟨218895030007832877934604921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145930020005221918623069947 218895030007832877934604921)
        ·
          refine ⟨164171272505874658450953691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218895030007832877934604921 164171272505874658450953691)
          ·
            refine ⟨246256908758811987676430537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164171272505874658450953691 246256908758811987676430537)
            ·
              refine ⟨184692681569108990757322903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246256908758811987676430537 184692681569108990757322903)
              ·
                refine ⟨277039022353663486135984355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184692681569108990757322903 277039022353663486135984355)
                ·
                  refine ⟨415558533530495229203976533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277039022353663486135984355 415558533530495229203976533)
                  ·
                    refine ⟨1217456641202622741808525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 415558533530495229203976533 1217456641202622741808525)
                    ·
                      rfl

theorem cell23_7112965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_7112965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112965 prefixEnd_7112965 := by exact prefixLift 7112965
  have htrace : WordTrace (prefixWord ++ tailWord_7112965) baseStart_7112965 baseEnd_7112965 := by
    simpa [prefixWord, tailWord_7112965, baseEnd_7112965] using wordTrace_append hprefix tailTrace_7112965
  have hstable : (prefixWord ++ tailWord_7112965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112965).length < 2 ^ (prefixWord ++ tailWord_7112965).sum := by decide
  have hdescent : baseEnd_7112965 < baseStart_7112965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112969 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 2, 5]
def baseStart_7112969 : Nat := 118140960795 + 7112969 * 2 ^ 59
def prefixEnd_7112969 : Nat := 4983230072969 + 3 ^ 40 * 7112969 * 2
def baseEnd_7112969 : Nat := 1217457325843495403258519

theorem tailTrace_7112969 : CollatzResearch.WordTrace tailWord_7112969 prefixEnd_7112969 1217457325843495403258519 := by
  unfold tailWord_7112969
  simp only [CollatzResearch.WordTrace]
  refine ⟨259431292567935586235269961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172954195045290390823513307 259431292567935586235269961)
  ·
    refine ⟨194573469425951689676452471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259431292567935586235269961 194573469425951689676452471)
    ·
      refine ⟨291860204138927534514678707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194573469425951689676452471 291860204138927534514678707)
      ·
        refine ⟨437790306208391301772018061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291860204138927534514678707 437790306208391301772018061)
        ·
          refine ⟨164171364828146738164506773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437790306208391301772018061 164171364828146738164506773)
          ·
            refine ⟨7695532726319378351461255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164171364828146738164506773 7695532726319378351461255)
            ·
              refine ⟨11543299089479067527191883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7695532726319378351461255 11543299089479067527191883)
              ·
                refine ⟨17314948634218601290787825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11543299089479067527191883 17314948634218601290787825)
                ·
                  refine ⟨12986211475663950968090869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17314948634218601290787825 12986211475663950968090869)
                  ·
                    refine ⟨1217457325843495403258519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12986211475663950968090869 1217457325843495403258519)
                    ·
                      rfl

theorem cell23_7112969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 5].length) (baseStart_7112969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112969 prefixEnd_7112969 := by exact prefixLift 7112969
  have htrace : WordTrace (prefixWord ++ tailWord_7112969) baseStart_7112969 baseEnd_7112969 := by
    simpa [prefixWord, tailWord_7112969, baseEnd_7112969] using wordTrace_append hprefix tailTrace_7112969
  have hstable : (prefixWord ++ tailWord_7112969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112969).length < 2 ^ (prefixWord ++ tailWord_7112969).sum := by decide
  have hdescent : baseEnd_7112969 < baseStart_7112969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7112972 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_7112972 : Nat := 118140960795 + 7112972 * 2 ^ 59
def prefixEnd_7112972 : Nat := 4983230072969 + 3 ^ 40 * 7112972 * 2
def baseEnd_7112972 : Nat := 3652373517972449698038043

theorem tailTrace_7112972 : CollatzResearch.WordTrace tailWord_7112972 prefixEnd_7112972 3652373517972449698038043 := by
  unfold tailWord_7112972
  simp only [CollatzResearch.WordTrace]
  refine ⟨129715700993462358873814585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172954267991283145165086113 129715700993462358873814585)
  ·
    refine ⟨97286775745096769155360939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129715700993462358873814585 97286775745096769155360939)
    ·
      refine ⟨145930163617645153733041409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97286775745096769155360939 145930163617645153733041409)
      ·
        refine ⟨109447622713233865299781057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145930163617645153733041409 109447622713233865299781057)
        ·
          refine ⟨82085717034925398974835793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109447622713233865299781057 82085717034925398974835793)
          ·
            refine ⟨61564287776194049231126845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82085717034925398974835793 61564287776194049231126845)
            ·
              refine ⟨23086607916072768461672567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61564287776194049231126845 23086607916072768461672567)
              ·
                refine ⟨34629911874109152692508851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23086607916072768461672567 34629911874109152692508851)
                ·
                  refine ⟨51944867811163729038763277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34629911874109152692508851 51944867811163729038763277)
                  ·
                    refine ⟨19479325429186398389536229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51944867811163729038763277 19479325429186398389536229)
                    ·
                      refine ⟨3652373517972449698038043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19479325429186398389536229 3652373517972449698038043)
                      ·
                        rfl

theorem cell23_7112972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_7112972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7112972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7112972 prefixEnd_7112972 := by exact prefixLift 7112972
  have htrace : WordTrace (prefixWord ++ tailWord_7112972) baseStart_7112972 baseEnd_7112972 := by
    simpa [prefixWord, tailWord_7112972, baseEnd_7112972] using wordTrace_append hprefix tailTrace_7112972
  have hstable : (prefixWord ++ tailWord_7112972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7112972).length < 2 ^ (prefixWord ++ tailWord_7112972).sum := by decide
  have hdescent : baseEnd_7112972 < baseStart_7112972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7112972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113079 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 4]
def baseStart_7113079 : Nat := 118140960795 + 7113079 * 2 ^ 59
def prefixEnd_7113079 : Nat := 4983230072969 + 3 ^ 40 * 7113079 * 2
def baseEnd_7113079 : Nat := 3652428460402480779400051

theorem tailTrace_7113079 : CollatzResearch.WordTrace tailWord_7113079 prefixEnd_7113079 3652428460402480779400051 := by
  unfold tailWord_7113079
  simp only [CollatzResearch.WordTrace]
  refine ⟨259435304597537075021774291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172956869731691383347849527 259435304597537075021774291)
  ·
    refine ⟨389152956896305612532661437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259435304597537075021774291 389152956896305612532661437)
    ·
      refine ⟨145932358836114604699748039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389152956896305612532661437 145932358836114604699748039)
      ·
        refine ⟨218898538254171907049622059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145932358836114604699748039 218898538254171907049622059)
        ·
          refine ⟨328347807381257860574433089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218898538254171907049622059 328347807381257860574433089)
          ·
            refine ⟨246260855535943395430824817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328347807381257860574433089 246260855535943395430824817)
            ·
              refine ⟨184695641651957546573118613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246260855535943395430824817 184695641651957546573118613)
              ·
                refine ⟨8657608202435509995614935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184695641651957546573118613 8657608202435509995614935)
                ·
                  refine ⟨12986412303653264993422403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8657608202435509995614935 12986412303653264993422403)
                  ·
                    refine ⟨19479618455479897490133605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12986412303653264993422403 19479618455479897490133605)
                    ·
                      refine ⟨3652428460402480779400051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19479618455479897490133605 3652428460402480779400051)
                      ·
                        rfl

theorem cell23_7113079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_7113079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113079 prefixEnd_7113079 := by exact prefixLift 7113079
  have htrace : WordTrace (prefixWord ++ tailWord_7113079) baseStart_7113079 baseEnd_7113079 := by
    simpa [prefixWord, tailWord_7113079, baseEnd_7113079] using wordTrace_append hprefix tailTrace_7113079
  have hstable : (prefixWord ++ tailWord_7113079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113079).length < 2 ^ (prefixWord ++ tailWord_7113079).sum := by decide
  have hdescent : baseEnd_7113079 < baseStart_7113079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113089 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 3, 6]
def baseStart_7113089 : Nat := 118140960795 + 7113089 * 2 ^ 59
def prefixEnd_7113089 : Nat := 4983230072969 + 3 ^ 40 * 7113089 * 2
def baseEnd_7113089 : Nat := 1217477865069675246758335

theorem tailTrace_7113089 : CollatzResearch.WordTrace tailWord_7113089 prefixEnd_7113089 1217477865069675246758335 := by
  unfold tailWord_7113089
  simp only [CollatzResearch.WordTrace]
  refine ⟨259435669327500846729638321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172957112885000564486425547 259435669327500846729638321)
  ·
    refine ⟨194576751995625635047228741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259435669327500846729638321 194576751995625635047228741)
    ·
      refine ⟨36483140999179806571355389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194576751995625635047228741 36483140999179806571355389)
      ·
        refine ⟨13681177874692427464258271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36483140999179806571355389 13681177874692427464258271)
        ·
          refine ⟨20521766812038641196387407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13681177874692427464258271 20521766812038641196387407)
          ·
            refine ⟨30782650218057961794581111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20521766812038641196387407 30782650218057961794581111)
            ·
              refine ⟨46173975327086942691871667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30782650218057961794581111 46173975327086942691871667)
              ·
                refine ⟨69260962990630414037807501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46173975327086942691871667 69260962990630414037807501)
                ·
                  refine ⟨25972861121486405264177813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69260962990630414037807501 25972861121486405264177813)
                  ·
                    refine ⟨1217477865069675246758335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25972861121486405264177813 1217477865069675246758335)
                    ·
                      rfl

theorem cell23_7113089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_7113089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113089 prefixEnd_7113089 := by exact prefixLift 7113089
  have htrace : WordTrace (prefixWord ++ tailWord_7113089) baseStart_7113089 baseEnd_7113089 := by
    simpa [prefixWord, tailWord_7113089, baseEnd_7113089] using wordTrace_append hprefix tailTrace_7113089
  have hstable : (prefixWord ++ tailWord_7113089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113089).length < 2 ^ (prefixWord ++ tailWord_7113089).sum := by decide
  have hdescent : baseEnd_7113089 < baseStart_7113089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113099 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 5]
def baseStart_7113099 : Nat := 118140960795 + 7113099 * 2 ^ 59
def prefixEnd_7113099 : Nat := 4983230072969 + 3 ^ 40 * 7113099 * 2
def baseEnd_7113099 : Nat := 3652438730015570701149959

theorem tailTrace_7113099 : CollatzResearch.WordTrace tailWord_7113099 prefixEnd_7113099 3652438730015570701149959 := by
  unfold tailWord_7113099
  simp only [CollatzResearch.WordTrace]
  refine ⟨259436034057464618437502351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172957356038309745625001567 259436034057464618437502351)
  ·
    refine ⟨389154051086196927656253527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259436034057464618437502351 389154051086196927656253527)
    ·
      refine ⟨583731076629295391484380291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389154051086196927656253527 583731076629295391484380291)
      ·
        refine ⟨875596614943943087226570437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583731076629295391484380291 875596614943943087226570437)
        ·
          refine ⟨164174365301989328854981957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 875596614943943087226570437 164174365301989328854981957)
          ·
            refine ⟨30782693494122999160309117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164174365301989328854981957 30782693494122999160309117)
            ·
              refine ⟨11543510060296124685115919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30782693494122999160309117 11543510060296124685115919)
              ·
                refine ⟨17315265090444187027673879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11543510060296124685115919 17315265090444187027673879)
                ·
                  refine ⟨25972897635666280541510819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17315265090444187027673879 25972897635666280541510819)
                  ·
                    refine ⟨38959346453499420812266229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25972897635666280541510819 38959346453499420812266229)
                    ·
                      refine ⟨3652438730015570701149959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38959346453499420812266229 3652438730015570701149959)
                      ·
                        rfl

theorem cell23_7113099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 5].length) (baseStart_7113099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113099 prefixEnd_7113099 := by exact prefixLift 7113099
  have htrace : WordTrace (prefixWord ++ tailWord_7113099) baseStart_7113099 baseEnd_7113099 := by
    simpa [prefixWord, tailWord_7113099, baseEnd_7113099] using wordTrace_append hprefix tailTrace_7113099
  have hstable : (prefixWord ++ tailWord_7113099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113099).length < 2 ^ (prefixWord ++ tailWord_7113099).sum := by decide
  have hdescent : baseEnd_7113099 < baseStart_7113099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113132 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_7113132 : Nat := 118140960795 + 7113132 * 2 ^ 59
def prefixEnd_7113132 : Nat := 4983230072969 + 3 ^ 40 * 7113132 * 2
def baseEnd_7113132 : Nat := 1217485224959056357345769

theorem tailTrace_7113132 : CollatzResearch.WordTrace tailWord_7113132 prefixEnd_7113132 1217485224959056357345769 := by
  unfold tailWord_7113132
  simp only [CollatzResearch.WordTrace]
  refine ⟨129718618833172532536726825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172958158444230043382302433 129718618833172532536726825)
  ·
    refine ⟨97288964124879399402545119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129718618833172532536726825 97288964124879399402545119)
    ·
      refine ⟨145933446187319099103817679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97288964124879399402545119 145933446187319099103817679)
      ·
        refine ⟨218900169280978648655726519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145933446187319099103817679 218900169280978648655726519)
        ·
          refine ⟨328350253921467972983589779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218900169280978648655726519 328350253921467972983589779)
          ·
            refine ⟨492525380882201959475384669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328350253921467972983589779 492525380882201959475384669)
            ·
              refine ⟨184697017830825734803269251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 492525380882201959475384669 184697017830825734803269251)
              ·
                refine ⟨277045526746238602204903877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184697017830825734803269251 277045526746238602204903877)
                ·
                  refine ⟨51946036264919737913419477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277045526746238602204903877 51946036264919737913419477)
                  ·
                    refine ⟨1217485224959056357345769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51946036264919737913419477 1217485224959056357345769)
                    ·
                      rfl

theorem cell23_7113132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_7113132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113132 prefixEnd_7113132 := by exact prefixLift 7113132
  have htrace : WordTrace (prefixWord ++ tailWord_7113132) baseStart_7113132 baseEnd_7113132 := by
    simpa [prefixWord, tailWord_7113132, baseEnd_7113132] using wordTrace_append hprefix tailTrace_7113132
  have hstable : (prefixWord ++ tailWord_7113132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113132).length < 2 ^ (prefixWord ++ tailWord_7113132).sum := by decide
  have hdescent : baseEnd_7113132 < baseStart_7113132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113153 : List Nat := [1, 2, 7, 1, 1, 1, 10]
def baseStart_7113153 : Nat := 118140960795 + 7113153 * 2 ^ 59
def prefixEnd_7113153 : Nat := 4983230072969 + 3 ^ 40 * 7113153 * 2
def baseEnd_7113153 : Nat := 45092178493468067776231

theorem tailTrace_7113153 : CollatzResearch.WordTrace tailWord_7113153 prefixEnd_7113153 45092178493468067776231 := by
  unfold tailWord_7113153
  simp only [CollatzResearch.WordTrace]
  refine ⟨259438003599268985659968113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172958669066179323773312075 259438003599268985659968113)
  ·
    refine ⟨194578502699451739244976085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259438003599268985659968113 194578502699451739244976085)
    ·
      refine ⟨4560433657018400138554127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 194578502699451739244976085 4560433657018400138554127)
      ·
        refine ⟨6840650485527600207831191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4560433657018400138554127 6840650485527600207831191)
        ·
          refine ⟨10260975728291400311746787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840650485527600207831191 10260975728291400311746787)
          ·
            refine ⟨15391463592437100467620181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10260975728291400311746787 15391463592437100467620181)
            ·
              refine ⟨45092178493468067776231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15391463592437100467620181 45092178493468067776231)
              ·
                rfl

theorem cell23_7113153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 10].length) (baseStart_7113153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113153 prefixEnd_7113153 := by exact prefixLift 7113153
  have htrace : WordTrace (prefixWord ++ tailWord_7113153) baseStart_7113153 baseEnd_7113153 := by
    simpa [prefixWord, tailWord_7113153, baseEnd_7113153] using wordTrace_append hprefix tailTrace_7113153
  have hstable : (prefixWord ++ tailWord_7113153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113153).length < 2 ^ (prefixWord ++ tailWord_7113153).sum := by decide
  have hdescent : baseEnd_7113153 < baseStart_7113153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113206 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_7113206 : Nat := 118140960795 + 7113206 * 2 ^ 59
def prefixEnd_7113206 : Nat := 4983230072969 + 3 ^ 40 * 7113206 * 2
def baseEnd_7113206 : Nat := 3652493672445601782511967

theorem tailTrace_7113206 : CollatzResearch.WordTrace tailWord_7113206 prefixEnd_7113206 3652493672445601782511967 := by
  unfold tailWord_7113206
  simp only [CollatzResearch.WordTrace]
  refine ⟨16214996041754810981977967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172959957778717983807764981 16214996041754810981977967)
  ·
    refine ⟨24322494062632216472966951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16214996041754810981977967 24322494062632216472966951)
    ·
      refine ⟨36483741093948324709450427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24322494062632216472966951 36483741093948324709450427)
      ·
        refine ⟨54725611640922487064175641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36483741093948324709450427 54725611640922487064175641)
        ·
          refine ⟨41044208730691865298131731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54725611640922487064175641 41044208730691865298131731)
          ·
            refine ⟨61566313096037797947197597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41044208730691865298131731 61566313096037797947197597)
            ·
              refine ⟨23087367411014174230199099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61566313096037797947197597 23087367411014174230199099)
              ·
                refine ⟨34631051116521261345298649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23087367411014174230199099 34631051116521261345298649)
                ·
                  refine ⟨25973288337390946008973987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34631051116521261345298649 25973288337390946008973987)
                  ·
                    refine ⟨38959932506086419013460981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25973288337390946008973987 38959932506086419013460981)
                    ·
                      refine ⟨3652493672445601782511967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38959932506086419013460981 3652493672445601782511967)
                      ·
                        rfl

theorem cell23_7113206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_7113206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113206 prefixEnd_7113206 := by exact prefixLift 7113206
  have htrace : WordTrace (prefixWord ++ tailWord_7113206) baseStart_7113206 baseEnd_7113206 := by
    simpa [prefixWord, tailWord_7113206, baseEnd_7113206] using wordTrace_append hprefix tailTrace_7113206
  have hstable : (prefixWord ++ tailWord_7113206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113206).length < 2 ^ (prefixWord ++ tailWord_7113206).sum := by decide
  have hdescent : baseEnd_7113206 < baseStart_7113206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113220 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_7113220 : Nat := 118140960795 + 7113220 * 2 ^ 59
def prefixEnd_7113220 : Nat := 4983230072969 + 3 ^ 40 * 7113220 * 2
def baseEnd_7113220 : Nat := 3652500861174764727736903

theorem tailTrace_7113220 : CollatzResearch.WordTrace tailWord_7113220 prefixEnd_7113220 3652500861174764727736903 := by
  unfold tailWord_7113220
  simp only [CollatzResearch.WordTrace]
  refine ⟨129720223645013128051328557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172960298193350837401771409 129720223645013128051328557)
  ·
    refine ⟨48645083866879923019248209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129720223645013128051328557 48645083866879923019248209)
    ·
      refine ⟨36483812900159942264436157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48645083866879923019248209 36483812900159942264436157)
      ·
        refine ⟨13681429837559978349163559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36483812900159942264436157 13681429837559978349163559)
        ·
          refine ⟨20522144756339967523745339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13681429837559978349163559 20522144756339967523745339)
          ·
            refine ⟨30783217134509951285618009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20522144756339967523745339 30783217134509951285618009)
            ·
              refine ⟨23087412850882463464213507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30783217134509951285618009 23087412850882463464213507)
              ·
                refine ⟨34631119276323695196320261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23087412850882463464213507 34631119276323695196320261)
                ·
                  refine ⟨6493334864310692849310049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34631119276323695196320261 6493334864310692849310049)
                  ·
                    refine ⟨4870001148233019636982537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6493334864310692849310049 4870001148233019636982537)
                    ·
                      refine ⟨3652500861174764727736903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4870001148233019636982537 3652500861174764727736903)
                      ·
                        rfl

theorem cell23_7113220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_7113220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113220 prefixEnd_7113220 := by exact prefixLift 7113220
  have htrace : WordTrace (prefixWord ++ tailWord_7113220) baseStart_7113220 baseEnd_7113220 := by
    simpa [prefixWord, tailWord_7113220, baseEnd_7113220] using wordTrace_append hprefix tailTrace_7113220
  have hstable : (prefixWord ++ tailWord_7113220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113220).length < 2 ^ (prefixWord ++ tailWord_7113220).sum := by decide
  have hdescent : baseEnd_7113220 < baseStart_7113220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113249 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7113249 : Nat := 118140960795 + 7113249 * 2 ^ 59
def prefixEnd_7113249 : Nat := 4983230072969 + 3 ^ 40 * 7113249 * 2
def baseEnd_7113249 : Nat := 3652515752113745114274269

theorem tailTrace_7113249 : CollatzResearch.WordTrace tailWord_7113249 prefixEnd_7113249 3652515752113745114274269 := by
  unfold tailWord_7113249
  simp only [CollatzResearch.WordTrace]
  refine ⟨259441505006921194055462801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172961003337947462703641867 259441505006921194055462801)
  ·
    refine ⟨194581128755190895541597101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259441505006921194055462801 194581128755190895541597101)
    ·
      refine ⟨72967923283196585828098913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194581128755190895541597101 72967923283196585828098913)
      ·
        refine ⟨54725942462397439371074185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72967923283196585828098913 54725942462397439371074185)
        ·
          refine ⟨41044456846798079528305639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54725942462397439371074185 41044456846798079528305639)
          ·
            refine ⟨61566685270197119292458459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41044456846798079528305639 61566685270197119292458459)
            ·
              refine ⟨92350027905295678938687689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61566685270197119292458459 92350027905295678938687689)
              ·
                refine ⟨69262520928971759204015767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92350027905295678938687689 69262520928971759204015767)
                ·
                  refine ⟨103893781393457638806023651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69262520928971759204015767 103893781393457638806023651)
                  ·
                    refine ⟨155840672090186458209035477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103893781393457638806023651 155840672090186458209035477)
                    ·
                      refine ⟨3652515752113745114274269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155840672090186458209035477 3652515752113745114274269)
                      ·
                        rfl

theorem cell23_7113249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7113249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113249 prefixEnd_7113249 := by exact prefixLift 7113249
  have htrace : WordTrace (prefixWord ++ tailWord_7113249) baseStart_7113249 baseEnd_7113249 := by
    simpa [prefixWord, tailWord_7113249, baseEnd_7113249] using wordTrace_append hprefix tailTrace_7113249
  have hstable : (prefixWord ++ tailWord_7113249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113249).length < 2 ^ (prefixWord ++ tailWord_7113249).sum := by decide
  have hdescent : baseEnd_7113249 < baseStart_7113249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113259 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 4]
def baseStart_7113259 : Nat := 118140960795 + 7113259 * 2 ^ 59
def prefixEnd_7113259 : Nat := 4983230072969 + 3 ^ 40 * 7113259 * 2
def baseEnd_7113259 : Nat := 3652520886920290075149223

theorem tailTrace_7113259 : CollatzResearch.WordTrace tailWord_7113259 prefixEnd_7113259 3652520886920290075149223 := by
  unfold tailWord_7113259
  simp only [CollatzResearch.WordTrace]
  refine ⟨259441869736884965763326831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172961246491256643842217887 259441869736884965763326831)
  ·
    refine ⟨389162804605327448644990247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259441869736884965763326831 389162804605327448644990247)
    ·
      refine ⟨583744206907991172967485371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389162804605327448644990247 583744206907991172967485371)
      ·
        refine ⟨875616310361986759451228057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583744206907991172967485371 875616310361986759451228057)
        ·
          refine ⟨656712232771490069588421043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 875616310361986759451228057 656712232771490069588421043)
          ·
            refine ⟨985068349157235104382631565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656712232771490069588421043 985068349157235104382631565)
            ·
              refine ⟨369400630933963164143486837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 985068349157235104382631565 369400630933963164143486837)
              ·
                refine ⟨34631309150059046638451891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 369400630933963164143486837 34631309150059046638451891)
                ·
                  refine ⟨51946963725088569957677837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34631309150059046638451891 51946963725088569957677837)
                  ·
                    refine ⟨19480111396908213734129189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51946963725088569957677837 19480111396908213734129189)
                    ·
                      refine ⟨3652520886920290075149223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19480111396908213734129189 3652520886920290075149223)
                      ·
                        rfl

theorem cell23_7113259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 4].length) (baseStart_7113259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113259 prefixEnd_7113259 := by exact prefixLift 7113259
  have htrace : WordTrace (prefixWord ++ tailWord_7113259) baseStart_7113259 baseEnd_7113259 := by
    simpa [prefixWord, tailWord_7113259, baseEnd_7113259] using wordTrace_append hprefix tailTrace_7113259
  have hstable : (prefixWord ++ tailWord_7113259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113259).length < 2 ^ (prefixWord ++ tailWord_7113259).sum := by decide
  have hdescent : baseEnd_7113259 < baseStart_7113259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113279 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_7113279 : Nat := 118140960795 + 7113279 * 2 ^ 59
def prefixEnd_7113279 : Nat := 4983230072969 + 3 ^ 40 * 7113279 * 2
def baseEnd_7113279 : Nat := 3652531156533379996899131

theorem tailTrace_7113279 : CollatzResearch.WordTrace tailWord_7113279 prefixEnd_7113279 3652531156533379996899131 := by
  unfold tailWord_7113279
  simp only [CollatzResearch.WordTrace]
  refine ⟨259442599196812509179054891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172961732797875006119369927 259442599196812509179054891)
  ·
    refine ⟨389163898795218763768582337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259442599196812509179054891 389163898795218763768582337)
    ·
      refine ⟨291872924096414072826436753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389163898795218763768582337 291872924096414072826436753)
      ·
        refine ⟨218904693072310554619827565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291872924096414072826436753 218904693072310554619827565)
        ·
          refine ⟨82089259902116457982435337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218904693072310554619827565 82089259902116457982435337)
          ·
            refine ⟨61566944926587343486826503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82089259902116457982435337 61566944926587343486826503)
            ·
              refine ⟨92350417389881015230239755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61566944926587343486826503 92350417389881015230239755)
              ·
                refine ⟨138525626084821522845359633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92350417389881015230239755 138525626084821522845359633)
                ·
                  refine ⟨103894219563616142134019725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138525626084821522845359633 103894219563616142134019725)
                  ·
                    refine ⟨38960332336356053300257397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103894219563616142134019725 38960332336356053300257397)
                    ·
                      refine ⟨3652531156533379996899131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38960332336356053300257397 3652531156533379996899131)
                      ·
                        rfl

theorem cell23_7113279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_7113279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113279 prefixEnd_7113279 := by exact prefixLift 7113279
  have htrace : WordTrace (prefixWord ++ tailWord_7113279) baseStart_7113279 baseEnd_7113279 := by
    simpa [prefixWord, tailWord_7113279, baseEnd_7113279] using wordTrace_append hprefix tailTrace_7113279
  have hstable : (prefixWord ++ tailWord_7113279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113279).length < 2 ^ (prefixWord ++ tailWord_7113279).sum := by decide
  have hdescent : baseEnd_7113279 < baseStart_7113279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113289 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 4]
def baseStart_7113289 : Nat := 118140960795 + 7113289 * 2 ^ 59
def prefixEnd_7113289 : Nat := 4983230072969 + 3 ^ 40 * 7113289 * 2
def baseEnd_7113289 : Nat := 3652536291339924957774085

theorem tailTrace_7113289 : CollatzResearch.WordTrace tailWord_7113289 prefixEnd_7113289 3652536291339924957774085 := by
  unfold tailWord_7113289
  simp only [CollatzResearch.WordTrace]
  refine ⟨259442963926776280886918921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172961975951184187257945947 259442963926776280886918921)
  ·
    refine ⟨194582222945082210665189191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259442963926776280886918921 194582222945082210665189191)
    ·
      refine ⟨291873334417623315997783787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194582222945082210665189191 291873334417623315997783787)
      ·
        refine ⟨437810001626434973996675681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291873334417623315997783787 437810001626434973996675681)
        ·
          refine ⟨328357501219826230497506761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437810001626434973996675681 328357501219826230497506761)
          ·
            refine ⟨246268125914869672873130071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328357501219826230497506761 246268125914869672873130071)
            ·
              refine ⟨369402188872304509309695107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246268125914869672873130071 369402188872304509309695107)
              ·
                refine ⟨554103283308456763964542661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369402188872304509309695107 554103283308456763964542661)
                ·
                  refine ⟨103894365620335643243351749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554103283308456763964542661 103894365620335643243351749)
                  ·
                    refine ⟨19480193553812933108128453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103894365620335643243351749 19480193553812933108128453)
                    ·
                      refine ⟨3652536291339924957774085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19480193553812933108128453 3652536291339924957774085)
                      ·
                        rfl

theorem cell23_7113289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_7113289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113289 prefixEnd_7113289 := by exact prefixLift 7113289
  have htrace : WordTrace (prefixWord ++ tailWord_7113289) baseStart_7113289 baseEnd_7113289 := by
    simpa [prefixWord, tailWord_7113289, baseEnd_7113289] using wordTrace_append hprefix tailTrace_7113289
  have hstable : (prefixWord ++ tailWord_7113289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113289).length < 2 ^ (prefixWord ++ tailWord_7113289).sum := by decide
  have hdescent : baseEnd_7113289 < baseStart_7113289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113313 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_7113313 : Nat := 118140960795 + 7113313 * 2 ^ 59
def prefixEnd_7113313 : Nat := 4983230072969 + 3 ^ 40 * 7113313 * 2
def baseEnd_7113313 : Nat := 3652548614875632863873975

theorem tailTrace_7113313 : CollatzResearch.WordTrace tailWord_7113313 prefixEnd_7113313 3652548614875632863873975 := by
  unfold tailWord_7113313
  simp only [CollatzResearch.WordTrace]
  refine ⟨259443839278689332985792593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172962559519126221990528395 259443839278689332985792593)
  ·
    refine ⟨194582879459016999739344445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259443839278689332985792593 194582879459016999739344445)
    ·
      refine ⟨72968579797131374902254167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194582879459016999739344445 72968579797131374902254167)
      ·
        refine ⟨109452869695697062353381251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72968579797131374902254167 109452869695697062353381251)
        ·
          refine ⟨164179304543545593530071877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109452869695697062353381251 164179304543545593530071877)
          ·
            refine ⟨30783619601914798786888477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164179304543545593530071877 30783619601914798786888477)
            ·
              refine ⟨11543857350718049545083179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30783619601914798786888477 11543857350718049545083179)
              ·
                refine ⟨17315786026077074317624769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11543857350718049545083179 17315786026077074317624769)
                ·
                  refine ⟨12986839519557805738218577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17315786026077074317624769 12986839519557805738218577)
                  ·
                    refine ⟨9740129639668354303663933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12986839519557805738218577 9740129639668354303663933)
                    ·
                      refine ⟨3652548614875632863873975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9740129639668354303663933 3652548614875632863873975)
                      ·
                        rfl

theorem cell23_7113313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_7113313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113313 prefixEnd_7113313 := by exact prefixLift 7113313
  have htrace : WordTrace (prefixWord ++ tailWord_7113313) baseStart_7113313 baseEnd_7113313 := by
    simpa [prefixWord, tailWord_7113313, baseEnd_7113313] using wordTrace_append hprefix tailTrace_7113313
  have hstable : (prefixWord ++ tailWord_7113313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113313).length < 2 ^ (prefixWord ++ tailWord_7113313).sum := by decide
  have hdescent : baseEnd_7113313 < baseStart_7113313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113333 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 8]
def baseStart_7113333 : Nat := 118140960795 + 7113333 * 2 ^ 59
def prefixEnd_7113333 : Nat := 4983230072969 + 3 ^ 40 * 7113333 * 2
def baseEnd_7113333 : Nat := 405839876054302531735987

theorem tailTrace_7113333 : CollatzResearch.WordTrace tailWord_7113333 prefixEnd_7113333 405839876054302531735987 := by
  unfold tailWord_7113333
  simp only [CollatzResearch.WordTrace]
  refine ⟨259444568738616876401520653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172963045825744584267680435 259444568738616876401520653)
  ·
    refine ⟨97291713276981328650570245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259444568738616876401520653 97291713276981328650570245)
    ·
      refine ⟨18242196239433999121981921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97291713276981328650570245 18242196239433999121981921)
      ·
        refine ⟨13681647179575499341486441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18242196239433999121981921 13681647179575499341486441)
        ·
          refine ⟨10261235384681624506114831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13681647179575499341486441 10261235384681624506114831)
          ·
            refine ⟨15391853077022436759172247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10261235384681624506114831 15391853077022436759172247)
            ·
              refine ⟨23087779615533655138758371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15391853077022436759172247 23087779615533655138758371)
              ·
                refine ⟨34631669423300482708137557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23087779615533655138758371 34631669423300482708137557)
                ·
                  refine ⟨405839876054302531735987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34631669423300482708137557 405839876054302531735987)
                  ·
                    rfl

theorem cell23_7113333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_7113333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113333 prefixEnd_7113333 := by exact prefixLift 7113333
  have htrace : WordTrace (prefixWord ++ tailWord_7113333) baseStart_7113333 baseEnd_7113333 := by
    simpa [prefixWord, tailWord_7113333, baseEnd_7113333] using wordTrace_append hprefix tailTrace_7113333
  have hstable : (prefixWord ++ tailWord_7113333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113333).length < 2 ^ (prefixWord ++ tailWord_7113333).sum := by decide
  have hdescent : baseEnd_7113333 < baseStart_7113333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113339 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 7]
def baseStart_7113339 : Nat := 118140960795 + 7113339 * 2 ^ 59
def prefixEnd_7113339 : Nat := 4983230072969 + 3 ^ 40 * 7113339 * 2
def baseEnd_7113339 : Nat := 3652561965372649762148855

theorem tailTrace_7113339 : CollatzResearch.WordTrace tailWord_7113339 prefixEnd_7113339 3652561965372649762148855 := by
  unfold tailWord_7113339
  simp only [CollatzResearch.WordTrace]
  refine ⟨259444787576595139426239071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172963191717730092950826047 259444787576595139426239071)
  ·
    refine ⟨389167181364892709139358607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259444787576595139426239071 389167181364892709139358607)
    ·
      refine ⟨583750772047339063709037911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389167181364892709139358607 583750772047339063709037911)
      ·
        refine ⟨875626158071008595563556867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583750772047339063709037911 875626158071008595563556867)
        ·
          refine ⟨1313439237106512893345335301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875626158071008595563556867 1313439237106512893345335301)
          ·
            refine ⟨246269856957471167502250369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1313439237106512893345335301 246269856957471167502250369)
            ·
              refine ⟨184702392718103375626687777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246269856957471167502250369 184702392718103375626687777)
              ·
                refine ⟨138526794538577531720015833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184702392718103375626687777 138526794538577531720015833)
                ·
                  refine ⟨103895095903933148790011875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138526794538577531720015833 103895095903933148790011875)
                  ·
                    refine ⟨155842643855899723185017813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103895095903933148790011875 155842643855899723185017813)
                    ·
                      refine ⟨3652561965372649762148855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155842643855899723185017813 3652561965372649762148855)
                      ·
                        rfl

theorem cell23_7113339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_7113339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113339 prefixEnd_7113339 := by exact prefixLift 7113339
  have htrace : WordTrace (prefixWord ++ tailWord_7113339) baseStart_7113339 baseEnd_7113339 := by
    simpa [prefixWord, tailWord_7113339, baseEnd_7113339] using wordTrace_append hprefix tailTrace_7113339
  have hstable : (prefixWord ++ tailWord_7113339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113339).length < 2 ^ (prefixWord ++ tailWord_7113339).sum := by decide
  have hdescent : baseEnd_7113339 < baseStart_7113339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113420 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7113420 : Nat := 118140960795 + 7113420 * 2 ^ 59
def prefixEnd_7113420 : Nat := 4983230072969 + 3 ^ 40 * 7113420 * 2
def baseEnd_7113420 : Nat := 3652603557305663945235983

theorem tailTrace_7113420 : CollatzResearch.WordTrace tailWord_7113420 prefixEnd_7113420 3652603557305663945235983 := by
  unfold tailWord_7113420
  simp only [CollatzResearch.WordTrace]
  refine ⟨129723870944650845129968857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172965161259534460173291809 129723870944650845129968857)
  ·
    refine ⟨97292903208488133847476643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129723870944650845129968857 97292903208488133847476643)
    ·
      refine ⟨145939354812732200771214965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97292903208488133847476643 145939354812732200771214965)
      ·
        refine ⟨13681814513693643822301403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145939354812732200771214965 13681814513693643822301403)
        ·
          refine ⟨20522721770540465733452105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13681814513693643822301403 20522721770540465733452105)
          ·
            refine ⟨15392041327905349300089079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20522721770540465733452105 15392041327905349300089079)
            ·
              refine ⟨23088061991858023950133619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15392041327905349300089079 23088061991858023950133619)
              ·
                refine ⟨34632092987787035925200429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23088061991858023950133619 34632092987787035925200429)
                ·
                  refine ⟨12987034870420138471950161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34632092987787035925200429 12987034870420138471950161)
                  ·
                    refine ⟨9740276152815103853962621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12987034870420138471950161 9740276152815103853962621)
                    ·
                      refine ⟨3652603557305663945235983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9740276152815103853962621 3652603557305663945235983)
                      ·
                        rfl

theorem cell23_7113420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7113420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113420 prefixEnd_7113420 := by exact prefixLift 7113420
  have htrace : WordTrace (prefixWord ++ tailWord_7113420) baseStart_7113420 baseEnd_7113420 := by
    simpa [prefixWord, tailWord_7113420, baseEnd_7113420] using wordTrace_append hprefix tailTrace_7113420
  have hstable : (prefixWord ++ tailWord_7113420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113420).length < 2 ^ (prefixWord ++ tailWord_7113420).sum := by decide
  have hdescent : baseEnd_7113420 < baseStart_7113420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113433 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 1, 3, 3]
def baseStart_7113433 : Nat := 118140960795 + 7113433 * 2 ^ 59
def prefixEnd_7113433 : Nat := 4983230072969 + 3 ^ 40 * 7113433 * 2
def baseEnd_7113433 : Nat := 3652610232554172394373423

theorem tailTrace_7113433 : CollatzResearch.WordTrace tailWord_7113433 prefixEnd_7113433 3652610232554172394373423 := by
  unfold tailWord_7113433
  simp only [CollatzResearch.WordTrace]
  refine ⟨259448216038254593480160953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172965477358836395653440635 259448216038254593480160953)
  ·
    refine ⟨194586162028690945110120715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259448216038254593480160953 194586162028690945110120715)
    ·
      refine ⟨291879243043036417665181073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194586162028690945110120715 291879243043036417665181073)
      ·
        refine ⟨218909432282277313248885805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291879243043036417665181073 218909432282277313248885805)
        ·
          refine ⟨82091037105853992468332177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218909432282277313248885805 82091037105853992468332177)
          ·
            refine ⟨61568277829390494351249133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82091037105853992468332177 61568277829390494351249133)
            ·
              refine ⟨23088104186021435381718425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61568277829390494351249133 23088104186021435381718425)
              ·
                refine ⟨17316078139516076536288819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23088104186021435381718425 17316078139516076536288819)
                ·
                  refine ⟨25974117209274114804433229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17316078139516076536288819 25974117209274114804433229)
                  ·
                    refine ⟨9740293953477793051662461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25974117209274114804433229 9740293953477793051662461)
                    ·
                      refine ⟨3652610232554172394373423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9740293953477793051662461 3652610232554172394373423)
                      ·
                        rfl

theorem cell23_7113433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_7113433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113433 prefixEnd_7113433 := by exact prefixLift 7113433
  have htrace : WordTrace (prefixWord ++ tailWord_7113433) baseStart_7113433 baseEnd_7113433 := by
    simpa [prefixWord, tailWord_7113433, baseEnd_7113433] using wordTrace_append hprefix tailTrace_7113433
  have hstable : (prefixWord ++ tailWord_7113433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113433).length < 2 ^ (prefixWord ++ tailWord_7113433).sum := by decide
  have hdescent : baseEnd_7113433 < baseStart_7113433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113456 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 4]
def baseStart_7113456 : Nat := 118140960795 + 7113456 * 2 ^ 59
def prefixEnd_7113456 : Nat := 4983230072969 + 3 ^ 40 * 7113456 * 2
def baseEnd_7113456 : Nat := 3652622042609225804385817

theorem tailTrace_7113456 : CollatzResearch.WordTrace tailWord_7113456 prefixEnd_7113456 3652622042609225804385817 := by
  unfold tailWord_7113456
  simp only [CollatzResearch.WordTrace]
  refine ⟨129724527458585634204124111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172966036611447512272165481 129724527458585634204124111)
  ·
    refine ⟨194586791187878451306186167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129724527458585634204124111 194586791187878451306186167)
    ·
      refine ⟨291880186781817676959279251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194586791187878451306186167 291880186781817676959279251)
      ·
        refine ⟨437820280172726515438918877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291880186781817676959279251 437820280172726515438918877)
        ·
          refine ⟨164182605064772443289594579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437820280172726515438918877 164182605064772443289594579)
          ·
            refine ⟨246273907597158664934391869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164182605064772443289594579 246273907597158664934391869)
            ·
              refine ⟨92352715348934499350396951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246273907597158664934391869 92352715348934499350396951)
              ·
                refine ⟨138529073023401749025595427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92352715348934499350396951 138529073023401749025595427)
                ·
                  refine ⟨207793609535102623538393141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138529073023401749025595427 207793609535102623538393141)
                  ·
                    refine ⟨19480650893915870956724357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 207793609535102623538393141 19480650893915870956724357)
                    ·
                      refine ⟨3652622042609225804385817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19480650893915870956724357 3652622042609225804385817)
                      ·
                        rfl

theorem cell23_7113456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_7113456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113456 prefixEnd_7113456 := by exact prefixLift 7113456
  have htrace : WordTrace (prefixWord ++ tailWord_7113456) baseStart_7113456 baseEnd_7113456 := by
    simpa [prefixWord, tailWord_7113456, baseEnd_7113456] using wordTrace_append hprefix tailTrace_7113456
  have hstable : (prefixWord ++ tailWord_7113456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113456).length < 2 ^ (prefixWord ++ tailWord_7113456).sum := by decide
  have hdescent : baseEnd_7113456 < baseStart_7113456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113466 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_7113466 : Nat := 118140960795 + 7113466 * 2 ^ 59
def prefixEnd_7113466 : Nat := 4983230072969 + 3 ^ 40 * 7113466 * 2
def baseEnd_7113466 : Nat := 1217542392471923588420257

theorem tailTrace_7113466 : CollatzResearch.WordTrace tailWord_7113466 prefixEnd_7113466 1217542392471923588420257 := by
  unfold tailWord_7113466
  simp only [CollatzResearch.WordTrace]
  refine ⟨64862354911783760029028063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172966279764756693410741501 64862354911783760029028063)
  ·
    refine ⟨97293532367675640043542095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64862354911783760029028063 97293532367675640043542095)
    ·
      refine ⟨145940298551513460065313143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97293532367675640043542095 145940298551513460065313143)
      ·
        refine ⟨218910447827270190097969715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145940298551513460065313143 218910447827270190097969715)
        ·
          refine ⟨328365671740905285146954573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218910447827270190097969715 328365671740905285146954573)
          ·
            refine ⟨123137126902839481930107965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328365671740905285146954573 123137126902839481930107965)
            ·
              refine ⟨46176422588564805723790487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123137126902839481930107965 46176422588564805723790487)
              ·
                refine ⟨69264633882847208585685731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46176422588564805723790487 69264633882847208585685731)
                ·
                  refine ⟨103896950824270812878528597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69264633882847208585685731 103896950824270812878528597)
                  ·
                    refine ⟨1217542392471923588420257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103896950824270812878528597 1217542392471923588420257)
                    ·
                      rfl

theorem cell23_7113466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_7113466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113466 prefixEnd_7113466 := by exact prefixLift 7113466
  have htrace : WordTrace (prefixWord ++ tailWord_7113466) baseStart_7113466 baseEnd_7113466 := by
    simpa [prefixWord, tailWord_7113466, baseEnd_7113466] using wordTrace_append hprefix tailTrace_7113466
  have hstable : (prefixWord ++ tailWord_7113466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113466).length < 2 ^ (prefixWord ++ tailWord_7113466).sum := by decide
  have hdescent : baseEnd_7113466 < baseStart_7113466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113496 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 11]
def baseStart_7113496 : Nat := 118140960795 + 7113496 * 2 ^ 59
def prefixEnd_7113496 : Nat := 4983230072969 + 3 ^ 40 * 7113496 * 2
def baseEnd_7113496 : Nat := 405849175759489516431737

theorem tailTrace_7113496 : CollatzResearch.WordTrace tailWord_7113496 prefixEnd_7113496 405849175759489516431737 := by
  unfold tailWord_7113496
  simp only [CollatzResearch.WordTrace]
  refine ⟨129725256918513177619852171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172967009224684236826469561 129725256918513177619852171)
  ·
    refine ⟨194587885377769766429778257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129725256918513177619852171 194587885377769766429778257)
    ·
      refine ⟨145940914033327324822333693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194587885377769766429778257 145940914033327324822333693)
      ·
        refine ⟨54727842762497746808375135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145940914033327324822333693 54727842762497746808375135)
        ·
          refine ⟨82091764143746620212562703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54727842762497746808375135 82091764143746620212562703)
          ·
            refine ⟨123137646215619930318844055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82091764143746620212562703 123137646215619930318844055)
            ·
              refine ⟨184706469323429895478266083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123137646215619930318844055 184706469323429895478266083)
              ·
                refine ⟨277059703985144843217399125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184706469323429895478266083 277059703985144843217399125)
                ·
                  refine ⟨405849175759489516431737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 277059703985144843217399125 405849175759489516431737)
                  ·
                    rfl

theorem cell23_7113496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 11].length) (baseStart_7113496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113496 prefixEnd_7113496 := by exact prefixLift 7113496
  have htrace : WordTrace (prefixWord ++ tailWord_7113496) baseStart_7113496 baseEnd_7113496 := by
    simpa [prefixWord, tailWord_7113496, baseEnd_7113496] using wordTrace_append hprefix tailTrace_7113496
  have hstable : (prefixWord ++ tailWord_7113496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113496).length < 2 ^ (prefixWord ++ tailWord_7113496).sum := by decide
  have hdescent : baseEnd_7113496 < baseStart_7113496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113501 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7113501 : Nat := 118140960795 + 7113501 * 2 ^ 59
def prefixEnd_7113501 : Nat := 4983230072969 + 3 ^ 40 * 7113501 * 2
def baseEnd_7113501 : Nat := 3652645149238678128323111

theorem tailTrace_7113501 : CollatzResearch.WordTrace tailWord_7113501 prefixEnd_7113501 3652645149238678128323111 := by
  unfold tailWord_7113501
  simp only [CollatzResearch.WordTrace]
  refine ⟨259450696202008241093636357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172967130801338827395757571 259450696202008241093636357)
  ·
    refine ⟨48647005537876545205056817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259450696202008241093636357 48647005537876545205056817)
    ·
      refine ⟨36485254153407408903792613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48647005537876545205056817 36485254153407408903792613)
      ·
        refine ⟨6840985153763889169461115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36485254153407408903792613 6840985153763889169461115)
        ·
          refine ⟨10261477730645833754191673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840985153763889169461115 10261477730645833754191673)
          ·
            refine ⟨7696108297984375315643755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10261477730645833754191673 7696108297984375315643755)
            ·
              refine ⟨11544162446976562973465633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7696108297984375315643755 11544162446976562973465633)
              ·
                refine ⟨8658121835232422230099225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11544162446976562973465633 8658121835232422230099225)
                ·
                  refine ⟨6493591376424316672574419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8658121835232422230099225 6493591376424316672574419)
                  ·
                    refine ⟨9740387064636475008861629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6493591376424316672574419 9740387064636475008861629)
                    ·
                      refine ⟨3652645149238678128323111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9740387064636475008861629 3652645149238678128323111)
                      ·
                        rfl

theorem cell23_7113501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7113501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113501 prefixEnd_7113501 := by exact prefixLift 7113501
  have htrace : WordTrace (prefixWord ++ tailWord_7113501) baseStart_7113501 baseEnd_7113501 := by
    simpa [prefixWord, tailWord_7113501, baseEnd_7113501] using wordTrace_append hprefix tailTrace_7113501
  have hstable : (prefixWord ++ tailWord_7113501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113501).length < 2 ^ (prefixWord ++ tailWord_7113501).sum := by decide
  have hdescent : baseEnd_7113501 < baseStart_7113501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113503 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 4]
def baseStart_7113503 : Nat := 118140960795 + 7113503 * 2 ^ 59
def prefixEnd_7113503 : Nat := 4983230072969 + 3 ^ 40 * 7113503 * 2
def baseEnd_7113503 : Nat := 3652646176199987120498101

theorem tailTrace_7113503 : CollatzResearch.WordTrace tailWord_7113503 prefixEnd_7113503 3652646176199987120498101 := by
  unfold tailWord_7113503
  simp only [CollatzResearch.WordTrace]
  refine ⟨259450769148000995435209163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172967179432000663623472775 259450769148000995435209163)
  ·
    refine ⟨389176153722001493152813745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259450769148000995435209163 389176153722001493152813745)
    ·
      refine ⟨291882115291501119864610309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389176153722001493152813745 291882115291501119864610309)
      ·
        refine ⟨54727896617156459974614433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291882115291501119864610309 54727896617156459974614433)
        ·
          refine ⟨41045922462867344980960825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54727896617156459974614433 41045922462867344980960825)
          ·
            refine ⟨30784441847150508735720619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41045922462867344980960825 30784441847150508735720619)
            ·
              refine ⟨46176662770725763103580929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30784441847150508735720619 46176662770725763103580929)
              ·
                refine ⟨34632497078044322327685697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46176662770725763103580929 34632497078044322327685697)
                ·
                  refine ⟨25974372808533241745764273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34632497078044322327685697 25974372808533241745764273)
                  ·
                    refine ⟨19480779606399931309323205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25974372808533241745764273 19480779606399931309323205)
                    ·
                      refine ⟨3652646176199987120498101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19480779606399931309323205 3652646176199987120498101)
                      ·
                        rfl

theorem cell23_7113503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_7113503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113503 prefixEnd_7113503 := by exact prefixLift 7113503
  have htrace : WordTrace (prefixWord ++ tailWord_7113503) baseStart_7113503 baseEnd_7113503 := by
    simpa [prefixWord, tailWord_7113503, baseEnd_7113503] using wordTrace_append hprefix tailTrace_7113503
  have hstable : (prefixWord ++ tailWord_7113503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113503).length < 2 ^ (prefixWord ++ tailWord_7113503).sum := by decide
  have hdescent : baseEnd_7113503 < baseStart_7113503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113543 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 2, 5]
def baseStart_7113543 : Nat := 118140960795 + 7113543 * 2 ^ 59
def prefixEnd_7113543 : Nat := 4983230072969 + 3 ^ 40 * 7113543 * 2
def baseEnd_7113543 : Nat := 1217555571808722321332639

theorem tailTrace_7113543 : CollatzResearch.WordTrace tailWord_7113543 prefixEnd_7113543 1217555571808722321332639 := by
  unfold tailWord_7113543
  simp only [CollatzResearch.WordTrace]
  refine ⟨259452228067856082266665283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172968152045237388177776855 259452228067856082266665283)
  ·
    refine ⟨389178342101784123399997925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259452228067856082266665283 389178342101784123399997925)
    ·
      refine ⟨72970939144084523137499611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389178342101784123399997925 72970939144084523137499611)
      ·
        refine ⟨109456408716126784706249417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72970939144084523137499611 109456408716126784706249417)
        ·
          refine ⟨82092306537095088529687063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109456408716126784706249417 82092306537095088529687063)
          ·
            refine ⟨123138459805642632794530595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82092306537095088529687063 123138459805642632794530595)
            ·
              refine ⟨184707689708463949191795893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123138459805642632794530595 184707689708463949191795893)
              ·
                refine ⟨17316345910168495236730865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184707689708463949191795893 17316345910168495236730865)
                ·
                  refine ⟨12987259432626371427548149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17316345910168495236730865 12987259432626371427548149)
                  ·
                    refine ⟨1217555571808722321332639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12987259432626371427548149 1217555571808722321332639)
                    ·
                      rfl

theorem cell23_7113543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_7113543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113543 prefixEnd_7113543 := by exact prefixLift 7113543
  have htrace : WordTrace (prefixWord ++ tailWord_7113543) baseStart_7113543 baseEnd_7113543 := by
    simpa [prefixWord, tailWord_7113543, baseEnd_7113543] using wordTrace_append hprefix tailTrace_7113543
  have hstable : (prefixWord ++ tailWord_7113543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113543).length < 2 ^ (prefixWord ++ tailWord_7113543).sum := by decide
  have hdescent : baseEnd_7113543 < baseStart_7113543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113564 : List Nat := [2, 2, 4, 2, 1, 2, 3, 2, 5]
def baseStart_7113564 : Nat := 118140960795 + 7113564 * 2 ^ 59
def prefixEnd_7113564 : Nat := 4983230072969 + 3 ^ 40 * 7113564 * 2
def baseEnd_7113564 : Nat := 405853055391101264648369

theorem tailTrace_7113564 : CollatzResearch.WordTrace tailWord_7113564 prefixEnd_7113564 405853055391101264648369 := by
  unfold tailWord_7113564
  simp only [CollatzResearch.WordTrace]
  refine ⟨129726497000390001426589873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172968662667186668568786497 129726497000390001426589873)
  ·
    refine ⟨97294872750292501069942405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129726497000390001426589873 97294872750292501069942405)
    ·
      refine ⟨18242788640679843950614201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97294872750292501069942405 18242788640679843950614201)
      ·
        refine ⟨13682091480509882962960651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18242788640679843950614201 13682091480509882962960651)
        ·
          refine ⟨20523137220764824444440977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13682091480509882962960651 20523137220764824444440977)
          ·
            refine ⟨15392352915573618333330733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20523137220764824444440977 15392352915573618333330733)
            ·
              refine ⟨5772132343340106874999025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15392352915573618333330733 5772132343340106874999025)
              ·
                refine ⟨4329099257505080156249269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5772132343340106874999025 4329099257505080156249269)
                ·
                  refine ⟨405853055391101264648369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4329099257505080156249269 405853055391101264648369)
                  ·
                    rfl

theorem cell23_7113564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_7113564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113564 prefixEnd_7113564 := by exact prefixLift 7113564
  have htrace : WordTrace (prefixWord ++ tailWord_7113564) baseStart_7113564 baseEnd_7113564 := by
    simpa [prefixWord, tailWord_7113564, baseEnd_7113564] using wordTrace_append hprefix tailTrace_7113564
  have hstable : (prefixWord ++ tailWord_7113564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113564).length < 2 ^ (prefixWord ++ tailWord_7113564).sum := by decide
  have hdescent : baseEnd_7113564 < baseStart_7113564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113580 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 1, 6, 2]
def baseStart_7113580 : Nat := 118140960795 + 7113580 * 2 ^ 59
def prefixEnd_7113580 : Nat := 4983230072969 + 3 ^ 40 * 7113580 * 2
def baseEnd_7113580 : Nat := 3652685714210383319235247

theorem tailTrace_7113580 : CollatzResearch.WordTrace tailWord_7113580 prefixEnd_7113580 3652685714210383319235247 := by
  unfold tailWord_7113580
  simp only [CollatzResearch.WordTrace]
  refine ⟨129726788784361018792881097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172969051712481358390508129 129726788784361018792881097)
  ·
    refine ⟨97295091588270764094660823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129726788784361018792881097 97295091588270764094660823)
    ·
      refine ⟨145942637382406146141991235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97295091588270764094660823 145942637382406146141991235)
      ·
        refine ⟨218913956073609219212986853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145942637382406146141991235 218913956073609219212986853)
        ·
          refine ⟨41046366763801728602435035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218913956073609219212986853 41046366763801728602435035)
          ·
            refine ⟨61569550145702592903652553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41046366763801728602435035 61569550145702592903652553)
            ·
              refine ⟨46177162609276944677739415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61569550145702592903652553 46177162609276944677739415)
              ·
                refine ⟨69265743913915417016609123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46177162609276944677739415 69265743913915417016609123)
                ·
                  refine ⟨103898615870873125524913685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69265743913915417016609123 103898615870873125524913685)
                  ·
                    refine ⟨4870247618947177758980329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103898615870873125524913685 4870247618947177758980329)
                    ·
                      refine ⟨3652685714210383319235247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4870247618947177758980329 3652685714210383319235247)
                      ·
                        rfl

theorem cell23_7113580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 6, 2].length) (baseStart_7113580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113580 prefixEnd_7113580 := by exact prefixLift 7113580
  have htrace : WordTrace (prefixWord ++ tailWord_7113580) baseStart_7113580 baseEnd_7113580 := by
    simpa [prefixWord, tailWord_7113580, baseEnd_7113580] using wordTrace_append hprefix tailTrace_7113580
  have hstable : (prefixWord ++ tailWord_7113580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113580).length < 2 ^ (prefixWord ++ tailWord_7113580).sum := by decide
  have hdescent : baseEnd_7113580 < baseStart_7113580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113583 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 3]
def baseStart_7113583 : Nat := 118140960795 + 7113583 * 2 ^ 59
def prefixEnd_7113583 : Nat := 4983230072969 + 3 ^ 40 * 7113583 * 2
def baseEnd_7113583 : Nat := 3652687254652346807497733

theorem tailTrace_7113583 : CollatzResearch.WordTrace tailWord_7113583 prefixEnd_7113583 3652687254652346807497733 := by
  unfold tailWord_7113583
  simp only [CollatzResearch.WordTrace]
  refine ⟨259453686987711169098121403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172969124658474112732080935 259453686987711169098121403)
  ·
    refine ⟨389180530481566753647182105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259453686987711169098121403 389180530481566753647182105)
    ·
      refine ⟨291885397861175065235386579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389180530481566753647182105 291885397861175065235386579)
      ·
        refine ⟨437828096791762597853079869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291885397861175065235386579 437828096791762597853079869)
        ·
          refine ⟨164185536296910974194904951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437828096791762597853079869 164185536296910974194904951)
          ·
            refine ⟨246278304445366461292357427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164185536296910974194904951 246278304445366461292357427)
            ·
              refine ⟨369417456668049691938536141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246278304445366461292357427 369417456668049691938536141)
              ·
                refine ⟨138531546250518634476951053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369417456668049691938536141 138531546250518634476951053)
                ·
                  refine ⟨51949329843944487928856645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138531546250518634476951053 51949329843944487928856645)
                  ·
                    refine ⟨9740499345739591486660621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51949329843944487928856645 9740499345739591486660621)
                    ·
                      refine ⟨3652687254652346807497733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9740499345739591486660621 3652687254652346807497733)
                      ·
                        rfl

theorem cell23_7113583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 3].length) (baseStart_7113583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113583 prefixEnd_7113583 := by exact prefixLift 7113583
  have htrace : WordTrace (prefixWord ++ tailWord_7113583) baseStart_7113583 baseEnd_7113583 := by
    simpa [prefixWord, tailWord_7113583, baseEnd_7113583] using wordTrace_append hprefix tailTrace_7113583
  have hstable : (prefixWord ++ tailWord_7113583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113583).length < 2 ^ (prefixWord ++ tailWord_7113583).sum := by decide
  have hdescent : baseEnd_7113583 < baseStart_7113583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113623 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_7113623 : Nat := 118140960795 + 7113623 * 2 ^ 59
def prefixEnd_7113623 : Nat := 4983230072969 + 3 ^ 40 * 7113623 * 2
def baseEnd_7113623 : Nat := 3652707793878526650997549

theorem tailTrace_7113623 : CollatzResearch.WordTrace tailWord_7113623 prefixEnd_7113623 3652707793878526650997549 := by
  unfold tailWord_7113623
  simp only [CollatzResearch.WordTrace]
  refine ⟨259455145907566255929577523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172970097271710837286385015 259455145907566255929577523)
  ·
    refine ⟨389182718861349383894366285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259455145907566255929577523 389182718861349383894366285)
    ·
      refine ⟨145943519573006018960387357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389182718861349383894366285 145943519573006018960387357)
      ·
        refine ⟨54728819839877257110145259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145943519573006018960387357 54728819839877257110145259)
        ·
          refine ⟨82093229759815885665217889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54728819839877257110145259 82093229759815885665217889)
          ·
            refine ⟨61569922319861914248913417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82093229759815885665217889 61569922319861914248913417)
            ·
              refine ⟨46177441739896435686685063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61569922319861914248913417 46177441739896435686685063)
              ·
                refine ⟨69266162609844653530027595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46177441739896435686685063 69266162609844653530027595)
                ·
                  refine ⟨103899243914766980295041393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69266162609844653530027595 103899243914766980295041393)
                  ·
                    refine ⟨77924432936075235221281045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103899243914766980295041393 77924432936075235221281045)
                    ·
                      refine ⟨3652707793878526650997549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77924432936075235221281045 3652707793878526650997549)
                      ·
                        rfl

theorem cell23_7113623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_7113623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113623 prefixEnd_7113623 := by exact prefixLift 7113623
  have htrace : WordTrace (prefixWord ++ tailWord_7113623) baseStart_7113623 baseEnd_7113623 := by
    simpa [prefixWord, tailWord_7113623, baseEnd_7113623] using wordTrace_append hprefix tailTrace_7113623
  have hstable : (prefixWord ++ tailWord_7113623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113623).length < 2 ^ (prefixWord ++ tailWord_7113623).sum := by decide
  have hdescent : baseEnd_7113623 < baseStart_7113623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113657 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 1, 5, 2]
def baseStart_7113657 : Nat := 118140960795 + 7113657 * 2 ^ 59
def prefixEnd_7113657 : Nat := 4983230072969 + 3 ^ 40 * 7113657 * 2
def baseEnd_7113657 : Nat := 3652725252220779517972393

theorem tailTrace_7113657 : CollatzResearch.WordTrace tailWord_7113657 prefixEnd_7113657 3652725252220779517972393 := by
  unfold tailWord_7113657
  simp only [CollatzResearch.WordTrace]
  refine ⟨259456385989443079736315225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172970923992962053157543483 259456385989443079736315225)
  ·
    refine ⟨194592289492082309802236419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259456385989443079736315225 194592289492082309802236419)
    ·
      refine ⟨291888434238123464703354629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194592289492082309802236419 291888434238123464703354629)
      ·
        refine ⟨54729081419648149631878993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291888434238123464703354629 54729081419648149631878993)
        ·
          refine ⟨41046811064736112223909245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54729081419648149631878993 41046811064736112223909245)
          ·
            refine ⟨15392554149276042083965967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41046811064736112223909245 15392554149276042083965967)
            ·
              refine ⟨23088831223914063125948951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15392554149276042083965967 23088831223914063125948951)
              ·
                refine ⟨34633246835871094688923427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23088831223914063125948951 34633246835871094688923427)
                ·
                  refine ⟨51949870253806642033385141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34633246835871094688923427 51949870253806642033385141)
                  ·
                    refine ⟨4870300336294372690629857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51949870253806642033385141 4870300336294372690629857)
                    ·
                      refine ⟨3652725252220779517972393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4870300336294372690629857 3652725252220779517972393)
                      ·
                        rfl

theorem cell23_7113657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_7113657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113657 prefixEnd_7113657 := by exact prefixLift 7113657
  have htrace : WordTrace (prefixWord ++ tailWord_7113657) baseStart_7113657 baseEnd_7113657 := by
    simpa [prefixWord, tailWord_7113657, baseEnd_7113657] using wordTrace_append hprefix tailTrace_7113657
  have hstable : (prefixWord ++ tailWord_7113657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113657).length < 2 ^ (prefixWord ++ tailWord_7113657).sum := by decide
  have hdescent : baseEnd_7113657 < baseStart_7113657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113663 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 3, 6]
def baseStart_7113663 : Nat := 118140960795 + 7113663 * 2 ^ 59
def prefixEnd_7113663 : Nat := 4983230072969 + 3 ^ 40 * 7113663 * 2
def baseEnd_7113663 : Nat := 1217576111034902164832455

theorem tailTrace_7113663 : CollatzResearch.WordTrace tailWord_7113663 prefixEnd_7113663 1217576111034902164832455 := by
  unfold tailWord_7113663
  simp only [CollatzResearch.WordTrace]
  refine ⟨259456604827421342761033643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172971069884947561840689095 259456604827421342761033643)
  ·
    refine ⟨389184907241132014141550465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259456604827421342761033643 389184907241132014141550465)
    ·
      refine ⟨291888680430849010606162849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389184907241132014141550465 291888680430849010606162849)
      ·
        refine ⟨218916510323136757954622137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291888680430849010606162849 218916510323136757954622137)
        ·
          refine ⟨164187382742352568465966603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218916510323136757954622137 164187382742352568465966603)
          ·
            refine ⟨246281074113528852698949905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164187382742352568465966603 246281074113528852698949905)
            ·
              refine ⟨184710805585146639524212429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246281074113528852698949905 184710805585146639524212429)
              ·
                refine ⟨69266552094429989821579661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184710805585146639524212429 69266552094429989821579661)
                ·
                  refine ⟨25974957035411246183092373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69266552094429989821579661 25974957035411246183092373)
                  ·
                    refine ⟨1217576111034902164832455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25974957035411246183092373 1217576111034902164832455)
                    ·
                      rfl

theorem cell23_7113663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_7113663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113663 prefixEnd_7113663 := by exact prefixLift 7113663
  have htrace : WordTrace (prefixWord ++ tailWord_7113663) baseStart_7113663 baseEnd_7113663 := by
    simpa [prefixWord, tailWord_7113663, baseEnd_7113663] using wordTrace_append hprefix tailTrace_7113663
  have hstable : (prefixWord ++ tailWord_7113663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113663).length < 2 ^ (prefixWord ++ tailWord_7113663).sum := by decide
  have hdescent : baseEnd_7113663 < baseStart_7113663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113664 : List Nat := [2, 1, 1, 2, 3, 3, 1, 5, 1, 1, 3]
def baseStart_7113664 : Nat := 118140960795 + 7113664 * 2 ^ 59
def prefixEnd_7113664 : Nat := 4983230072969 + 3 ^ 40 * 7113664 * 2
def baseEnd_7113664 : Nat := 3652728846585360990584861

theorem tailTrace_7113664 : CollatzResearch.WordTrace tailWord_7113664 prefixEnd_7113664 3652728846585360990584861 := by
  unfold tailWord_7113664
  simp only [CollatzResearch.WordTrace]
  refine ⟨129728320650208859965910023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172971094200278479954546697 129728320650208859965910023)
  ·
    refine ⟨194592480975313289948865035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129728320650208859965910023 194592480975313289948865035)
    ·
      refine ⟨291888721462969934923297553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194592480975313289948865035 291888721462969934923297553)
      ·
        refine ⟨218916541097227451192473165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291888721462969934923297553 218916541097227451192473165)
        ·
          refine ⟨82093702911460294197177437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218916541097227451192473165 82093702911460294197177437)
          ·
            refine ⟨30785138591797610323941539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82093702911460294197177437 30785138591797610323941539)
            ·
              refine ⟨46177707887696415485912309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30785138591797610323941539 46177707887696415485912309)
              ·
                refine ⟨4329160114471538951804279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46177707887696415485912309 4329160114471538951804279)
                ·
                  refine ⟨6493740171707308427706419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4329160114471538951804279 6493740171707308427706419)
                  ·
                    refine ⟨9740610257560962641559629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6493740171707308427706419 9740610257560962641559629)
                    ·
                      refine ⟨3652728846585360990584861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9740610257560962641559629 3652728846585360990584861)
                      ·
                        rfl

theorem cell23_7113664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 1, 1, 3].length) (baseStart_7113664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113664 prefixEnd_7113664 := by exact prefixLift 7113664
  have htrace : WordTrace (prefixWord ++ tailWord_7113664) baseStart_7113664 baseEnd_7113664 := by
    simpa [prefixWord, tailWord_7113664, baseEnd_7113664] using wordTrace_append hprefix tailTrace_7113664
  have hstable : (prefixWord ++ tailWord_7113664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113664).length < 2 ^ (prefixWord ++ tailWord_7113664).sum := by decide
  have hdescent : baseEnd_7113664 < baseStart_7113664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113690 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_7113690 : Nat := 118140960795 + 7113690 * 2 ^ 59
def prefixEnd_7113690 : Nat := 4983230072969 + 3 ^ 40 * 7113690 * 2
def baseEnd_7113690 : Nat := 3652742197082377888859741

theorem tailTrace_7113690 : CollatzResearch.WordTrace tailWord_7113690 prefixEnd_7113690 3652742197082377888859741 := by
  unfold tailWord_7113690
  simp only [CollatzResearch.WordTrace]
  refine ⟨64864397399580881593066631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172971726398882350914844349 64864397399580881593066631)
  ·
    refine ⟨97296596099371322389599947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64864397399580881593066631 97296596099371322389599947)
    ·
      refine ⟨145944894149056983584399921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97296596099371322389599947 145944894149056983584399921)
      ·
        refine ⟨109458670611792737688299941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145944894149056983584399921 109458670611792737688299941)
        ·
          refine ⟨20523500739711138316556239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109458670611792737688299941 20523500739711138316556239)
          ·
            refine ⟨30785251109566707474834359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20523500739711138316556239 30785251109566707474834359)
            ·
              refine ⟨46177876664350061212251539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30785251109566707474834359 46177876664350061212251539)
              ·
                refine ⟨69266814996525091818377309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46177876664350061212251539 69266814996525091818377309)
                ·
                  refine ⟨25975055623696909431891491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69266814996525091818377309 25975055623696909431891491)
                  ·
                    refine ⟨38962583435545364147837237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25975055623696909431891491 38962583435545364147837237)
                    ·
                      refine ⟨3652742197082377888859741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38962583435545364147837237 3652742197082377888859741)
                      ·
                        rfl

theorem cell23_7113690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_7113690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113690 prefixEnd_7113690 := by exact prefixLift 7113690
  have htrace : WordTrace (prefixWord ++ tailWord_7113690) baseStart_7113690 baseEnd_7113690 := by
    simpa [prefixWord, tailWord_7113690, baseEnd_7113690] using wordTrace_append hprefix tailTrace_7113690
  have hstable : (prefixWord ++ tailWord_7113690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113690).length < 2 ^ (prefixWord ++ tailWord_7113690).sum := by decide
  have hdescent : baseEnd_7113690 < baseStart_7113690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113700 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_7113700 : Nat := 118140960795 + 7113700 * 2 ^ 59
def prefixEnd_7113700 : Nat := 4983230072969 + 3 ^ 40 * 7113700 * 2
def baseEnd_7113700 : Nat := 3652747331888922849734695

theorem tailTrace_7113700 : CollatzResearch.WordTrace tailWord_7113700 prefixEnd_7113700 3652747331888922849734695 := by
  unfold tailWord_7113700
  simp only [CollatzResearch.WordTrace]
  refine ⟨129728977164143649040065277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172971969552191532053420369 129728977164143649040065277)
  ·
    refine ⟨48648366436553868390024479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129728977164143649040065277 48648366436553868390024479)
    ·
      refine ⟨72972549654830802585036719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48648366436553868390024479 72972549654830802585036719)
      ·
        refine ⟨109458824482246203877555079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72972549654830802585036719 109458824482246203877555079)
        ·
          refine ⟨164188236723369305816332619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109458824482246203877555079 164188236723369305816332619)
          ·
            refine ⟨246282355085053958724498929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164188236723369305816332619 246282355085053958724498929)
            ·
              refine ⟨184711766313790469043374197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246282355085053958724498929 184711766313790469043374197)
              ·
                refine ⟨17316728091917856472816331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184711766313790469043374197 17316728091917856472816331)
                ·
                  refine ⟨25975092137876784709224497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17316728091917856472816331 25975092137876784709224497)
                  ·
                    refine ⟨19481319103407588531918373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25975092137876784709224497 19481319103407588531918373)
                    ·
                      refine ⟨3652747331888922849734695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19481319103407588531918373 3652747331888922849734695)
                      ·
                        rfl

theorem cell23_7113700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_7113700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113700 prefixEnd_7113700 := by exact prefixLift 7113700
  have htrace : WordTrace (prefixWord ++ tailWord_7113700) baseStart_7113700 baseEnd_7113700 := by
    simpa [prefixWord, tailWord_7113700, baseEnd_7113700] using wordTrace_append hprefix tailTrace_7113700
  have hstable : (prefixWord ++ tailWord_7113700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113700).length < 2 ^ (prefixWord ++ tailWord_7113700).sum := by decide
  have hdescent : baseEnd_7113700 < baseStart_7113700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113704 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_7113704 : Nat := 118140960795 + 7113704 * 2 ^ 59
def prefixEnd_7113704 : Nat := 4983230072969 + 3 ^ 40 * 7113704 * 2
def baseEnd_7113704 : Nat := 3652749385811540834084677

theorem tailTrace_7113704 : CollatzResearch.WordTrace tailWord_7113704 prefixEnd_7113704 3652749385811540834084677 := by
  unfold tailWord_7113704
  simp only [CollatzResearch.WordTrace]
  refine ⟨129729050110136403381638083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172972066813515204508850777 129729050110136403381638083)
  ·
    refine ⟨194593575165204605072457125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129729050110136403381638083 194593575165204605072457125)
    ·
      refine ⟨36486295343475863451085711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194593575165204605072457125 36486295343475863451085711)
      ·
        refine ⟨54729443015213795176628567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36486295343475863451085711 54729443015213795176628567)
        ·
          refine ⟨82094164522820692764942851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54729443015213795176628567 82094164522820692764942851)
          ·
            refine ⟨123141246784231039147414277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82094164522820692764942851 123141246784231039147414277)
            ·
              refine ⟨23088983772043319840140177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123141246784231039147414277 23088983772043319840140177)
              ·
                refine ⟨17316737829032489880105133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23088983772043319840140177 17316737829032489880105133)
                ·
                  refine ⟨6493776685887183705039425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17316737829032489880105133 6493776685887183705039425)
                  ·
                    refine ⟨4870332514415387778779569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6493776685887183705039425 4870332514415387778779569)
                    ·
                      refine ⟨3652749385811540834084677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4870332514415387778779569 3652749385811540834084677)
                      ·
                        rfl

theorem cell23_7113704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_7113704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113704 prefixEnd_7113704 := by exact prefixLift 7113704
  have htrace : WordTrace (prefixWord ++ tailWord_7113704) baseStart_7113704 baseEnd_7113704 := by
    simpa [prefixWord, tailWord_7113704, baseEnd_7113704] using wordTrace_append hprefix tailTrace_7113704
  have hstable : (prefixWord ++ tailWord_7113704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113704).length < 2 ^ (prefixWord ++ tailWord_7113704).sum := by decide
  have hdescent : baseEnd_7113704 < baseStart_7113704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113720 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 3, 3, 3]
def baseStart_7113720 : Nat := 118140960795 + 7113720 * 2 ^ 59
def prefixEnd_7113720 : Nat := 4983230072969 + 3 ^ 40 * 7113720 * 2
def baseEnd_7113720 : Nat := 3652757601502012771484603

theorem tailTrace_7113720 : CollatzResearch.WordTrace tailWord_7113720 prefixEnd_7113720 3652757601502012771484603 := by
  unfold tailWord_7113720
  simp only [CollatzResearch.WordTrace]
  refine ⟨129729341894107420747929307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172972455858809894330572409 129729341894107420747929307)
  ·
    refine ⟨194594012841161131121893961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129729341894107420747929307 194594012841161131121893961)
    ·
      refine ⟨145945509630870848341420471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194594012841161131121893961 145945509630870848341420471)
      ·
        refine ⟨218918264446306272512130707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145945509630870848341420471 218918264446306272512130707)
        ·
          refine ⟨328377396669459408768196061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218918264446306272512130707 328377396669459408768196061)
          ·
            refine ⟨123141523751047278288073523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328377396669459408768196061 123141523751047278288073523)
            ·
              refine ⟨184712285626570917432110285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123141523751047278288073523 184712285626570917432110285)
              ·
                refine ⟨69267107109964094037041357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184712285626570917432110285 69267107109964094037041357)
                ·
                  refine ⟨25975165166236535263890509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69267107109964094037041357 25975165166236535263890509)
                  ·
                    refine ⟨9740686937338700723958941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25975165166236535263890509 9740686937338700723958941)
                    ·
                      refine ⟨3652757601502012771484603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9740686937338700723958941 3652757601502012771484603)
                      ·
                        rfl

theorem cell23_7113720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_7113720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113720 prefixEnd_7113720 := by exact prefixLift 7113720
  have htrace : WordTrace (prefixWord ++ tailWord_7113720) baseStart_7113720 baseEnd_7113720 := by
    simpa [prefixWord, tailWord_7113720, baseEnd_7113720] using wordTrace_append hprefix tailTrace_7113720
  have hstable : (prefixWord ++ tailWord_7113720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113720).length < 2 ^ (prefixWord ++ tailWord_7113720).sum := by decide
  have hdescent : baseEnd_7113720 < baseStart_7113720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113723 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 1, 9]
def baseStart_7113723 : Nat := 118140960795 + 7113723 * 2 ^ 59
def prefixEnd_7113723 : Nat := 4983230072969 + 3 ^ 40 * 7113723 * 2
def baseEnd_7113723 : Nat := 1217586380647992086582363

theorem tailTrace_7113723 : CollatzResearch.WordTrace tailWord_7113723 prefixEnd_7113723 1217586380647992086582363 := by
  unfold tailWord_7113723
  simp only [CollatzResearch.WordTrace]
  refine ⟨259458793207203973008217823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172972528804802648672145215 259458793207203973008217823)
  ·
    refine ⟨389188189810805959512326735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259458793207203973008217823 389188189810805959512326735)
    ·
      refine ⟨583782284716208939268490103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389188189810805959512326735 583782284716208939268490103)
      ·
        refine ⟨875673427074313408902735155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583782284716208939268490103 875673427074313408902735155)
        ·
          refine ⟨1313510140611470113354102733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875673427074313408902735155 1313510140611470113354102733)
          ·
            refine ⟨492566302729301292507788525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1313510140611470113354102733 492566302729301292507788525)
            ·
              refine ⟨184712363523487984690420697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 492566302729301292507788525 184712363523487984690420697)
              ·
                refine ⟨138534272642615988517815523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184712363523487984690420697 138534272642615988517815523)
                ·
                  refine ⟨207801408963923982776723285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138534272642615988517815523 207801408963923982776723285)
                  ·
                    refine ⟨1217586380647992086582363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 207801408963923982776723285 1217586380647992086582363)
                    ·
                      rfl

theorem cell23_7113723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 9].length) (baseStart_7113723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113723 prefixEnd_7113723 := by exact prefixLift 7113723
  have htrace : WordTrace (prefixWord ++ tailWord_7113723) baseStart_7113723 baseEnd_7113723 := by
    simpa [prefixWord, tailWord_7113723, baseEnd_7113723] using wordTrace_append hprefix tailTrace_7113723
  have hstable : (prefixWord ++ tailWord_7113723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113723).length < 2 ^ (prefixWord ++ tailWord_7113723).sum := by decide
  have hdescent : baseEnd_7113723 < baseStart_7113723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113747 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 3, 3, 2]
def baseStart_7113747 : Nat := 118140960795 + 7113747 * 2 ^ 59
def prefixEnd_7113747 : Nat := 4983230072969 + 3 ^ 40 * 7113747 * 2
def baseEnd_7113747 : Nat := 3652771465479684165846979

theorem tailTrace_7113747 : CollatzResearch.WordTrace tailWord_7113747 prefixEnd_7113747 3652771465479684165846979 := by
  unfold tailWord_7113747
  simp only [CollatzResearch.WordTrace]
  refine ⟨259459668559117025107091495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172973112372744683404727663 259459668559117025107091495)
  ·
    refine ⟨389189502838675537660637243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259459668559117025107091495 389189502838675537660637243)
    ·
      refine ⟨583784254258013306490955865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389189502838675537660637243 583784254258013306490955865)
      ·
        refine ⟨437838190693509979868216899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583784254258013306490955865 437838190693509979868216899)
        ·
          refine ⟨656757286040264969802325349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437838190693509979868216899 656757286040264969802325349)
          ·
            refine ⟨123141991132549681837936003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 656757286040264969802325349 123141991132549681837936003)
            ·
              refine ⟨184712986698824522756904005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123141991132549681837936003 184712986698824522756904005)
              ·
                refine ⟨34633685006029598016919501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184712986698824522756904005 34633685006029598016919501)
                ·
                  refine ⟨12987631877261099256344813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34633685006029598016919501 12987631877261099256344813)
                  ·
                    refine ⟨4870361953972912221129305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12987631877261099256344813 4870361953972912221129305)
                    ·
                      refine ⟨3652771465479684165846979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4870361953972912221129305 3652771465479684165846979)
                      ·
                        rfl

theorem cell23_7113747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 3, 2].length) (baseStart_7113747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113747 prefixEnd_7113747 := by exact prefixLift 7113747
  have htrace : WordTrace (prefixWord ++ tailWord_7113747) baseStart_7113747 baseEnd_7113747 := by
    simpa [prefixWord, tailWord_7113747, baseEnd_7113747] using wordTrace_append hprefix tailTrace_7113747
  have hstable : (prefixWord ++ tailWord_7113747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113747).length < 2 ^ (prefixWord ++ tailWord_7113747).sum := by decide
  have hdescent : baseEnd_7113747 < baseStart_7113747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113754 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3]
def baseStart_7113754 : Nat := 118140960795 + 7113754 * 2 ^ 59
def prefixEnd_7113754 : Nat := 4983230072969 + 3 ^ 40 * 7113754 * 2
def baseEnd_7113754 : Nat := 3652775059844265638459447

theorem tailTrace_7113754 : CollatzResearch.WordTrace tailWord_7113754 prefixEnd_7113754 3652775059844265638459447 := by
  unfold tailWord_7113754
  simp only [CollatzResearch.WordTrace]
  refine ⟨64864980967522916325649079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172973282580061110201730877 64864980967522916325649079)
  ·
    refine ⟨97297471451284374488473619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64864980967522916325649079 97297471451284374488473619)
    ·
      refine ⟨145946207176926561732710429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97297471451284374488473619 145946207176926561732710429)
      ·
        refine ⟨54729827691347460649766411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145946207176926561732710429 54729827691347460649766411)
        ·
          refine ⟨82094741537021190974649617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54729827691347460649766411 82094741537021190974649617)
          ·
            refine ⟨61571056152765893230987213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82094741537021190974649617 61571056152765893230987213)
            ·
              refine ⟨23089146057287209961620205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61571056152765893230987213 23089146057287209961620205)
              ·
                refine ⟨8658429771482703735607577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23089146057287209961620205 8658429771482703735607577)
                ·
                  refine ⟨6493822328612027801705683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8658429771482703735607577 6493822328612027801705683)
                  ·
                    refine ⟨9740733492918041702558525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6493822328612027801705683 9740733492918041702558525)
                    ·
                      refine ⟨3652775059844265638459447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9740733492918041702558525 3652775059844265638459447)
                      ·
                        rfl

theorem cell23_7113754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_7113754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113754 prefixEnd_7113754 := by exact prefixLift 7113754
  have htrace : WordTrace (prefixWord ++ tailWord_7113754) baseStart_7113754 baseEnd_7113754 := by
    simpa [prefixWord, tailWord_7113754, baseEnd_7113754] using wordTrace_append hprefix tailTrace_7113754
  have hstable : (prefixWord ++ tailWord_7113754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113754).length < 2 ^ (prefixWord ++ tailWord_7113754).sum := by decide
  have hdescent : baseEnd_7113754 < baseStart_7113754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113800 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 7]
def baseStart_7113800 : Nat := 118140960795 + 7113800 * 2 ^ 59
def prefixEnd_7113800 : Nat := 4983230072969 + 3 ^ 40 * 7113800 * 2
def baseEnd_7113800 : Nat := 405866519994930273164915

theorem tailTrace_7113800 : CollatzResearch.WordTrace tailWord_7113800 prefixEnd_7113800 405866519994930273164915 := by
  unfold tailWord_7113800
  simp only [CollatzResearch.WordTrace]
  refine ⟨129730800813962507579385427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172974401085283343439180569 129730800813962507579385427)
  ·
    refine ⟨194596201220943761369078141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129730800813962507579385427 194596201220943761369078141)
    ·
      refine ⟨72973575457853910513404303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194596201220943761369078141 72973575457853910513404303)
      ·
        refine ⟨109460363186780865770106455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72973575457853910513404303 109460363186780865770106455)
        ·
          refine ⟨164190544780171298655159683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109460363186780865770106455 164190544780171298655159683)
          ·
            refine ⟨246285817170256947982739525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164190544780171298655159683 246285817170256947982739525)
            ·
              refine ⟨46178590719423177746763661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246285817170256947982739525 46178590719423177746763661)
              ·
                refine ⟨17316971519783691655036373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46178590719423177746763661 17316971519783691655036373)
                ·
                  refine ⟨405866519994930273164915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17316971519783691655036373 405866519994930273164915)
                  ·
                    rfl

theorem cell23_7113800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 7].length) (baseStart_7113800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113800 prefixEnd_7113800 := by exact prefixLift 7113800
  have htrace : WordTrace (prefixWord ++ tailWord_7113800) baseStart_7113800 baseEnd_7113800 := by
    simpa [prefixWord, tailWord_7113800, baseEnd_7113800] using wordTrace_append hprefix tailTrace_7113800
  have hstable : (prefixWord ++ tailWord_7113800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113800).length < 2 ^ (prefixWord ++ tailWord_7113800).sum := by decide
  have hdescent : baseEnd_7113800 < baseStart_7113800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113832 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7113832 : Nat := 118140960795 + 7113832 * 2 ^ 59
def prefixEnd_7113832 : Nat := 4983230072969 + 3 ^ 40 * 7113832 * 2
def baseEnd_7113832 : Nat := 3652815111335316333284089

theorem tailTrace_7113832 : CollatzResearch.WordTrace tailWord_7113832 prefixEnd_7113832 3652815111335316333284089 := by
  unfold tailWord_7113832
  simp only [CollatzResearch.WordTrace]
  refine ⟨129731384381904542311967875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172975179175872723082623833 129731384381904542311967875)
  ·
    refine ⟨194597076572856813467951813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129731384381904542311967875 194597076572856813467951813)
    ·
      refine ⟨36486951857410652525240965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194597076572856813467951813 36486951857410652525240965)
      ·
        refine ⟨6841303473264497348482681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36486951857410652525240965 6841303473264497348482681)
        ·
          refine ⟨5130977604948373011362011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6841303473264497348482681 5130977604948373011362011)
          ·
            refine ⟨7696466407422559517043017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5130977604948373011362011 7696466407422559517043017)
            ·
              refine ⟨5772349805566919637782263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7696466407422559517043017 5772349805566919637782263)
              ·
                refine ⟨8658524708350379456673395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5772349805566919637782263 8658524708350379456673395)
                ·
                  refine ⟨12987787062525569185010093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8658524708350379456673395 12987787062525569185010093)
                  ·
                    refine ⟨4870420148447088444378785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12987787062525569185010093 4870420148447088444378785)
                    ·
                      refine ⟨3652815111335316333284089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4870420148447088444378785 3652815111335316333284089)
                      ·
                        rfl

theorem cell23_7113832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7113832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113832 prefixEnd_7113832 := by exact prefixLift 7113832
  have htrace : WordTrace (prefixWord ++ tailWord_7113832) baseStart_7113832 baseEnd_7113832 := by
    simpa [prefixWord, tailWord_7113832, baseEnd_7113832] using wordTrace_append hprefix tailTrace_7113832
  have hstable : (prefixWord ++ tailWord_7113832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113832).length < 2 ^ (prefixWord ++ tailWord_7113832).sum := by decide
  have hdescent : baseEnd_7113832 < baseStart_7113832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113834 : List Nat := [3, 1, 3, 2, 2, 1, 1, 5, 5]
def baseStart_7113834 : Nat := 118140960795 + 7113834 * 2 ^ 59
def prefixEnd_7113834 : Nat := 4983230072969 + 3 ^ 40 * 7113834 * 2
def baseEnd_7113834 : Nat := 405868459810736147273231

theorem tailTrace_7113834 : CollatzResearch.WordTrace tailWord_7113834 prefixEnd_7113834 405868459810736147273231 := by
  unfold tailWord_7113834
  simp only [CollatzResearch.WordTrace]
  refine ⟨64865710427450459741377139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172975227806534559310339037 64865710427450459741377139)
  ·
    refine ⟨97298565641175689612065709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64865710427450459741377139 97298565641175689612065709)
    ·
      refine ⟨36486962115440883604524641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97298565641175689612065709 36486962115440883604524641)
      ·
        refine ⟨27365221586580662703393481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36486962115440883604524641 27365221586580662703393481)
        ·
          refine ⟨20523916189935497027545111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27365221586580662703393481 20523916189935497027545111)
          ·
            refine ⟨30785874284903245541317667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20523916189935497027545111 30785874284903245541317667)
            ·
              refine ⟨46178811427354868311976501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30785874284903245541317667 46178811427354868311976501)
              ·
                refine ⟨4329263571314518904247797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46178811427354868311976501 4329263571314518904247797)
                ·
                  refine ⟨405868459810736147273231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4329263571314518904247797 405868459810736147273231)
                  ·
                    rfl

theorem cell23_7113834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_7113834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113834 prefixEnd_7113834 := by exact prefixLift 7113834
  have htrace : WordTrace (prefixWord ++ tailWord_7113834) baseStart_7113834 baseEnd_7113834 := by
    simpa [prefixWord, tailWord_7113834, baseEnd_7113834] using wordTrace_append hprefix tailTrace_7113834
  have hstable : (prefixWord ++ tailWord_7113834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113834).length < 2 ^ (prefixWord ++ tailWord_7113834).sum := by decide
  have hdescent : baseEnd_7113834 < baseStart_7113834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113877 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 5, 4]
def baseStart_7113877 : Nat := 118140960795 + 7113877 * 2 ^ 59
def prefixEnd_7113877 : Nat := 4983230072969 + 3 ^ 40 * 7113877 * 2
def baseEnd_7113877 : Nat := 1217612739321589552407127

theorem tailTrace_7113877 : CollatzResearch.WordTrace tailWord_7113877 prefixEnd_7113877 1217612739321589552407127 := by
  unfold tailWord_7113877
  simp only [CollatzResearch.WordTrace]
  refine ⟨259464410048646057309323885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172976273365764038206215923 259464410048646057309323885)
  ·
    refine ⟨97299153768242271490996457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259464410048646057309323885 97299153768242271490996457)
    ·
      refine ⟨72974365326181703618247343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97299153768242271490996457 72974365326181703618247343)
      ·
        refine ⟨109461547989272555427371015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72974365326181703618247343 109461547989272555427371015)
        ·
          refine ⟨164192321983908833141056523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109461547989272555427371015 164192321983908833141056523)
          ·
            refine ⟨246288482975863249711584785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164192321983908833141056523 246288482975863249711584785)
            ·
              refine ⟨184716362231897437283688589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246288482975863249711584785 184716362231897437283688589)
              ·
                refine ⟨69268635836961538981383221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184716362231897437283688589 69268635836961538981383221)
                ·
                  refine ⟨6493934609715144279504677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69268635836961538981383221 6493934609715144279504677)
                  ·
                    refine ⟨1217612739321589552407127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6493934609715144279504677 1217612739321589552407127)
                    ·
                      rfl

theorem cell23_7113877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_7113877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113877 prefixEnd_7113877 := by exact prefixLift 7113877
  have htrace : WordTrace (prefixWord ++ tailWord_7113877) baseStart_7113877 baseEnd_7113877 := by
    simpa [prefixWord, tailWord_7113877, baseEnd_7113877] using wordTrace_append hprefix tailTrace_7113877
  have hstable : (prefixWord ++ tailWord_7113877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113877).length < 2 ^ (prefixWord ++ tailWord_7113877).sum := by decide
  have hdescent : baseEnd_7113877 < baseStart_7113877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113901 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_7113901 : Nat := 118140960795 + 7113901 * 2 ^ 59
def prefixEnd_7113901 : Nat := 4983230072969 + 3 ^ 40 * 7113901 * 2
def baseEnd_7113901 : Nat := 3652850541500476563321271

theorem tailTrace_7113901 : CollatzResearch.WordTrace tailWord_7113901 prefixEnd_7113901 3652850541500476563321271 := by
  unfold tailWord_7113901
  simp only [CollatzResearch.WordTrace]
  refine ⟨259465285400559109408197557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172976856933706072938798371 259465285400559109408197557)
  ·
    refine ⟨24324870506302416507018521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259465285400559109408197557 24324870506302416507018521)
    ·
      refine ⟨18243652879726812380263891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24324870506302416507018521 18243652879726812380263891)
      ·
        refine ⟨27365479319590218570395837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18243652879726812380263891 27365479319590218570395837)
        ·
          refine ⟨10262054744846331963898439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27365479319590218570395837 10262054744846331963898439)
          ·
            refine ⟨15393082117269497945847659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10262054744846331963898439 15393082117269497945847659)
            ·
              refine ⟨23089623175904246918771489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15393082117269497945847659 23089623175904246918771489)
              ·
                refine ⟨17317217381928185189078617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23089623175904246918771489 17317217381928185189078617)
                ·
                  refine ⟨12987913036446138891808963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17317217381928185189078617 12987913036446138891808963)
                  ·
                    refine ⟨19481869554669208337713445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12987913036446138891808963 19481869554669208337713445)
                    ·
                      refine ⟨3652850541500476563321271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19481869554669208337713445 3652850541500476563321271)
                      ·
                        rfl

theorem cell23_7113901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_7113901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113901 prefixEnd_7113901 := by exact prefixLift 7113901
  have htrace : WordTrace (prefixWord ++ tailWord_7113901) baseStart_7113901 baseEnd_7113901 := by
    simpa [prefixWord, tailWord_7113901, baseEnd_7113901] using wordTrace_append hprefix tailTrace_7113901
  have hstable : (prefixWord ++ tailWord_7113901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113901).length < 2 ^ (prefixWord ++ tailWord_7113901).sum := by decide
  have hdescent : baseEnd_7113901 < baseStart_7113901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7113977 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 5]
def baseStart_7113977 : Nat := 118140960795 + 7113977 * 2 ^ 59
def prefixEnd_7113977 : Nat := 4983230072969 + 3 ^ 40 * 7113977 * 2
def baseEnd_7113977 : Nat := 3652889566030218265970921

theorem tailTrace_7113977 : CollatzResearch.WordTrace tailWord_7113977 prefixEnd_7113977 3652889566030218265970921 := by
  unfold tailWord_7113977
  simp only [CollatzResearch.WordTrace]
  refine ⟨259468057348283774387964185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172978704898855849591976123 259468057348283774387964185)
  ·
    refine ⟨194601043011212830790973139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259468057348283774387964185 194601043011212830790973139)
    ·
      refine ⟨291901564516819246186459709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194601043011212830790973139 291901564516819246186459709)
      ·
        refine ⟨109463086693807217319922391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291901564516819246186459709 109463086693807217319922391)
        ·
          refine ⟨164194630040710825979883587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109463086693807217319922391 164194630040710825979883587)
          ·
            refine ⟨246291945061066238969825381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164194630040710825979883587 246291945061066238969825381)
            ·
              refine ⟨46179739698949919806842259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246291945061066238969825381 46179739698949919806842259)
              ·
                refine ⟨69269609548424879710263389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46179739698949919806842259 69269609548424879710263389)
                ·
                  refine ⟨25976103580659329891348771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69269609548424879710263389 25976103580659329891348771)
                  ·
                    refine ⟨38964155370988994837023157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25976103580659329891348771 38964155370988994837023157)
                    ·
                      refine ⟨3652889566030218265970921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38964155370988994837023157 3652889566030218265970921)
                      ·
                        rfl

theorem cell23_7113977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_7113977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7113977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7113977 prefixEnd_7113977 := by exact prefixLift 7113977
  have htrace : WordTrace (prefixWord ++ tailWord_7113977) baseStart_7113977 baseEnd_7113977 := by
    simpa [prefixWord, tailWord_7113977, baseEnd_7113977] using wordTrace_append hprefix tailTrace_7113977
  have hstable : (prefixWord ++ tailWord_7113977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7113977).length < 2 ^ (prefixWord ++ tailWord_7113977).sum := by decide
  have hdescent : baseEnd_7113977 < baseStart_7113977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7113977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114008 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 1, 1, 4]
def baseStart_7114008 : Nat := 118140960795 + 7114008 * 2 ^ 59
def prefixEnd_7114008 : Nat := 4983230072969 + 3 ^ 40 * 7114008 * 2
def baseEnd_7114008 : Nat := 3652905483930507644683279

theorem tailTrace_7114008 : CollatzResearch.WordTrace tailWord_7114008 prefixEnd_7114008 3652905483930507644683279 := by
  unfold tailWord_7114008
  simp only [CollatzResearch.WordTrace]
  refine ⟨129734594005585733341171339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172979458674114311121561785 129734594005585733341171339)
  ·
    refine ⟨194601891008378600011757009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129734594005585733341171339 194601891008378600011757009)
    ·
      refine ⟨145951418256283950008817757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194601891008378600011757009 145951418256283950008817757)
      ·
        refine ⟨54731781846106481253306659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145951418256283950008817757 54731781846106481253306659)
        ·
          refine ⟨82097672769159721879959989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54731781846106481253306659 82097672769159721879959989)
          ·
            refine ⟨7696656822108723926246249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82097672769159721879959989 7696656822108723926246249)
            ·
              refine ⟨5772492616581542944684687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7696656822108723926246249 5772492616581542944684687)
              ·
                refine ⟨8658738924872314417027031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5772492616581542944684687 8658738924872314417027031)
                ·
                  refine ⟨12988108387308471625540547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8658738924872314417027031 12988108387308471625540547)
                  ·
                    refine ⟨19482162580962707438310821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12988108387308471625540547 19482162580962707438310821)
                    ·
                      refine ⟨3652905483930507644683279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19482162580962707438310821 3652905483930507644683279)
                      ·
                        rfl

theorem cell23_7114008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_7114008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114008 prefixEnd_7114008 := by exact prefixLift 7114008
  have htrace : WordTrace (prefixWord ++ tailWord_7114008) baseStart_7114008 baseEnd_7114008 := by
    simpa [prefixWord, tailWord_7114008, baseEnd_7114008] using wordTrace_append hprefix tailTrace_7114008
  have hstable : (prefixWord ++ tailWord_7114008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114008).length < 2 ^ (prefixWord ++ tailWord_7114008).sum := by decide
  have hdescent : baseEnd_7114008 < baseStart_7114008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114017 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7114017 : Nat := 118140960795 + 7114017 * 2 ^ 59
def prefixEnd_7114017 : Nat := 4983230072969 + 3 ^ 40 * 7114017 * 2
def baseEnd_7114017 : Nat := 3652910105256398109470737

theorem tailTrace_7114017 : CollatzResearch.WordTrace tailWord_7114017 prefixEnd_7114017 3652910105256398109470737 := by
  unfold tailWord_7114017
  simp only [CollatzResearch.WordTrace]
  refine ⟨259469516268138861219420305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172979677512092574146280203 259469516268138861219420305)
  ·
    refine ⟨194602137201104145914565229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259469516268138861219420305 194602137201104145914565229)
    ·
      refine ⟨72975801450414054717961961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194602137201104145914565229 72975801450414054717961961)
      ·
        refine ⟨54731851087810541038471471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72975801450414054717961961 54731851087810541038471471)
        ·
          refine ⟨82097776631715811557707207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54731851087810541038471471 82097776631715811557707207)
          ·
            refine ⟨123146664947573717336560811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82097776631715811557707207 123146664947573717336560811)
            ·
              refine ⟨184719997421360576004841217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123146664947573717336560811 184719997421360576004841217)
              ·
                refine ⟨138539998066020432003630913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184719997421360576004841217 138539998066020432003630913)
                ·
                  refine ⟨103904998549515324002723185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138539998066020432003630913 103904998549515324002723185)
                  ·
                    refine ⟨77928748912136493002042389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103904998549515324002723185 77928748912136493002042389)
                    ·
                      refine ⟨3652910105256398109470737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77928748912136493002042389 3652910105256398109470737)
                      ·
                        rfl

theorem cell23_7114017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7114017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114017 prefixEnd_7114017 := by exact prefixLift 7114017
  have htrace : WordTrace (prefixWord ++ tailWord_7114017) baseStart_7114017 baseEnd_7114017 := by
    simpa [prefixWord, tailWord_7114017, baseEnd_7114017] using wordTrace_append hprefix tailTrace_7114017
  have hstable : (prefixWord ++ tailWord_7114017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114017).length < 2 ^ (prefixWord ++ tailWord_7114017).sum := by decide
  have hdescent : baseEnd_7114017 < baseStart_7114017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114038 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7114038 : Nat := 118140960795 + 7114038 * 2 ^ 59
def prefixEnd_7114038 : Nat := 4983230072969 + 3 ^ 40 * 7114038 * 2
def baseEnd_7114038 : Nat := 3652920888350142527308141

theorem tailTrace_7114038 : CollatzResearch.WordTrace tailWord_7114038 prefixEnd_7114038 3652920888350142527308141 := by
  unfold tailWord_7114038
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216892637566423862870923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172980188134041854537289845 16216892637566423862870923)
  ·
    refine ⟨24325338956349635794306385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16216892637566423862870923 24325338956349635794306385)
    ·
      refine ⟨18244004217262226845729789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24325338956349635794306385 18244004217262226845729789)
      ·
        refine ⟨6841501581473335067148671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18244004217262226845729789 6841501581473335067148671)
        ·
          refine ⟨10262252372210002600723007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6841501581473335067148671 10262252372210002600723007)
          ·
            refine ⟨15393378558315003901084511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10262252372210002600723007 15393378558315003901084511)
            ·
              refine ⟨23090067837472505851626767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15393378558315003901084511 23090067837472505851626767)
              ·
                refine ⟨34635101756208758777440151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23090067837472505851626767 34635101756208758777440151)
                ·
                  refine ⟨51952652634313138166160227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34635101756208758777440151 51952652634313138166160227)
                  ·
                    refine ⟨77928978951469707249240341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51952652634313138166160227 77928978951469707249240341)
                    ·
                      refine ⟨3652920888350142527308141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77928978951469707249240341 3652920888350142527308141)
                      ·
                        rfl

theorem cell23_7114038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7114038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114038 prefixEnd_7114038 := by exact prefixLift 7114038
  have htrace : WordTrace (prefixWord ++ tailWord_7114038) baseStart_7114038 baseEnd_7114038 := by
    simpa [prefixWord, tailWord_7114038, baseEnd_7114038] using wordTrace_append hprefix tailTrace_7114038
  have hstable : (prefixWord ++ tailWord_7114038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114038).length < 2 ^ (prefixWord ++ tailWord_7114038).sum := by decide
  have hdescent : baseEnd_7114038 < baseStart_7114038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114045 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7114045 : Nat := 118140960795 + 7114045 * 2 ^ 59
def prefixEnd_7114045 : Nat := 4983230072969 + 3 ^ 40 * 7114045 * 2
def baseEnd_7114045 : Nat := 3652924482714723999920609

theorem tailTrace_7114045 : CollatzResearch.WordTrace tailWord_7114045 prefixEnd_7114045 3652924482714723999920609 := by
  unfold tailWord_7114045
  simp only [CollatzResearch.WordTrace]
  refine ⟨259470537512037422001439589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172980358341358281334293059 259470537512037422001439589)
  ·
    refine ⟨48650725783507016625269923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259470537512037422001439589 48650725783507016625269923)
    ·
      refine ⟨72976088675260524937904885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48650725783507016625269923 72976088675260524937904885)
      ·
        refine ⟨6841508313305674212928583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72976088675260524937904885 6841508313305674212928583)
        ·
          refine ⟨10262262469958511319392875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6841508313305674212928583 10262262469958511319392875)
          ·
            refine ⟨15393393704937766979089313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10262262469958511319392875 15393393704937766979089313)
            ·
              refine ⟨11545045278703325234316985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15393393704937766979089313 11545045278703325234316985)
              ·
                refine ⟨8658783959027493925737739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11545045278703325234316985 8658783959027493925737739)
                ·
                  refine ⟨12988175938541240888606609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8658783959027493925737739 12988175938541240888606609)
                  ·
                    refine ⟨9741131953905930666454957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12988175938541240888606609 9741131953905930666454957)
                    ·
                      refine ⟨3652924482714723999920609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9741131953905930666454957 3652924482714723999920609)
                      ·
                        rfl

theorem cell23_7114045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7114045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114045 prefixEnd_7114045 := by exact prefixLift 7114045
  have htrace : WordTrace (prefixWord ++ tailWord_7114045) baseStart_7114045 baseEnd_7114045 := by
    simpa [prefixWord, tailWord_7114045, baseEnd_7114045] using wordTrace_append hprefix tailTrace_7114045
  have hstable : (prefixWord ++ tailWord_7114045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114045).length < 2 ^ (prefixWord ++ tailWord_7114045).sum := by decide
  have hdescent : baseEnd_7114045 < baseStart_7114045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114057 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 1, 8]
def baseStart_7114057 : Nat := 118140960795 + 7114057 * 2 ^ 59
def prefixEnd_7114057 : Nat := 4983230072969 + 3 ^ 40 * 7114057 * 2
def baseEnd_7114057 : Nat := 1217643548160859317656851

theorem tailTrace_7114057 : CollatzResearch.WordTrace tailWord_7114057 prefixEnd_7114057 1217643548160859317656851 := by
  unfold tailWord_7114057
  simp only [CollatzResearch.WordTrace]
  refine ⟨259470975187993948050876425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172980650125329298700584283 259470975187993948050876425)
  ·
    refine ⟨194603231390995461038157319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259470975187993948050876425 194603231390995461038157319)
    ·
      refine ⟨291904847086493191557235979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194603231390995461038157319 291904847086493191557235979)
      ·
        refine ⟨437857270629739787335853969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291904847086493191557235979 437857270629739787335853969)
        ·
          refine ⟨328392952972304840501890477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437857270629739787335853969 328392952972304840501890477)
          ·
            refine ⟨123147357364614315188208929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328392952972304840501890477 123147357364614315188208929)
            ·
              refine ⟨92360518023460736391156697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123147357364614315188208929 92360518023460736391156697)
              ·
                refine ⟨69270388517595552293367523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92360518023460736391156697 69270388517595552293367523)
                ·
                  refine ⟨103905582776393328440051285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69270388517595552293367523 103905582776393328440051285)
                  ·
                    refine ⟨1217643548160859317656851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103905582776393328440051285 1217643548160859317656851)
                    ·
                      rfl

theorem cell23_7114057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_7114057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114057 prefixEnd_7114057 := by exact prefixLift 7114057
  have htrace : WordTrace (prefixWord ++ tailWord_7114057) baseStart_7114057 baseEnd_7114057 := by
    simpa [prefixWord, tailWord_7114057, baseEnd_7114057] using wordTrace_append hprefix tailTrace_7114057
  have hstable : (prefixWord ++ tailWord_7114057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114057).length < 2 ^ (prefixWord ++ tailWord_7114057).sum := by decide
  have hdescent : baseEnd_7114057 < baseStart_7114057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114068 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_7114068 : Nat := 118140960795 + 7114068 * 2 ^ 59
def prefixEnd_7114068 : Nat := 4983230072969 + 3 ^ 40 * 7114068 * 2
def baseEnd_7114068 : Nat := 3652936292769777409933003

theorem tailTrace_7114068 : CollatzResearch.WordTrace tailWord_7114068 prefixEnd_7114068 3652936292769777409933003 := by
  unfold tailWord_7114068
  simp only [CollatzResearch.WordTrace]
  refine ⟨129735688195477048464763429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172980917593969397953017905 129735688195477048464763429)
  ·
    refine ⟨24325441536651946587143143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129735688195477048464763429 24325441536651946587143143)
    ·
      refine ⟨36488162304977919880714715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24325441536651946587143143 36488162304977919880714715)
      ·
        refine ⟨54732243457466879821072073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36488162304977919880714715 54732243457466879821072073)
        ·
          refine ⟨41049182593100159865804055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54732243457466879821072073 41049182593100159865804055)
          ·
            refine ⟨61573773889650239798706083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41049182593100159865804055 61573773889650239798706083)
            ·
              refine ⟨92360660834475359698059125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61573773889650239798706083 92360660834475359698059125)
              ·
                refine ⟨8658811953232064971693043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92360660834475359698059125 8658811953232064971693043)
                ·
                  refine ⟨12988217929848097457539565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8658811953232064971693043 12988217929848097457539565)
                  ·
                    refine ⟨4870581723693036546577337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12988217929848097457539565 4870581723693036546577337)
                    ·
                      refine ⟨3652936292769777409933003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4870581723693036546577337 3652936292769777409933003)
                      ·
                        rfl

theorem cell23_7114068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_7114068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114068 prefixEnd_7114068 := by exact prefixLift 7114068
  have htrace : WordTrace (prefixWord ++ tailWord_7114068) baseStart_7114068 baseEnd_7114068 := by
    simpa [prefixWord, tailWord_7114068, baseEnd_7114068] using wordTrace_append hprefix tailTrace_7114068
  have hstable : (prefixWord ++ tailWord_7114068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114068).length < 2 ^ (prefixWord ++ tailWord_7114068).sum := by decide
  have hdescent : baseEnd_7114068 < baseStart_7114068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114132 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_7114132 : Nat := 118140960795 + 7114132 * 2 ^ 59
def prefixEnd_7114132 : Nat := 4983230072969 + 3 ^ 40 * 7114132 * 2
def baseEnd_7114132 : Nat := 3652969155531665159532709

theorem tailTrace_7114132 : CollatzResearch.WordTrace tailWord_7114132 prefixEnd_7114132 3652969155531665159532709 := by
  unfold tailWord_7114132
  simp only [CollatzResearch.WordTrace]
  refine ⟨129736855331361117929928325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172982473775148157239904433 129736855331361117929928325)
  ·
    refine ⟨24325660374630209611861561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129736855331361117929928325 24325660374630209611861561)
    ·
      refine ⟨18244245280972657208896171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24325660374630209611861561 18244245280972657208896171)
      ·
        refine ⟨27366367921458985813344257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18244245280972657208896171 27366367921458985813344257)
        ·
          refine ⟨20524775941094239360008193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27366367921458985813344257 20524775941094239360008193)
          ·
            refine ⟨15393581955820679520006145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20524775941094239360008193 15393581955820679520006145)
            ·
              refine ⟨11545186466865509640004609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15393581955820679520006145 11545186466865509640004609)
              ·
                refine ⟨8658889850149132230003457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11545186466865509640004609 8658889850149132230003457)
                ·
                  refine ⟨6494167387611849172502593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8658889850149132230003457 6494167387611849172502593)
                  ·
                    refine ⟨4870625540708886879376945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6494167387611849172502593 4870625540708886879376945)
                    ·
                      refine ⟨3652969155531665159532709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4870625540708886879376945 3652969155531665159532709)
                      ·
                        rfl

theorem cell23_7114132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_7114132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114132 prefixEnd_7114132 := by exact prefixLift 7114132
  have htrace : WordTrace (prefixWord ++ tailWord_7114132) baseStart_7114132 baseEnd_7114132 := by
    simpa [prefixWord, tailWord_7114132, baseEnd_7114132] using wordTrace_append hprefix tailTrace_7114132
  have hstable : (prefixWord ++ tailWord_7114132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114132).length < 2 ^ (prefixWord ++ tailWord_7114132).sum := by decide
  have hdescent : baseEnd_7114132 < baseStart_7114132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114144 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 5]
def baseStart_7114144 : Nat := 118140960795 + 7114144 * 2 ^ 59
def prefixEnd_7114144 : Nat := 4983230072969 + 3 ^ 40 * 7114144 * 2
def baseEnd_7114144 : Nat := 3652975317299519112582653

theorem tailTrace_7114144 : CollatzResearch.WordTrace tailWord_7114144 prefixEnd_7114144 3652975317299519112582653 := by
  unfold tailWord_7114144
  simp only [CollatzResearch.WordTrace]
  refine ⟨129737074169339380954646743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172982765559119174606195657 129737074169339380954646743)
  ·
    refine ⟨194605611254009071431970115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129737074169339380954646743 194605611254009071431970115)
    ·
      refine ⟨291908416881013607147955173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194605611254009071431970115 291908416881013607147955173)
      ·
        refine ⟨54732828165190051340241595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291908416881013607147955173 54732828165190051340241595)
        ·
          refine ⟨82099242247785077010362393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54732828165190051340241595 82099242247785077010362393)
          ·
            refine ⟨61574431685838807757771795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82099242247785077010362393 61574431685838807757771795)
            ·
              refine ⟨92361647528758211636657693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61574431685838807757771795 92361647528758211636657693)
              ·
                refine ⟨34635617823284329363746635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92361647528758211636657693 34635617823284329363746635)
                ·
                  refine ⟨51953426734926494045619953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34635617823284329363746635 51953426734926494045619953)
                  ·
                    refine ⟨38965070051194870534214965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51953426734926494045619953 38965070051194870534214965)
                    ·
                      refine ⟨3652975317299519112582653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38965070051194870534214965 3652975317299519112582653)
                      ·
                        rfl

theorem cell23_7114144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_7114144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114144 prefixEnd_7114144 := by exact prefixLift 7114144
  have htrace : WordTrace (prefixWord ++ tailWord_7114144) baseStart_7114144 baseEnd_7114144 := by
    simpa [prefixWord, tailWord_7114144, baseEnd_7114144] using wordTrace_append hprefix tailTrace_7114144
  have hstable : (prefixWord ++ tailWord_7114144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114144).length < 2 ^ (prefixWord ++ tailWord_7114144).sum := by decide
  have hdescent : baseEnd_7114144 < baseStart_7114144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114184 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_7114184 : Nat := 118140960795 + 7114184 * 2 ^ 59
def prefixEnd_7114184 : Nat := 4983230072969 + 3 ^ 40 * 7114184 * 2
def baseEnd_7114184 : Nat := 3652995856525698956082469

theorem tailTrace_7114184 : CollatzResearch.WordTrace tailWord_7114184 prefixEnd_7114184 3652995856525698956082469 := by
  unfold tailWord_7114184
  simp only [CollatzResearch.WordTrace]
  refine ⟨129737803629266924370374803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172983738172355899160499737 129737803629266924370374803)
  ·
    refine ⟨194606705443900386555562205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129737803629266924370374803 194606705443900386555562205)
    ·
      refine ⟨72977514541462644958335827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194606705443900386555562205 72977514541462644958335827)
      ·
        refine ⟨109466271812193967437503741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72977514541462644958335827 109466271812193967437503741)
        ·
          refine ⟨41049851929572737789063903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109466271812193967437503741 41049851929572737789063903)
          ·
            refine ⟨61574777894359106683595855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41049851929572737789063903 61574777894359106683595855)
            ·
              refine ⟨92362166841538660025393783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61574777894359106683595855 92362166841538660025393783)
              ·
                refine ⟨138543250262307990038090675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92362166841538660025393783 138543250262307990038090675)
                ·
                  refine ⟨207814875393461985057136013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138543250262307990038090675 207814875393461985057136013)
                  ·
                    refine ⟨77930578272548244396426005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207814875393461985057136013 77930578272548244396426005)
                    ·
                      refine ⟨3652995856525698956082469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77930578272548244396426005 3652995856525698956082469)
                      ·
                        rfl

theorem cell23_7114184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_7114184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114184 prefixEnd_7114184 := by exact prefixLift 7114184
  have htrace : WordTrace (prefixWord ++ tailWord_7114184) baseStart_7114184 baseEnd_7114184 := by
    simpa [prefixWord, tailWord_7114184, baseEnd_7114184] using wordTrace_append hprefix tailTrace_7114184
  have hstable : (prefixWord ++ tailWord_7114184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114184).length < 2 ^ (prefixWord ++ tailWord_7114184).sum := by decide
  have hdescent : baseEnd_7114184 < baseStart_7114184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114188 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 2, 4, 2]
def baseStart_7114188 : Nat := 118140960795 + 7114188 * 2 ^ 59
def prefixEnd_7114188 : Nat := 4983230072969 + 3 ^ 40 * 7114188 * 2
def baseEnd_7114188 : Nat := 3652997910448316940432451

theorem tailTrace_7114188 : CollatzResearch.WordTrace tailWord_7114188 prefixEnd_7114188 3652997910448316940432451 := by
  unfold tailWord_7114188
  simp only [CollatzResearch.WordTrace]
  refine ⟨129737876575259678711947609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172983835433679571615930145 129737876575259678711947609)
  ·
    refine ⟨97303407431444759033960707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129737876575259678711947609 97303407431444759033960707)
    ·
      refine ⟨145955111147167138550941061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97303407431444759033960707 145955111147167138550941061)
      ·
        refine ⟨27366583340093838478301449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145955111147167138550941061 27366583340093838478301449)
        ·
          refine ⟨20524937505070378858726087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27366583340093838478301449 20524937505070378858726087)
          ·
            refine ⟨30787406257605568288089131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20524937505070378858726087 30787406257605568288089131)
            ·
              refine ⟨46181109386408352432133697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30787406257605568288089131 46181109386408352432133697)
              ·
                refine ⟨34635832039806264324100273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46181109386408352432133697 34635832039806264324100273)
                ·
                  refine ⟨25976874029854698243075205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34635832039806264324100273 25976874029854698243075205)
                  ·
                    refine ⟨4870663880597755920576601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25976874029854698243075205 4870663880597755920576601)
                    ·
                      refine ⟨3652997910448316940432451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4870663880597755920576601 3652997910448316940432451)
                      ·
                        rfl

theorem cell23_7114188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_7114188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114188 prefixEnd_7114188 := by exact prefixLift 7114188
  have htrace : WordTrace (prefixWord ++ tailWord_7114188) baseStart_7114188 baseEnd_7114188 := by
    simpa [prefixWord, tailWord_7114188, baseEnd_7114188] using wordTrace_append hprefix tailTrace_7114188
  have hstable : (prefixWord ++ tailWord_7114188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114188).length < 2 ^ (prefixWord ++ tailWord_7114188).sum := by decide
  have hdescent : baseEnd_7114188 < baseStart_7114188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114191 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 3]
def baseStart_7114191 : Nat := 118140960795 + 7114191 * 2 ^ 59
def prefixEnd_7114191 : Nat := 4983230072969 + 3 ^ 40 * 7114191 * 2
def baseEnd_7114191 : Nat := 3652999450890280428694937

theorem tailTrace_7114191 : CollatzResearch.WordTrace tailWord_7114191 prefixEnd_7114191 3652999450890280428694937 := by
  unfold tailWord_7114191
  simp only [CollatzResearch.WordTrace]
  refine ⟨259475862569508488936254427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172983908379672325957502951 259475862569508488936254427)
  ·
    refine ⟨389213793854262733404381641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259475862569508488936254427 389213793854262733404381641)
    ·
      refine ⟨291910345390697050053286231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389213793854262733404381641 291910345390697050053286231)
      ·
        refine ⟨437865518086045575079929347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291910345390697050053286231 437865518086045575079929347)
        ·
          refine ⟨656798277129068362619894021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437865518086045575079929347 656798277129068362619894021)
          ·
            refine ⟨123149676961700317991230129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 656798277129068362619894021 123149676961700317991230129)
            ·
              refine ⟨92362257721275238493422597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123149676961700317991230129 92362257721275238493422597)
              ·
                refine ⟨17317923322739107217516737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92362257721275238493422597 17317923322739107217516737)
                ·
                  refine ⟨12988442492054330413137553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17317923322739107217516737 12988442492054330413137553)
                  ·
                    refine ⟨9741331869040747809853165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12988442492054330413137553 9741331869040747809853165)
                    ·
                      refine ⟨3652999450890280428694937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9741331869040747809853165 3652999450890280428694937)
                      ·
                        rfl

theorem cell23_7114191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 3].length) (baseStart_7114191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114191 prefixEnd_7114191 := by exact prefixLift 7114191
  have htrace : WordTrace (prefixWord ++ tailWord_7114191) baseStart_7114191 baseEnd_7114191 := by
    simpa [prefixWord, tailWord_7114191, baseEnd_7114191] using wordTrace_append hprefix tailTrace_7114191
  have hstable : (prefixWord ++ tailWord_7114191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114191).length < 2 ^ (prefixWord ++ tailWord_7114191).sum := by decide
  have hdescent : baseEnd_7114191 < baseStart_7114191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114248 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 4, 3, 2]
def baseStart_7114248 : Nat := 118140960795 + 7114248 * 2 ^ 59
def prefixEnd_7114248 : Nat := 4983230072969 + 3 ^ 40 * 7114248 * 2
def baseEnd_7114248 : Nat := 3653028719287586705682175

theorem tailTrace_7114248 : CollatzResearch.WordTrace tailWord_7114248 prefixEnd_7114248 3653028719287586705682175 := by
  unfold tailWord_7114248
  simp only [CollatzResearch.WordTrace]
  refine ⟨129738970765150993835539699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172985294353534658447386265 129738970765150993835539699)
  ·
    refine ⟨194608456147726490753309549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129738970765150993835539699 194608456147726490753309549)
    ·
      refine ⟨72978171055397434032491081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194608456147726490753309549 72978171055397434032491081)
      ·
        refine ⟨54733628291548075524368311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72978171055397434032491081 54733628291548075524368311)
        ·
          refine ⟨82100442437322113286552467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54733628291548075524368311 82100442437322113286552467)
          ·
            refine ⟨123150663655983169929828701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82100442437322113286552467 123150663655983169929828701)
            ·
              refine ⟨46181498870993688723685763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123150663655983169929828701 46181498870993688723685763)
              ·
                refine ⟨69272248306490533085528645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46181498870993688723685763 69272248306490533085528645)
                ·
                  refine ⟨12988546557466974953536621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69272248306490533085528645 12988546557466974953536621)
                  ·
                    refine ⟨4870704959050115607576233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12988546557466974953536621 4870704959050115607576233)
                    ·
                      refine ⟨3653028719287586705682175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4870704959050115607576233 3653028719287586705682175)
                      ·
                        rfl

theorem cell23_7114248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_7114248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114248 prefixEnd_7114248 := by exact prefixLift 7114248
  have htrace : WordTrace (prefixWord ++ tailWord_7114248) baseStart_7114248 baseEnd_7114248 := by
    simpa [prefixWord, tailWord_7114248, baseEnd_7114248] using wordTrace_append hprefix tailTrace_7114248
  have hstable : (prefixWord ++ tailWord_7114248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114248).length < 2 ^ (prefixWord ++ tailWord_7114248).sum := by decide
  have hdescent : baseEnd_7114248 < baseStart_7114248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114275 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 1, 5]
def baseStart_7114275 : Nat := 118140960795 + 7114275 * 2 ^ 59
def prefixEnd_7114275 : Nat := 4983230072969 + 3 ^ 40 * 7114275 * 2
def baseEnd_7114275 : Nat := 1217680861088419366681517

theorem tailTrace_7114275 : CollatzResearch.WordTrace tailWord_7114275 prefixEnd_7114275 1217680861088419366681517 := by
  unfold tailWord_7114275
  simp only [CollatzResearch.WordTrace]
  refine ⟨259478926301204171282312279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172985950867469447521541519 259478926301204171282312279)
  ·
    refine ⟨389218389451806256923468419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259478926301204171282312279 389218389451806256923468419)
    ·
      refine ⟨583827584177709385385202629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389218389451806256923468419 583827584177709385385202629)
      ·
        refine ⟨109467672033320509759725493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 583827584177709385385202629 109467672033320509759725493)
        ·
          refine ⟨10262594253123797789974265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109467672033320509759725493 10262594253123797789974265)
          ·
            refine ⟨7696945689842848342480699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10262594253123797789974265 7696945689842848342480699)
            ·
              refine ⟨11545418534764272513721049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7696945689842848342480699 11545418534764272513721049)
              ·
                refine ⟨8659063901073204385290787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11545418534764272513721049 8659063901073204385290787)
                ·
                  refine ⟨12988595851609806577936181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8659063901073204385290787 12988595851609806577936181)
                  ·
                    refine ⟨1217680861088419366681517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12988595851609806577936181 1217680861088419366681517)
                    ·
                      rfl

theorem cell23_7114275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 5].length) (baseStart_7114275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114275 prefixEnd_7114275 := by exact prefixLift 7114275
  have htrace : WordTrace (prefixWord ++ tailWord_7114275) baseStart_7114275 baseEnd_7114275 := by
    simpa [prefixWord, tailWord_7114275, baseEnd_7114275] using wordTrace_append hprefix tailTrace_7114275
  have hstable : (prefixWord ++ tailWord_7114275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114275).length < 2 ^ (prefixWord ++ tailWord_7114275).sum := by decide
  have hdescent : baseEnd_7114275 < baseStart_7114275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114291 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 4]
def baseStart_7114291 : Nat := 118140960795 + 7114291 * 2 ^ 59
def prefixEnd_7114291 : Nat := 4983230072969 + 3 ^ 40 * 7114291 * 2
def baseEnd_7114291 : Nat := 3653050798955730037444477

theorem tailTrace_7114291 : CollatzResearch.WordTrace tailWord_7114291 prefixEnd_7114291 3653050798955730037444477 := by
  unfold tailWord_7114291
  simp only [CollatzResearch.WordTrace]
  refine ⟨259479509869146206014894727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172986339912764137343263151 259479509869146206014894727)
  ·
    refine ⟨389219264803719309022342091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259479509869146206014894727 389219264803719309022342091)
    ·
      refine ⟨583828897205578963533513137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389219264803719309022342091 583828897205578963533513137)
      ·
        refine ⟨437871672904184222650134853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583828897205578963533513137 437871672904184222650134853)
        ·
          refine ⟨82100938669534541746900285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 437871672904184222650134853 82100938669534541746900285)
          ·
            refine ⟨30787852001075453155087607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82100938669534541746900285 30787852001075453155087607)
            ·
              refine ⟨46181778001613179732631411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30787852001075453155087607 46181778001613179732631411)
              ·
                refine ⟨69272667002419769598947117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46181778001613179732631411 69272667002419769598947117)
                ·
                  refine ⟨25977250125907413599605169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69272667002419769598947117 25977250125907413599605169)
                  ·
                    refine ⟨19482937594430560199703877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25977250125907413599605169 19482937594430560199703877)
                    ·
                      refine ⟨3653050798955730037444477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19482937594430560199703877 3653050798955730037444477)
                      ·
                        rfl

theorem cell23_7114291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_7114291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114291 prefixEnd_7114291 := by exact prefixLift 7114291
  have htrace : WordTrace (prefixWord ++ tailWord_7114291) baseStart_7114291 baseEnd_7114291 := by
    simpa [prefixWord, tailWord_7114291, baseEnd_7114291] using wordTrace_append hprefix tailTrace_7114291
  have hstable : (prefixWord ++ tailWord_7114291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114291).length < 2 ^ (prefixWord ++ tailWord_7114291).sum := by decide
  have hdescent : baseEnd_7114291 < baseStart_7114291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114295 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 1, 1, 4]
def baseStart_7114295 : Nat := 118140960795 + 7114295 * 2 ^ 59
def prefixEnd_7114295 : Nat := 4983230072969 + 3 ^ 40 * 7114295 * 2
def baseEnd_7114295 : Nat := 3653052852878348021794459

theorem tailTrace_7114295 : CollatzResearch.WordTrace tailWord_7114295 prefixEnd_7114295 3653052852878348021794459 := by
  unfold tailWord_7114295
  simp only [CollatzResearch.WordTrace]
  refine ⟨259479655761131714698040339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172986437174087809798693559 259479655761131714698040339)
  ·
    refine ⟨389219483641697572047060509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259479655761131714698040339 389219483641697572047060509)
    ·
      refine ⟨145957306365636589517647691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389219483641697572047060509 145957306365636589517647691)
      ·
        refine ⟨218935959548454884276471537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145957306365636589517647691 218935959548454884276471537)
        ·
          refine ⟨164201969661341163207353653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218935959548454884276471537 164201969661341163207353653)
          ·
            refine ⟨15393934655750734050689405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164201969661341163207353653 15393934655750734050689405)
            ·
              refine ⟨5772725495906525269008527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15393934655750734050689405 5772725495906525269008527)
              ·
                refine ⟨8659088243859787903512791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5772725495906525269008527 8659088243859787903512791)
                ·
                  refine ⟨12988632365789681855269187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8659088243859787903512791 12988632365789681855269187)
                  ·
                    refine ⟨19482948548684522782903781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12988632365789681855269187 19482948548684522782903781)
                    ·
                      refine ⟨3653052852878348021794459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19482948548684522782903781 3653052852878348021794459)
                      ·
                        rfl

theorem cell23_7114295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 1, 4].length) (baseStart_7114295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114295 prefixEnd_7114295 := by exact prefixLift 7114295
  have htrace : WordTrace (prefixWord ++ tailWord_7114295) baseStart_7114295 baseEnd_7114295 := by
    simpa [prefixWord, tailWord_7114295, baseEnd_7114295] using wordTrace_append hprefix tailTrace_7114295
  have hstable : (prefixWord ++ tailWord_7114295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114295).length < 2 ^ (prefixWord ++ tailWord_7114295).sum := by decide
  have hdescent : baseEnd_7114295 < baseStart_7114295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114301 : List Nat := [1, 4, 1, 3, 3, 11]
def baseStart_7114301 : Nat := 118140960795 + 7114301 * 2 ^ 59
def prefixEnd_7114301 : Nat := 4983230072969 + 3 ^ 40 * 7114301 * 2
def baseEnd_7114301 : Nat := 15033151990791255137117

theorem tailTrace_7114301 : CollatzResearch.WordTrace tailWord_7114301 prefixEnd_7114301 15033151990791255137117 := by
  unfold tailWord_7114301
  simp only [CollatzResearch.WordTrace]
  refine ⟨259479874599109977722758757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172986583066073318481839171 259479874599109977722758757)
  ·
    refine ⟨48652476487333120823017267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259479874599109977722758757 48652476487333120823017267)
    ·
      refine ⟨72978714730999681234525901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48652476487333120823017267 72978714730999681234525901)
      ·
        refine ⟨27367018024124880462947213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72978714730999681234525901 27367018024124880462947213)
        ·
          refine ⟨10262631759046830173605205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27367018024124880462947213 10262631759046830173605205)
          ·
            refine ⟨15033151990791255137117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10262631759046830173605205 15033151990791255137117)
            ·
              rfl

theorem cell23_7114301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 11].length) (baseStart_7114301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114301 prefixEnd_7114301 := by exact prefixLift 7114301
  have htrace : WordTrace (prefixWord ++ tailWord_7114301) baseStart_7114301 baseEnd_7114301 := by
    simpa [prefixWord, tailWord_7114301, baseEnd_7114301] using wordTrace_append hprefix tailTrace_7114301
  have hstable : (prefixWord ++ tailWord_7114301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114301).length < 2 ^ (prefixWord ++ tailWord_7114301).sum := by decide
  have hdescent : baseEnd_7114301 < baseStart_7114301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114305 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7114305 : Nat := 118140960795 + 7114305 * 2 ^ 59
def prefixEnd_7114305 : Nat := 4983230072969 + 3 ^ 40 * 7114305 * 2
def baseEnd_7114305 : Nat := 1217685995894964327556471

theorem tailTrace_7114305 : CollatzResearch.WordTrace tailWord_7114305 prefixEnd_7114305 1217685995894964327556471 := by
  unfold tailWord_7114305
  simp only [CollatzResearch.WordTrace]
  refine ⟨259480020491095486405904369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172986680327396990937269579 259480020491095486405904369)
  ·
    refine ⟨194610015368321614804428277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259480020491095486405904369 194610015368321614804428277)
    ·
      refine ⟨18244688940780151387915151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194610015368321614804428277 18244688940780151387915151)
      ·
        refine ⟨27367033411170227081872727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18244688940780151387915151 27367033411170227081872727)
        ·
          refine ⟨41050550116755340622809091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27367033411170227081872727 41050550116755340622809091)
          ·
            refine ⟨61575825175133010934213637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41050550116755340622809091 61575825175133010934213637)
            ·
              refine ⟨11545467220337439550165057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61575825175133010934213637 11545467220337439550165057)
              ·
                refine ⟨8659100415253079662623793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11545467220337439550165057 8659100415253079662623793)
                ·
                  refine ⟨6494325311439809746967845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8659100415253079662623793 6494325311439809746967845)
                  ·
                    refine ⟨1217685995894964327556471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6494325311439809746967845 1217685995894964327556471)
                    ·
                      rfl

theorem cell23_7114305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7114305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114305 prefixEnd_7114305 := by exact prefixLift 7114305
  have htrace : WordTrace (prefixWord ++ tailWord_7114305) baseStart_7114305 baseEnd_7114305 := by
    simpa [prefixWord, tailWord_7114305, baseEnd_7114305] using wordTrace_append hprefix tailTrace_7114305
  have hstable : (prefixWord ++ tailWord_7114305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114305).length < 2 ^ (prefixWord ++ tailWord_7114305).sum := by decide
  have hdescent : baseEnd_7114305 < baseStart_7114305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114328 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 6, 1, 3]
def baseStart_7114328 : Nat := 118140960795 + 7114328 * 2 ^ 59
def prefixEnd_7114328 : Nat := 4983230072969 + 3 ^ 40 * 7114328 * 2
def baseEnd_7114328 : Nat := 3653069797739946392681807

theorem tailTrace_7114328 : CollatzResearch.WordTrace tailWord_7114328 prefixEnd_7114328 3653069797739946392681807 := by
  unfold tailWord_7114328
  simp only [CollatzResearch.WordTrace]
  refine ⟨129740429685006080666995819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172987239580008107555994425 129740429685006080666995819)
  ·
    refine ⟨194610644527509121000493729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129740429685006080666995819 194610644527509121000493729)
    ·
      refine ⟨145957983395631840750370297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194610644527509121000493729 145957983395631840750370297)
      ·
        refine ⟨109468487546723880562777723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145957983395631840750370297 109468487546723880562777723)
        ·
          refine ⟨164202731320085820844166585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109468487546723880562777723 164202731320085820844166585)
          ·
            refine ⟨123152048490064365633124939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164202731320085820844166585 123152048490064365633124939)
            ·
              refine ⟨184728072735096548449687409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123152048490064365633124939 184728072735096548449687409)
              ·
                refine ⟨138546054551322411337265557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184728072735096548449687409 138546054551322411337265557)
                ·
                  refine ⟨6494346307093238031434323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138546054551322411337265557 6494346307093238031434323)
                  ·
                    refine ⟨9741519460639857047151485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6494346307093238031434323 9741519460639857047151485)
                    ·
                      refine ⟨3653069797739946392681807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9741519460639857047151485 3653069797739946392681807)
                      ·
                        rfl

theorem cell23_7114328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_7114328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114328 prefixEnd_7114328 := by exact prefixLift 7114328
  have htrace : WordTrace (prefixWord ++ tailWord_7114328) baseStart_7114328 baseEnd_7114328 := by
    simpa [prefixWord, tailWord_7114328, baseEnd_7114328] using wordTrace_append hprefix tailTrace_7114328
  have hstable : (prefixWord ++ tailWord_7114328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114328).length < 2 ^ (prefixWord ++ tailWord_7114328).sum := by decide
  have hdescent : baseEnd_7114328 < baseStart_7114328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114349 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_7114349 : Nat := 118140960795 + 7114349 * 2 ^ 59
def prefixEnd_7114349 : Nat := 4983230072969 + 3 ^ 40 * 7114349 * 2
def baseEnd_7114349 : Nat := 3653080580833690810519211

theorem tailTrace_7114349 : CollatzResearch.WordTrace tailWord_7114349 prefixEnd_7114349 3653080580833690810519211 := by
  unfold tailWord_7114349
  simp only [CollatzResearch.WordTrace]
  refine ⟨259481625302936081920506101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172987750201957387947004067 259481625302936081920506101)
  ·
    refine ⟨24326402372150257680047447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259481625302936081920506101 24326402372150257680047447)
    ·
      refine ⟨36489603558225386520071171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24326402372150257680047447 36489603558225386520071171)
      ·
        refine ⟨54734405337338079780106757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36489603558225386520071171 54734405337338079780106757)
        ·
          refine ⟨10262701000750889958770017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54734405337338079780106757 10262701000750889958770017)
          ·
            refine ⟨7697025750563167469077513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10262701000750889958770017 7697025750563167469077513)
            ·
              refine ⟨5772769312922375601808135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7697025750563167469077513 5772769312922375601808135)
              ·
                refine ⟨8659153969383563402712203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5772769312922375601808135 8659153969383563402712203)
                ·
                  refine ⟨12988730954075345104068305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8659153969383563402712203 12988730954075345104068305)
                  ·
                    refine ⟨9741548215556508828051229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12988730954075345104068305 9741548215556508828051229)
                    ·
                      refine ⟨3653080580833690810519211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9741548215556508828051229 3653080580833690810519211)
                      ·
                        rfl

theorem cell23_7114349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_7114349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114349 prefixEnd_7114349 := by exact prefixLift 7114349
  have htrace : WordTrace (prefixWord ++ tailWord_7114349) baseStart_7114349 baseEnd_7114349 := by
    simpa [prefixWord, tailWord_7114349, baseEnd_7114349] using wordTrace_append hprefix tailTrace_7114349
  have hstable : (prefixWord ++ tailWord_7114349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114349).length < 2 ^ (prefixWord ++ tailWord_7114349).sum := by decide
  have hdescent : baseEnd_7114349 < baseStart_7114349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114361 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 4, 6]
def baseStart_7114361 : Nat := 118140960795 + 7114361 * 2 ^ 59
def prefixEnd_7114361 : Nat := 4983230072969 + 3 ^ 40 * 7114361 * 2
def baseEnd_7114361 : Nat := 1217695580867181587856385

theorem tailTrace_7114361 : CollatzResearch.WordTrace tailWord_7114361 prefixEnd_7114361 1217695580867181587856385 := by
  unfold tailWord_7114361
  simp only [CollatzResearch.WordTrace]
  refine ⟨259482062978892607969942937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172988041985928405313295291 259482062978892607969942937)
  ·
    refine ⟨194611547234169455977457203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259482062978892607969942937 194611547234169455977457203)
    ·
      refine ⟨291917320851254183966185805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194611547234169455977457203 291917320851254183966185805)
      ·
        refine ⟨109468995319220318987319677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291917320851254183966185805 109468995319220318987319677)
        ·
          refine ⟨41050873244707619620244879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109468995319220318987319677 41050873244707619620244879)
          ·
            refine ⟨61576309867061429430367319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41050873244707619620244879 61576309867061429430367319)
            ·
              refine ⟨92364464800592144145550979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61576309867061429430367319 92364464800592144145550979)
              ·
                refine ⟨138546697200888216218326469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92364464800592144145550979 138546697200888216218326469)
                ·
                  refine ⟨25977505725166540540936213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138546697200888216218326469 25977505725166540540936213)
                  ·
                    refine ⟨1217695580867181587856385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25977505725166540540936213 1217695580867181587856385)
                    ·
                      rfl

theorem cell23_7114361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_7114361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114361 prefixEnd_7114361 := by exact prefixLift 7114361
  have htrace : WordTrace (prefixWord ++ tailWord_7114361) baseStart_7114361 baseEnd_7114361 := by
    simpa [prefixWord, tailWord_7114361, baseEnd_7114361] using wordTrace_append hprefix tailTrace_7114361
  have hstable : (prefixWord ++ tailWord_7114361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114361).length < 2 ^ (prefixWord ++ tailWord_7114361).sum := by decide
  have hdescent : baseEnd_7114361 < baseStart_7114361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114371 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 5]
def baseStart_7114371 : Nat := 118140960795 + 7114371 * 2 ^ 59
def prefixEnd_7114371 : Nat := 4983230072969 + 3 ^ 40 * 7114371 * 2
def baseEnd_7114371 : Nat := 3653091877408089724444109

theorem tailTrace_7114371 : CollatzResearch.WordTrace tailWord_7114371 prefixEnd_7114371 3653091877408089724444109 := by
  unfold tailWord_7114371
  simp only [CollatzResearch.WordTrace]
  refine ⟨259482427708856379677806967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172988285139237586451871311 259482427708856379677806967)
  ·
    refine ⟨389223641563284569516710451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259482427708856379677806967 389223641563284569516710451)
    ·
      refine ⟨583835462344926854275065677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389223641563284569516710451 583835462344926854275065677)
      ·
        refine ⟨218938298379347570353149629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 583835462344926854275065677 218938298379347570353149629)
        ·
          refine ⟨82101861892255338882431111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218938298379347570353149629 82101861892255338882431111)
          ·
            refine ⟨123152792838383008323646667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82101861892255338882431111 123152792838383008323646667)
            ·
              refine ⟨184729189257574512485470001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123152792838383008323646667 184729189257574512485470001)
              ·
                refine ⟨138546891943180884364102501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184729189257574512485470001 138546891943180884364102501)
                ·
                  refine ⟨25977542239346415818269219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138546891943180884364102501 25977542239346415818269219)
                  ·
                    refine ⟨38966313359019623727403829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25977542239346415818269219 38966313359019623727403829)
                    ·
                      refine ⟨3653091877408089724444109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38966313359019623727403829 3653091877408089724444109)
                      ·
                        rfl

theorem cell23_7114371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_7114371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114371 prefixEnd_7114371 := by exact prefixLift 7114371
  have htrace : WordTrace (prefixWord ++ tailWord_7114371) baseStart_7114371 baseEnd_7114371 := by
    simpa [prefixWord, tailWord_7114371, baseEnd_7114371] using wordTrace_append hprefix tailTrace_7114371
  have hstable : (prefixWord ++ tailWord_7114371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114371).length < 2 ^ (prefixWord ++ tailWord_7114371).sum := by decide
  have hdescent : baseEnd_7114371 < baseStart_7114371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114378 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_7114378 : Nat := 118140960795 + 7114378 * 2 ^ 59
def prefixEnd_7114378 : Nat := 4983230072969 + 3 ^ 40 * 7114378 * 2
def baseEnd_7114378 : Nat := 1217698490590890399018859

theorem tailTrace_7114378 : CollatzResearch.WordTrace tailWord_7114378 prefixEnd_7114378 1217698490590890399018859 := by
  unfold tailWord_7114378
  simp only [CollatzResearch.WordTrace]
  refine ⟨64870670754957754968327947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172988455346554013248874525 64870670754957754968327947)
  ·
    refine ⟨97306006132436632452491921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64870670754957754968327947 97306006132436632452491921)
    ·
      refine ⟨72979504599327474339368941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97306006132436632452491921 72979504599327474339368941)
      ·
        refine ⟨27367314224747802877263353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72979504599327474339368941 27367314224747802877263353)
        ·
          refine ⟨20525485668560852157947515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27367314224747802877263353 20525485668560852157947515)
          ·
            refine ⟨30788228502841278236921273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20525485668560852157947515 30788228502841278236921273)
            ·
              refine ⟨23091171377130958677690955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30788228502841278236921273 23091171377130958677690955)
              ·
                refine ⟨34636757065696438016536433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23091171377130958677690955 34636757065696438016536433)
                ·
                  refine ⟨25977567799272328512402325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34636757065696438016536433 25977567799272328512402325)
                  ·
                    refine ⟨1217698490590890399018859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25977567799272328512402325 1217698490590890399018859)
                    ·
                      rfl

theorem cell23_7114378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_7114378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114378 prefixEnd_7114378 := by exact prefixLift 7114378
  have htrace : WordTrace (prefixWord ++ tailWord_7114378) baseStart_7114378 baseEnd_7114378 := by
    simpa [prefixWord, tailWord_7114378, baseEnd_7114378] using wordTrace_append hprefix tailTrace_7114378
  have hstable : (prefixWord ++ tailWord_7114378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114378).length < 2 ^ (prefixWord ++ tailWord_7114378).sum := by decide
  have hdescent : baseEnd_7114378 < baseStart_7114378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114418 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_7114418 : Nat := 118140960795 + 7114418 * 2 ^ 59
def prefixEnd_7114418 : Nat := 4983230072969 + 3 ^ 40 * 7114418 * 2
def baseEnd_7114418 : Nat := 3653116010998851040556393

theorem tailTrace_7114418 : CollatzResearch.WordTrace tailWord_7114418 prefixEnd_7114418 3653116010998851040556393 := by
  unfold tailWord_7114418
  simp only [CollatzResearch.WordTrace]
  refine ⟨64871035484921526676191977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172989427959790737803178605 64871035484921526676191977)
  ·
    refine ⟨48653276613691145007143983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64871035484921526676191977 48653276613691145007143983)
    ·
      refine ⟨72979914920536717510715975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48653276613691145007143983 72979914920536717510715975)
      ·
        refine ⟨109469872380805076266073963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72979914920536717510715975 109469872380805076266073963)
        ·
          refine ⟨164204808571207614399110945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109469872380805076266073963 164204808571207614399110945)
          ·
            refine ⟨123153606428405710799333209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164204808571207614399110945 123153606428405710799333209)
            ·
              refine ⟨92365204821304283099499907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123153606428405710799333209 92365204821304283099499907)
              ·
                refine ⟨138547807231956424649249861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92365204821304283099499907 138547807231956424649249861)
                ·
                  refine ⟨25977713855991829621734349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138547807231956424649249861 25977713855991829621734349)
                  ·
                    refine ⟨9741642695996936108150381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25977713855991829621734349 9741642695996936108150381)
                    ·
                      refine ⟨3653116010998851040556393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9741642695996936108150381 3653116010998851040556393)
                      ·
                        rfl

theorem cell23_7114418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_7114418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114418 prefixEnd_7114418 := by exact prefixLift 7114418
  have htrace : WordTrace (prefixWord ++ tailWord_7114418) baseStart_7114418 baseEnd_7114418 := by
    simpa [prefixWord, tailWord_7114418, baseEnd_7114418] using wordTrace_append hprefix tailTrace_7114418
  have hstable : (prefixWord ++ tailWord_7114418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114418).length < 2 ^ (prefixWord ++ tailWord_7114418).sum := by decide
  have hdescent : baseEnd_7114418 < baseStart_7114418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114478 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_7114478 : Nat := 118140960795 + 7114478 * 2 ^ 59
def prefixEnd_7114478 : Nat := 4983230072969 + 3 ^ 40 * 7114478 * 2
def baseEnd_7114478 : Nat := 3653146819838120805806117

theorem tailTrace_7114478 : CollatzResearch.WordTrace tailWord_7114478 prefixEnd_7114478 3653146819838120805806117 := by
  unfold tailWord_7114478
  simp only [CollatzResearch.WordTrace]
  refine ⟨32435791289933592118994011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172990886879645824634634725 32435791289933592118994011)
  ·
    refine ⟨48653686934900388178491017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32435791289933592118994011 48653686934900388178491017)
    ·
      refine ⟨36490265201175291133868263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48653686934900388178491017 36490265201175291133868263)
      ·
        refine ⟨54735397801762936700802395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36490265201175291133868263 54735397801762936700802395)
        ·
          refine ⟨82103096702644405051203593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54735397801762936700802395 82103096702644405051203593)
          ·
            refine ⟨61577322526983303788402695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82103096702644405051203593 61577322526983303788402695)
            ·
              refine ⟨92365983790474955682604043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61577322526983303788402695 92365983790474955682604043)
              ·
                refine ⟨138548975685712433523906065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92365983790474955682604043 138548975685712433523906065)
                ·
                  refine ⟨103911731764284325142929549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138548975685712433523906065 103911731764284325142929549)
                  ·
                    refine ⟨38966899411606621928598581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103911731764284325142929549 38966899411606621928598581)
                    ·
                      refine ⟨3653146819838120805806117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38966899411606621928598581 3653146819838120805806117)
                      ·
                        rfl

theorem cell23_7114478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_7114478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114478 prefixEnd_7114478 := by exact prefixLift 7114478
  have htrace : WordTrace (prefixWord ++ tailWord_7114478) baseStart_7114478 baseEnd_7114478 := by
    simpa [prefixWord, tailWord_7114478, baseEnd_7114478] using wordTrace_append hprefix tailTrace_7114478
  have hstable : (prefixWord ++ tailWord_7114478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114478).length < 2 ^ (prefixWord ++ tailWord_7114478).sum := by decide
  have hdescent : baseEnd_7114478 < baseStart_7114478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114519 : List Nat := [1, 1, 3, 4, 2, 2, 2, 3, 1, 4]
def baseStart_7114519 : Nat := 118140960795 + 7114519 * 2 ^ 59
def prefixEnd_7114519 : Nat := 4983230072969 + 3 ^ 40 * 7114519 * 2
def baseEnd_7114519 : Nat := 1217722624181651715131143

theorem tailTrace_7114519 : CollatzResearch.WordTrace tailWord_7114519 prefixEnd_7114519 1217722624181651715131143 := by
  unfold tailWord_7114519
  simp only [CollatzResearch.WordTrace]
  refine ⟨259487825712320200954194611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172991883808213467302796407 259487825712320200954194611)
  ·
    refine ⟨389231738568480301431291917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259487825712320200954194611 389231738568480301431291917)
    ·
      refine ⟨145961901963180113036734469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389231738568480301431291917 145961901963180113036734469)
      ·
        refine ⟨27367856618096271194387713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145961901963180113036734469 27367856618096271194387713)
        ·
          refine ⟨20525892463572203395790785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27367856618096271194387713 20525892463572203395790785)
          ·
            refine ⟨15394419347679152546843089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20525892463572203395790785 15394419347679152546843089)
            ·
              refine ⟨11545814510759364410132317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15394419347679152546843089 11545814510759364410132317)
              ·
                refine ⟨4329680441534761653799619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11545814510759364410132317 4329680441534761653799619)
                ·
                  refine ⟨6494520662302142480699429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4329680441534761653799619 6494520662302142480699429)
                  ·
                    refine ⟨1217722624181651715131143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6494520662302142480699429 1217722624181651715131143)
                    ·
                      rfl

theorem cell23_7114519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_7114519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114519 prefixEnd_7114519 := by exact prefixLift 7114519
  have htrace : WordTrace (prefixWord ++ tailWord_7114519) baseStart_7114519 baseEnd_7114519 := by
    simpa [prefixWord, tailWord_7114519, baseEnd_7114519] using wordTrace_append hprefix tailTrace_7114519
  have hstable : (prefixWord ++ tailWord_7114519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114519).length < 2 ^ (prefixWord ++ tailWord_7114519).sum := by decide
  have hdescent : baseEnd_7114519 < baseStart_7114519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114532 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 6]
def baseStart_7114532 : Nat := 118140960795 + 7114532 * 2 ^ 59
def prefixEnd_7114532 : Nat := 4983230072969 + 3 ^ 40 * 7114532 * 2
def baseEnd_7114532 : Nat := 405908283088162621614541

theorem tailTrace_7114532 : CollatzResearch.WordTrace tailWord_7114532 prefixEnd_7114532 405908283088162621614541 := by
  unfold tailWord_7114532
  simp only [CollatzResearch.WordTrace]
  refine ⟨129744149930636552087208925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172992199907515402782945233 129744149930636552087208925)
  ·
    refine ⟨48654056223988707032703347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129744149930636552087208925 48654056223988707032703347)
    ·
      refine ⟨72981084335983060549055021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48654056223988707032703347 72981084335983060549055021)
      ·
        refine ⟨27367906625993647705895633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72981084335983060549055021 27367906625993647705895633)
        ·
          refine ⟨20525929969495235779421725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27367906625993647705895633 20525929969495235779421725)
          ·
            refine ⟨7697223738560713417283147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20525929969495235779421725 7697223738560713417283147)
            ·
              refine ⟨11545835607841070125924721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7697223738560713417283147 11545835607841070125924721)
              ·
                refine ⟨8659376705880802594443541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11545835607841070125924721 8659376705880802594443541)
                ·
                  refine ⟨405908283088162621614541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8659376705880802594443541 405908283088162621614541)
                  ·
                    rfl

theorem cell23_7114532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_7114532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114532 prefixEnd_7114532 := by exact prefixLift 7114532
  have htrace : WordTrace (prefixWord ++ tailWord_7114532) baseStart_7114532 baseEnd_7114532 := by
    simpa [prefixWord, tailWord_7114532, baseEnd_7114532] using wordTrace_append hprefix tailTrace_7114532
  have hstable : (prefixWord ++ tailWord_7114532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114532).length < 2 ^ (prefixWord ++ tailWord_7114532).sum := by decide
  have hdescent : baseEnd_7114532 < baseStart_7114532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114565 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 2, 6, 2]
def baseStart_7114565 : Nat := 118140960795 + 7114565 * 2 ^ 59
def prefixEnd_7114565 : Nat := 4983230072969 + 3 ^ 40 * 7114565 * 2
def baseEnd_7114565 : Nat := 3653191492655061965418217

theorem tailTrace_7114565 : CollatzResearch.WordTrace tailWord_7114565 prefixEnd_7114565 3653191492655061965418217 := by
  unfold tailWord_7114565
  simp only [CollatzResearch.WordTrace]
  refine ⟨259489503470153550810369149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172993002313435700540246099 259489503470153550810369149)
  ·
    refine ⟨97308563801307581553888431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259489503470153550810369149 97308563801307581553888431)
    ·
      refine ⟨145962845701961372330832647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97308563801307581553888431 145962845701961372330832647)
      ·
        refine ⟨218944268552942058496248971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145962845701961372330832647 218944268552942058496248971)
        ·
          refine ⟨328416402829413087744373457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218944268552942058496248971 328416402829413087744373457)
          ·
            refine ⟨246312302122059815808280093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328416402829413087744373457 246312302122059815808280093)
            ·
              refine ⟨92367113295772430928105035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246312302122059815808280093 92367113295772430928105035)
              ·
                refine ⟨138550669943658646392157553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92367113295772430928105035 138550669943658646392157553)
                ·
                  refine ⟨103913002457743984794118165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138550669943658646392157553 103913002457743984794118165)
                  ·
                    refine ⟨4870921990206749287224289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103913002457743984794118165 4870921990206749287224289)
                    ·
                      refine ⟨3653191492655061965418217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4870921990206749287224289 3653191492655061965418217)
                      ·
                        rfl

theorem cell23_7114565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 6, 2].length) (baseStart_7114565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114565 prefixEnd_7114565 := by exact prefixLift 7114565
  have htrace : WordTrace (prefixWord ++ tailWord_7114565) baseStart_7114565 baseEnd_7114565 := by
    simpa [prefixWord, tailWord_7114565, baseEnd_7114565] using wordTrace_append hprefix tailTrace_7114565
  have hstable : (prefixWord ++ tailWord_7114565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114565).length < 2 ^ (prefixWord ++ tailWord_7114565).sum := by decide
  have hdescent : baseEnd_7114565 < baseStart_7114565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114585 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 5]
def baseStart_7114585 : Nat := 118140960795 + 7114585 * 2 ^ 59
def prefixEnd_7114585 : Nat := 4983230072969 + 3 ^ 40 * 7114585 * 2
def baseEnd_7114585 : Nat := 3653201762268151887168125

theorem tailTrace_7114585 : CollatzResearch.WordTrace tailWord_7114585 prefixEnd_7114585 3653201762268151887168125 := by
  unfold tailWord_7114585
  simp only [CollatzResearch.WordTrace]
  refine ⟨259490232930081094226097209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172993488620054062817398139 259490232930081094226097209)
  ·
    refine ⟨194617674697560820669572907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259490232930081094226097209 194617674697560820669572907)
    ·
      refine ⟨291926512046341231004359361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194617674697560820669572907 291926512046341231004359361)
      ·
        refine ⟨218944884034755923253269521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291926512046341231004359361 218944884034755923253269521)
        ·
          refine ⟨164208663026066942439952141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218944884034755923253269521 164208663026066942439952141)
          ·
            refine ⟨61578248634775103414982053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164208663026066942439952141 61578248634775103414982053)
            ·
              refine ⟨11545921619020331890309135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61578248634775103414982053 11545921619020331890309135)
              ·
                refine ⟨17318882428530497835463703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11545921619020331890309135 17318882428530497835463703)
                ·
                  refine ⟨25978323642795746753195555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17318882428530497835463703 25978323642795746753195555)
                  ·
                    refine ⟨38967485464193620129793333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25978323642795746753195555 38967485464193620129793333)
                    ·
                      refine ⟨3653201762268151887168125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38967485464193620129793333 3653201762268151887168125)
                      ·
                        rfl

theorem cell23_7114585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_7114585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114585 prefixEnd_7114585 := by exact prefixLift 7114585
  have htrace : WordTrace (prefixWord ++ tailWord_7114585) baseStart_7114585 baseEnd_7114585 := by
    simpa [prefixWord, tailWord_7114585, baseEnd_7114585] using wordTrace_append hprefix tailTrace_7114585
  have hstable : (prefixWord ++ tailWord_7114585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114585).length < 2 ^ (prefixWord ++ tailWord_7114585).sum := by decide
  have hdescent : baseEnd_7114585 < baseStart_7114585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114608 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_7114608 : Nat := 118140960795 + 7114608 * 2 ^ 59
def prefixEnd_7114608 : Nat := 4983230072969 + 3 ^ 40 * 7114608 * 2
def baseEnd_7114608 : Nat := 3653213572323205297180519

theorem tailTrace_7114608 : CollatzResearch.WordTrace tailWord_7114608 prefixEnd_7114608 3653213572323205297180519 := by
  unfold tailWord_7114608
  simp only [CollatzResearch.WordTrace]
  refine ⟨129745535904498884577092239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172994047872665179436122985 129745535904498884577092239)
  ·
    refine ⟨194618303856748326865638359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129745535904498884577092239 194618303856748326865638359)
    ·
      refine ⟨291927455785122490298457539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194618303856748326865638359 291927455785122490298457539)
      ·
        refine ⟨437891183677683735447686309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291927455785122490298457539 437891183677683735447686309)
        ·
          refine ⟨82104596939565700396441183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 437891183677683735447686309 82104596939565700396441183)
          ·
            refine ⟨123156895409348550594661775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82104596939565700396441183 123156895409348550594661775)
            ·
              refine ⟨184735343114022825891992663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123156895409348550594661775 184735343114022825891992663)
              ·
                refine ⟨277103014671034238837988995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184735343114022825891992663 277103014671034238837988995)
                ·
                  refine ⟨415654522006551358256983493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277103014671034238837988995 415654522006551358256983493)
                  ·
                    refine ⟨77935222876228379673184405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 415654522006551358256983493 77935222876228379673184405)
                    ·
                      refine ⟨3653213572323205297180519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77935222876228379673184405 3653213572323205297180519)
                      ·
                        rfl

theorem cell23_7114608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_7114608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114608 prefixEnd_7114608 := by exact prefixLift 7114608
  have htrace : WordTrace (prefixWord ++ tailWord_7114608) baseStart_7114608 baseEnd_7114608 := by
    simpa [prefixWord, tailWord_7114608, baseEnd_7114608] using wordTrace_append hprefix tailTrace_7114608
  have hstable : (prefixWord ++ tailWord_7114608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114608).length < 2 ^ (prefixWord ++ tailWord_7114608).sum := by decide
  have hdescent : baseEnd_7114608 < baseStart_7114608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114622 : List Nat := [4, 2, 3, 1, 1, 1, 2, 9]
def baseStart_7114622 : Nat := 118140960795 + 7114622 * 2 ^ 59
def prefixEnd_7114622 : Nat := 4983230072969 + 3 ^ 40 * 7114622 * 2
def baseEnd_7114622 : Nat := 135304472631569194163165

theorem tailTrace_7114622 : CollatzResearch.WordTrace tailWord_7114622 prefixEnd_7114622 135304472631569194163165 := by
  unfold tailWord_7114622
  simp only [CollatzResearch.WordTrace]
  refine ⟨32436447803868381193149265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172994388287298033030129413 32436447803868381193149265)
  ·
    refine ⟨24327335852901285894861949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32436447803868381193149265 24327335852901285894861949)
    ·
      refine ⟨9122750944837982210573231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24327335852901285894861949 9122750944837982210573231)
      ·
        refine ⟨13684126417256973315859847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9122750944837982210573231 13684126417256973315859847)
        ·
          refine ⟨20526189625885459973789771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13684126417256973315859847 20526189625885459973789771)
          ·
            refine ⟨30789284438828189960684657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20526189625885459973789771 30789284438828189960684657)
            ·
              refine ⟨23091963329121142470513493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30789284438828189960684657 23091963329121142470513493)
              ·
                refine ⟨135304472631569194163165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23091963329121142470513493 135304472631569194163165)
                ·
                  rfl

theorem cell23_7114622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_7114622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114622 prefixEnd_7114622 := by exact prefixLift 7114622
  have htrace : WordTrace (prefixWord ++ tailWord_7114622) baseStart_7114622 baseEnd_7114622 := by
    simpa [prefixWord, tailWord_7114622, baseEnd_7114622] using wordTrace_append hprefix tailTrace_7114622
  have hstable : (prefixWord ++ tailWord_7114622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114622).length < 2 ^ (prefixWord ++ tailWord_7114622).sum := by decide
  have hdescent : baseEnd_7114622 < baseStart_7114622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114650 : List Nat := [3, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2]
def baseStart_7114650 : Nat := 118140960795 + 7114650 * 2 ^ 59
def prefixEnd_7114650 : Nat := 4983230072969 + 3 ^ 40 * 7114650 * 2
def baseEnd_7114650 : Nat := 3653235138510694132855327

theorem tailTrace_7114650 : CollatzResearch.WordTrace tailWord_7114650 prefixEnd_7114650 3653235138510694132855327 := by
  unfold tailWord_7114650
  simp only [CollatzResearch.WordTrace]
  refine ⟨64873150918711402581803351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172995069116563740218142269 64873150918711402581803351)
  ·
    refine ⟨97309726378067103872705027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64873150918711402581803351 97309726378067103872705027)
    ·
      refine ⟨145964589567100655809057541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97309726378067103872705027 145964589567100655809057541)
      ·
        refine ⟨27368360543831372964198289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145964589567100655809057541 27368360543831372964198289)
        ·
          refine ⟨20526270407873529723148717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27368360543831372964198289 20526270407873529723148717)
          ·
            refine ⟨7697351402952573646180769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20526270407873529723148717 7697351402952573646180769)
            ·
              refine ⟨5773013552214430234635577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7697351402952573646180769 5773013552214430234635577)
              ·
                refine ⟨4329760164160822675976683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5773013552214430234635577 4329760164160822675976683)
                ·
                  refine ⟨6494640246241234013965025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4329760164160822675976683 6494640246241234013965025)
                  ·
                    refine ⟨4870980184680925510473769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6494640246241234013965025 4870980184680925510473769)
                    ·
                      refine ⟨3653235138510694132855327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4870980184680925510473769 3653235138510694132855327)
                      ·
                        rfl

theorem cell23_7114650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_7114650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114650 prefixEnd_7114650 := by exact prefixLift 7114650
  have htrace : WordTrace (prefixWord ++ tailWord_7114650) baseStart_7114650 baseEnd_7114650 := by
    simpa [prefixWord, tailWord_7114650, baseEnd_7114650] using wordTrace_append hprefix tailTrace_7114650
  have hstable : (prefixWord ++ tailWord_7114650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114650).length < 2 ^ (prefixWord ++ tailWord_7114650).sum := by decide
  have hdescent : baseEnd_7114650 < baseStart_7114650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114675 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 3]
def baseStart_7114675 : Nat := 118140960795 + 7114675 * 2 ^ 59
def prefixEnd_7114675 : Nat := 4983230072969 + 3 ^ 40 * 7114675 * 2
def baseEnd_7114675 : Nat := 3653247975527056535042711

theorem tailTrace_7114675 : CollatzResearch.WordTrace tailWord_7114675 prefixEnd_7114675 3653247975527056535042711 := by
  unfold tailWord_7114675
  simp only [CollatzResearch.WordTrace]
  refine ⟨259493515499755039596873479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172995676999836693064582319 259493515499755039596873479)
  ·
    refine ⟨389240273249632559395310219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259493515499755039596873479 389240273249632559395310219)
    ·
      refine ⟨583860409874448839092965329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389240273249632559395310219 583860409874448839092965329)
      ·
        refine ⟨437895307405836629319723997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583860409874448839092965329 437895307405836629319723997)
        ·
          refine ⟨164210740277188735994896499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437895307405836629319723997 164210740277188735994896499)
          ·
            refine ⟨246316110415783103992344749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164210740277188735994896499 246316110415783103992344749)
            ·
              refine ⟨92368541405918663997129281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246316110415783103992344749 92368541405918663997129281)
              ·
                refine ⟨69276406054438997997846961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92368541405918663997129281 69276406054438997997846961)
                ·
                  refine ⟨51957304540829248498385221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69276406054438997997846961 51957304540829248498385221)
                  ·
                    refine ⟨9741994601405484093447229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51957304540829248498385221 9741994601405484093447229)
                    ·
                      refine ⟨3653247975527056535042711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9741994601405484093447229 3653247975527056535042711)
                      ·
                        rfl

theorem cell23_7114675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 3].length) (baseStart_7114675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114675 prefixEnd_7114675 := by exact prefixLift 7114675
  have htrace : WordTrace (prefixWord ++ tailWord_7114675) baseStart_7114675 baseEnd_7114675 := by
    simpa [prefixWord, tailWord_7114675, baseEnd_7114675] using wordTrace_append hprefix tailTrace_7114675
  have hstable : (prefixWord ++ tailWord_7114675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114675).length < 2 ^ (prefixWord ++ tailWord_7114675).sum := by decide
  have hdescent : baseEnd_7114675 < baseStart_7114675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114712 : List Nat := [2, 1, 2, 2, 2, 2, 1, 6, 5]
def baseStart_7114712 : Nat := 118140960795 + 7114712 * 2 ^ 59
def prefixEnd_7114712 : Nat := 4983230072969 + 3 ^ 40 * 7114712 * 2
def baseEnd_7114712 : Nat := 405918552701252543364449

theorem tailTrace_7114712 : CollatzResearch.WordTrace tailWord_7114712 prefixEnd_7114712 405918552701252543364449 := by
  unfold tailWord_7114712
  simp only [CollatzResearch.WordTrace]
  refine ⟨129747432500310497457985195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172996576667080663277313593 129747432500310497457985195)
  ·
    refine ⟨194621148750465746186977793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129747432500310497457985195 194621148750465746186977793)
    ·
      refine ⟨145965861562849309640233345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194621148750465746186977793 145965861562849309640233345)
      ·
        refine ⟨109474396172136982230175009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145965861562849309640233345 109474396172136982230175009)
        ·
          refine ⟨82105797129102736672631257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109474396172136982230175009 82105797129102736672631257)
          ·
            refine ⟨61579347846827052504473443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82105797129102736672631257 61579347846827052504473443)
            ·
              refine ⟨92369021770240578756710165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61579347846827052504473443 92369021770240578756710165)
              ·
                refine ⟨4329797895480027129220789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92369021770240578756710165 4329797895480027129220789)
                ·
                  refine ⟨405918552701252543364449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4329797895480027129220789 405918552701252543364449)
                  ·
                    rfl

theorem cell23_7114712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 5].length) (baseStart_7114712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114712 prefixEnd_7114712 := by exact prefixLift 7114712
  have htrace : WordTrace (prefixWord ++ tailWord_7114712) baseStart_7114712 baseEnd_7114712 := by
    simpa [prefixWord, tailWord_7114712, baseEnd_7114712] using wordTrace_append hprefix tailTrace_7114712
  have hstable : (prefixWord ++ tailWord_7114712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114712).length < 2 ^ (prefixWord ++ tailWord_7114712).sum := by decide
  have hdescent : baseEnd_7114712 < baseStart_7114712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114723 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 2, 2, 2]
def baseStart_7114723 : Nat := 118140960795 + 7114723 * 2 ^ 59
def prefixEnd_7114723 : Nat := 4983230072969 + 3 ^ 40 * 7114723 * 2
def baseEnd_7114723 : Nat := 3653272622598472347242491

theorem tailTrace_7114723 : CollatzResearch.WordTrace tailWord_7114723 prefixEnd_7114723 3653272622598472347242491 := by
  unfold tailWord_7114723
  simp only [CollatzResearch.WordTrace]
  refine ⟨259495266203581143794620823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172996844135720762529747215 259495266203581143794620823)
  ·
    refine ⟨389242899305371715691931235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259495266203581143794620823 389242899305371715691931235)
    ·
      refine ⟨583864348958057573537896853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389242899305371715691931235 583864348958057573537896853)
      ·
        refine ⟨27368641357408948759588915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 583864348958057573537896853 27368641357408948759588915)
        ·
          refine ⟨41052962036113423139383373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27368641357408948759588915 41052962036113423139383373)
          ·
            refine ⟨15394860763542533677268765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41052962036113423139383373 15394860763542533677268765)
            ·
              refine ⟨5773072786328450128975787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15394860763542533677268765 5773072786328450128975787)
              ·
                refine ⟨8659609179492675193463681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5773072786328450128975787 8659609179492675193463681)
                ·
                  refine ⟨6494706884619506395097761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8659609179492675193463681 6494706884619506395097761)
                  ·
                    refine ⟨4871030163464629796323321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6494706884619506395097761 4871030163464629796323321)
                    ·
                      refine ⟨3653272622598472347242491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871030163464629796323321 3653272622598472347242491)
                      ·
                        rfl

theorem cell23_7114723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_7114723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114723 prefixEnd_7114723 := by exact prefixLift 7114723
  have htrace : WordTrace (prefixWord ++ tailWord_7114723) baseStart_7114723 baseEnd_7114723 := by
    simpa [prefixWord, tailWord_7114723, baseEnd_7114723] using wordTrace_append hprefix tailTrace_7114723
  have hstable : (prefixWord ++ tailWord_7114723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114723).length < 2 ^ (prefixWord ++ tailWord_7114723).sum := by decide
  have hdescent : baseEnd_7114723 < baseStart_7114723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114732 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 2, 5, 2]
def baseStart_7114732 : Nat := 118140960795 + 7114732 * 2 ^ 59
def prefixEnd_7114732 : Nat := 4983230072969 + 3 ^ 40 * 7114732 * 2
def baseEnd_7114732 : Nat := 3653277243924362812029949

theorem tailTrace_7114732 : CollatzResearch.WordTrace tailWord_7114732 prefixEnd_7114732 3653277243924362812029949 := by
  unfold tailWord_7114732
  simp only [CollatzResearch.WordTrace]
  refine ⟨129747797230274269165849225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172997062973699025554465633 129747797230274269165849225)
  ·
    refine ⟨97310847922705701874386919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129747797230274269165849225 97310847922705701874386919)
    ·
      refine ⟨145966271884058552811580379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97310847922705701874386919 145966271884058552811580379)
      ·
        refine ⟨218949407826087829217370569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145966271884058552811580379 218949407826087829217370569)
        ·
          refine ⟨164212055869565871913027927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218949407826087829217370569 164212055869565871913027927)
          ·
            refine ⟨246318083804348807869541891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164212055869565871913027927 246318083804348807869541891)
            ·
              refine ⟨369477125706523211804312837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246318083804348807869541891 369477125706523211804312837)
              ·
                refine ⟨69276961069973102213308657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369477125706523211804312837 69276961069973102213308657)
                ·
                  refine ⟨51957720802479826659981493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69276961069973102213308657 51957720802479826659981493)
                  ·
                    refine ⟨4871036325232483749373265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51957720802479826659981493 4871036325232483749373265)
                    ·
                      refine ⟨3653277243924362812029949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871036325232483749373265 3653277243924362812029949)
                      ·
                        rfl

theorem cell23_7114732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 5, 2].length) (baseStart_7114732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114732 prefixEnd_7114732 := by exact prefixLift 7114732
  have htrace : WordTrace (prefixWord ++ tailWord_7114732) baseStart_7114732 baseEnd_7114732 := by
    simpa [prefixWord, tailWord_7114732, baseEnd_7114732] using wordTrace_append hprefix tailTrace_7114732
  have hstable : (prefixWord ++ tailWord_7114732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114732).length < 2 ^ (prefixWord ++ tailWord_7114732).sum := by decide
  have hdescent : baseEnd_7114732 < baseStart_7114732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114839 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 4, 3, 2]
def baseStart_7114839 : Nat := 118140960795 + 7114839 * 2 ^ 59
def prefixEnd_7114839 : Nat := 4983230072969 + 3 ^ 40 * 7114839 * 2
def baseEnd_7114839 : Nat := 3653332186354393893391957

theorem tailTrace_7114839 : CollatzResearch.WordTrace tailWord_7114839 prefixEnd_7114839 3653332186354393893391957 := by
  unfold tailWord_7114839
  simp only [CollatzResearch.WordTrace]
  refine ⟨259499497071160895605843571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172999664714107263737229047 259499497071160895605843571)
  ·
    refine ⟨389249245606741343408765357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259499497071160895605843571 389249245606741343408765357)
    ·
      refine ⟨145968467102528003778287009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389249245606741343408765357 145968467102528003778287009)
      ·
        refine ⟨109476350326896002833715257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145968467102528003778287009 109476350326896002833715257)
        ·
          refine ⟨82107262745172002125286443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109476350326896002833715257 82107262745172002125286443)
          ·
            refine ⟨123160894117758003187929665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82107262745172002125286443 123160894117758003187929665)
            ·
              refine ⟨92370670588318502390947249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123160894117758003187929665 92370670588318502390947249)
              ·
                refine ⟨69278002941238876793210437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92370670588318502390947249 69278002941238876793210437)
                ·
                  refine ⟨12989625551482289398726957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69278002941238876793210437 12989625551482289398726957)
                  ·
                    refine ⟨4871109581805858524522609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12989625551482289398726957 4871109581805858524522609)
                    ·
                      refine ⟨3653332186354393893391957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871109581805858524522609 3653332186354393893391957)
                      ·
                        rfl

theorem cell23_7114839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_7114839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114839 prefixEnd_7114839 := by exact prefixLift 7114839
  have htrace : WordTrace (prefixWord ++ tailWord_7114839) baseStart_7114839 baseEnd_7114839 := by
    simpa [prefixWord, tailWord_7114839, baseEnd_7114839] using wordTrace_append hprefix tailTrace_7114839
  have hstable : (prefixWord ++ tailWord_7114839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114839).length < 2 ^ (prefixWord ++ tailWord_7114839).sum := by decide
  have hdescent : baseEnd_7114839 < baseStart_7114839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114850 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7114850 : Nat := 118140960795 + 7114850 * 2 ^ 59
def prefixEnd_7114850 : Nat := 4983230072969 + 3 ^ 40 * 7114850 * 2
def baseEnd_7114850 : Nat := 3653337834641593350354407

theorem tailTrace_7114850 : CollatzResearch.WordTrace tailWord_7114850 prefixEnd_7114850 3653337834641593350354407 := by
  unfold tailWord_7114850
  simp only [CollatzResearch.WordTrace]
  refine ⟨64874974568530261121123501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172999932182747362989662669 64874974568530261121123501)
  ·
    refine ⟨24328115463198847920421313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64874974568530261121123501 24328115463198847920421313)
    ·
      refine ⟨18246086597399135940315985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24328115463198847920421313 18246086597399135940315985)
      ·
        refine ⟨13684564948049351955236989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18246086597399135940315985 13684564948049351955236989)
        ·
          refine ⟨5131711855518506983213871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13684564948049351955236989 5131711855518506983213871)
          ·
            refine ⟨7697567783277760474820807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131711855518506983213871 7697567783277760474820807)
            ·
              refine ⟨11546351674916640712231211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7697567783277760474820807 11546351674916640712231211)
              ·
                refine ⟨17319527512374961068346817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11546351674916640712231211 17319527512374961068346817)
                ·
                  refine ⟨12989645634281220801260113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17319527512374961068346817 12989645634281220801260113)
                  ·
                    refine ⟨9742234225710915600945085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12989645634281220801260113 9742234225710915600945085)
                    ·
                      refine ⟨3653337834641593350354407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9742234225710915600945085 3653337834641593350354407)
                      ·
                        rfl

theorem cell23_7114850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7114850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114850 prefixEnd_7114850 := by exact prefixLift 7114850
  have htrace : WordTrace (prefixWord ++ tailWord_7114850) baseStart_7114850 baseEnd_7114850 := by
    simpa [prefixWord, tailWord_7114850, baseEnd_7114850] using wordTrace_append hprefix tailTrace_7114850
  have hstable : (prefixWord ++ tailWord_7114850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114850).length < 2 ^ (prefixWord ++ tailWord_7114850).sum := by decide
  have hdescent : baseEnd_7114850 < baseStart_7114850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114863 : List Nat := [1, 1, 2, 1, 3, 5, 2, 3, 1, 1, 3]
def baseStart_7114863 : Nat := 118140960795 + 7114863 * 2 ^ 59
def prefixEnd_7114863 : Nat := 4983230072969 + 3 ^ 40 * 7114863 * 2
def baseEnd_7114863 : Nat := 3653344509890101799491847

theorem tailTrace_7114863 : CollatzResearch.WordTrace tailWord_7114863 prefixEnd_7114863 3653344509890101799491847 := by
  unfold tailWord_7114863
  simp only [CollatzResearch.WordTrace]
  refine ⟨259500372423073947704717243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173000248282049298469811495 259500372423073947704717243)
  ·
    refine ⟨389250558634610921557075865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259500372423073947704717243 389250558634610921557075865)
    ·
      refine ⟨291937918975958191167806899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389250558634610921557075865 291937918975958191167806899)
      ·
        refine ⟨437906878463937286751710349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291937918975958191167806899 437906878463937286751710349)
        ·
          refine ⟨164215079423976482531891381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437906878463937286751710349 164215079423976482531891381)
          ·
            refine ⟨15395163695997795237364817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164215079423976482531891381 15395163695997795237364817)
            ·
              refine ⟨11546372771998346428023613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15395163695997795237364817 11546372771998346428023613)
              ·
                refine ⟨4329889789499379910508855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11546372771998346428023613 4329889789499379910508855)
                ·
                  refine ⟨6494834684249069865763283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4329889789499379910508855 6494834684249069865763283)
                  ·
                    refine ⟨9742252026373604798644925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6494834684249069865763283 9742252026373604798644925)
                    ·
                      refine ⟨3653344509890101799491847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9742252026373604798644925 3653344509890101799491847)
                      ·
                        rfl

theorem cell23_7114863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 1, 1, 3].length) (baseStart_7114863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114863 prefixEnd_7114863 := by exact prefixLift 7114863
  have htrace : WordTrace (prefixWord ++ tailWord_7114863) baseStart_7114863 baseEnd_7114863 := by
    simpa [prefixWord, tailWord_7114863, baseEnd_7114863] using wordTrace_append hprefix tailTrace_7114863
  have hstable : (prefixWord ++ tailWord_7114863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114863).length < 2 ^ (prefixWord ++ tailWord_7114863).sum := by decide
  have hdescent : baseEnd_7114863 < baseStart_7114863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114866 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_7114866 : Nat := 118140960795 + 7114866 * 2 ^ 59
def prefixEnd_7114866 : Nat := 4983230072969 + 3 ^ 40 * 7114866 * 2
def baseEnd_7114866 : Nat := 1217782016777355095918111

theorem tailTrace_7114866 : CollatzResearch.WordTrace tailWord_7114866 prefixEnd_7114866 1217782016777355095918111 := by
  unfold tailWord_7114866
  simp only [CollatzResearch.WordTrace]
  refine ⟨64875120460515769804269113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173000321228042052811384301 64875120460515769804269113)
  ·
    refine ⟨48656340345386827353201835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64875120460515769804269113 48656340345386827353201835)
    ·
      refine ⟨72984510518080241029802753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48656340345386827353201835 72984510518080241029802753)
      ·
        refine ⟨54738382888560180772352065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72984510518080241029802753 54738382888560180772352065)
        ·
          refine ⟨41053787166420135579264049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54738382888560180772352065 41053787166420135579264049)
          ·
            refine ⟨30790340374815101684448037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41053787166420135579264049 30790340374815101684448037)
            ·
              refine ⟨5773188820277831565834007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30790340374815101684448037 5773188820277831565834007)
              ·
                refine ⟨8659783230416747348751011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5773188820277831565834007 8659783230416747348751011)
                ·
                  refine ⟨12989674845625121023126517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8659783230416747348751011 12989674845625121023126517)
                  ·
                    refine ⟨1217782016777355095918111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12989674845625121023126517 1217782016777355095918111)
                    ·
                      rfl

theorem cell23_7114866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_7114866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114866 prefixEnd_7114866 := by exact prefixLift 7114866
  have htrace : WordTrace (prefixWord ++ tailWord_7114866) baseStart_7114866 baseEnd_7114866 := by
    simpa [prefixWord, tailWord_7114866, baseEnd_7114866] using wordTrace_append hprefix tailTrace_7114866
  have hstable : (prefixWord ++ tailWord_7114866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114866).length < 2 ^ (prefixWord ++ tailWord_7114866).sum := by decide
  have hdescent : baseEnd_7114866 < baseStart_7114866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114872 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_7114872 : Nat := 118140960795 + 7114872 * 2 ^ 59
def prefixEnd_7114872 : Nat := 4983230072969 + 3 ^ 40 * 7114872 * 2
def baseEnd_7114872 : Nat := 3653349131215992264279305

theorem tailTrace_7114872 : CollatzResearch.WordTrace tailWord_7114872 prefixEnd_7114872 3653349131215992264279305 := by
  unfold tailWord_7114872
  simp only [CollatzResearch.WordTrace]
  refine ⟨129750350340020671120897435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173000467120027561494529913 129750350340020671120897435)
  ·
    refine ⟨194625525510031006681346153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129750350340020671120897435 194625525510031006681346153)
    ·
      refine ⟨145969144132523255011009615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194625525510031006681346153 145969144132523255011009615)
      ·
        refine ⟨218953716198784882516514423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145969144132523255011009615 218953716198784882516514423)
        ·
          refine ⟨328430574298177323774771635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218953716198784882516514423 328430574298177323774771635)
          ·
            refine ⟨492645861447265985662157453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328430574298177323774771635 492645861447265985662157453)
            ·
              refine ⟨184742198042724744623309045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 492645861447265985662157453 184742198042724744623309045)
              ·
                refine ⟨17319581066505444808435223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184742198042724744623309045 17319581066505444808435223)
                ·
                  refine ⟨25979371599758167212652835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17319581066505444808435223 25979371599758167212652835)
                  ·
                    refine ⟨38969057399637250818979253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25979371599758167212652835 38969057399637250818979253)
                    ·
                      refine ⟨3653349131215992264279305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38969057399637250818979253 3653349131215992264279305)
                      ·
                        rfl

theorem cell23_7114872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_7114872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114872 prefixEnd_7114872 := by exact prefixLift 7114872
  have htrace : WordTrace (prefixWord ++ tailWord_7114872) baseStart_7114872 baseEnd_7114872 := by
    simpa [prefixWord, tailWord_7114872, baseEnd_7114872] using wordTrace_append hprefix tailTrace_7114872
  have hstable : (prefixWord ++ tailWord_7114872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114872).length < 2 ^ (prefixWord ++ tailWord_7114872).sum := by decide
  have hdescent : baseEnd_7114872 < baseStart_7114872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114896 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 2, 4]
def baseStart_7114896 : Nat := 118140960795 + 7114896 * 2 ^ 59
def prefixEnd_7114896 : Nat := 4983230072969 + 3 ^ 40 * 7114896 * 2
def baseEnd_7114896 : Nat := 1217787151583900056793065

theorem tailTrace_7114896 : CollatzResearch.WordTrace tailWord_7114896 prefixEnd_7114896 1217787151583900056793065 := by
  unfold tailWord_7114896
  simp only [CollatzResearch.WordTrace]
  refine ⟨129750788015977197170334271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173001050687969596227112361 129750788015977197170334271)
  ·
    refine ⟨194626182023965795755501407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129750788015977197170334271 194626182023965795755501407)
    ·
      refine ⟨291939273035948693633252111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194626182023965795755501407 291939273035948693633252111)
      ·
        refine ⟨437908909553923040449878167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291939273035948693633252111 437908909553923040449878167)
        ·
          refine ⟨656863364330884560674817251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437908909553923040449878167 656863364330884560674817251)
          ·
            refine ⟨985295046496326841012225877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656863364330884560674817251 985295046496326841012225877)
            ·
              refine ⟨5773213163064415084056011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 985295046496326841012225877 5773213163064415084056011)
              ·
                refine ⟨8659819744596622626084017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5773213163064415084056011 8659819744596622626084017)
                ·
                  refine ⟨6494864808447466969563013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8659819744596622626084017 6494864808447466969563013)
                  ·
                    refine ⟨1217787151583900056793065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6494864808447466969563013 1217787151583900056793065)
                    ·
                      rfl

theorem cell23_7114896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 2, 4].length) (baseStart_7114896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114896 prefixEnd_7114896 := by exact prefixLift 7114896
  have htrace : WordTrace (prefixWord ++ tailWord_7114896) baseStart_7114896 baseEnd_7114896 := by
    simpa [prefixWord, tailWord_7114896, baseEnd_7114896] using wordTrace_append hprefix tailTrace_7114896
  have hstable : (prefixWord ++ tailWord_7114896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114896).length < 2 ^ (prefixWord ++ tailWord_7114896).sum := by decide
  have hdescent : baseEnd_7114896 < baseStart_7114896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114909 : List Nat := [1, 4, 2, 1, 1, 3, 4, 7]
def baseStart_7114909 : Nat := 118140960795 + 7114909 * 2 ^ 59
def prefixEnd_7114909 : Nat := 4983230072969 + 3 ^ 40 * 7114909 * 2
def baseEnd_7114909 : Nat := 135309930740748467389505

theorem tailTrace_7114909 : CollatzResearch.WordTrace tailWord_7114909 prefixEnd_7114909 135309930740748467389505 := by
  unfold tailWord_7114909
  simp only [CollatzResearch.WordTrace]
  refine ⟨259502050180907297560891781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173001366787271531707261187 259502050180907297560891781)
  ·
    refine ⟨48656634408920118292667209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259502050180907297560891781 48656634408920118292667209)
    ·
      refine ⟨36492475806690088719500407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48656634408920118292667209 36492475806690088719500407)
      ·
        refine ⟨54738713710035133079250611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36492475806690088719500407 54738713710035133079250611)
        ·
          refine ⟨82108070565052699618875917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54738713710035133079250611 82108070565052699618875917)
          ·
            refine ⟨30790526461894762357078469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82108070565052699618875917 30790526461894762357078469)
            ·
              refine ⟨5773223711605267941952213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30790526461894762357078469 5773223711605267941952213)
              ·
                refine ⟨135309930740748467389505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5773223711605267941952213 135309930740748467389505)
                ·
                  rfl

theorem cell23_7114909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 7].length) (baseStart_7114909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114909 prefixEnd_7114909 := by exact prefixLift 7114909
  have htrace : WordTrace (prefixWord ++ tailWord_7114909) baseStart_7114909 baseEnd_7114909 := by
    simpa [prefixWord, tailWord_7114909, baseEnd_7114909] using wordTrace_append hprefix tailTrace_7114909
  have hstable : (prefixWord ++ tailWord_7114909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114909).length < 2 ^ (prefixWord ++ tailWord_7114909).sum := by decide
  have hdescent : baseEnd_7114909 < baseStart_7114909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114936 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 2, 1, 3]
def baseStart_7114936 : Nat := 118140960795 + 7114936 * 2 ^ 59
def prefixEnd_7114936 : Nat := 4983230072969 + 3 ^ 40 * 7114936 * 2
def baseEnd_7114936 : Nat := 3653381993977880013879011

theorem tailTrace_7114936 : CollatzResearch.WordTrace tailWord_7114936 prefixEnd_7114936 3653381993977880013879011 := by
  unfold tailWord_7114936
  simp only [CollatzResearch.WordTrace]
  refine ⟨129751517475904740586062331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173002023301206320781416441 129751517475904740586062331)
  ·
    refine ⟨194627276213857110879093497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129751517475904740586062331 194627276213857110879093497)
    ·
      refine ⟨145970457160392833159320123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194627276213857110879093497 145970457160392833159320123)
      ·
        refine ⟨218955685740589249738980185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145970457160392833159320123 218955685740589249738980185)
        ·
          refine ⟨164216764305441937304235139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218955685740589249738980185 164216764305441937304235139)
          ·
            refine ⟨246325146458162905956352709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164216764305441937304235139 246325146458162905956352709)
            ·
              refine ⟨46185964960905544866816133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246325146458162905956352709 46185964960905544866816133)
              ·
                refine ⟨8659868430169789662528025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46185964960905544866816133 8659868430169789662528025)
                ·
                  refine ⟨6494901322627342246896019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8659868430169789662528025 6494901322627342246896019)
                  ·
                    refine ⟨9742351983941013370344029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6494901322627342246896019 9742351983941013370344029)
                    ·
                      refine ⟨3653381993977880013879011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9742351983941013370344029 3653381993977880013879011)
                      ·
                        rfl

theorem cell23_7114936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_7114936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114936 prefixEnd_7114936 := by exact prefixLift 7114936
  have htrace : WordTrace (prefixWord ++ tailWord_7114936) baseStart_7114936 baseEnd_7114936 := by
    simpa [prefixWord, tailWord_7114936, baseEnd_7114936] using wordTrace_append hprefix tailTrace_7114936
  have hstable : (prefixWord ++ tailWord_7114936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114936).length < 2 ^ (prefixWord ++ tailWord_7114936).sum := by decide
  have hdescent : baseEnd_7114936 < baseStart_7114936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114952 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 1, 8]
def baseStart_7114952 : Nat := 118140960795 + 7114952 * 2 ^ 59
def prefixEnd_7114952 : Nat := 4983230072969 + 3 ^ 40 * 7114952 * 2
def baseEnd_7114952 : Nat := 1217796736556117317092979

theorem tailTrace_7114952 : CollatzResearch.WordTrace tailWord_7114952 prefixEnd_7114952 1217796736556117317092979 := by
  unfold tailWord_7114952
  simp only [CollatzResearch.WordTrace]
  refine ⟨129751809259875757952353555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173002412346501010603138073 129751809259875757952353555)
  ·
    refine ⟨194627713889813636928530333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129751809259875757952353555 194627713889813636928530333)
    ·
      refine ⟨72985392708680113848198875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194627713889813636928530333 72985392708680113848198875)
      ·
        refine ⟨109478089063020170772298313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72985392708680113848198875 109478089063020170772298313)
        ·
          refine ⟨82108566797265128079223735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109478089063020170772298313 82108566797265128079223735)
          ·
            refine ⟨123162850195897692118835603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82108566797265128079223735 123162850195897692118835603)
            ·
              refine ⟨184744275293846538178253405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123162850195897692118835603 184744275293846538178253405)
              ·
                refine ⟨69279103235192451816845027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184744275293846538178253405 69279103235192451816845027)
                ·
                  refine ⟨103918654852788677725267541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69279103235192451816845027 103918654852788677725267541)
                  ·
                    refine ⟨1217796736556117317092979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103918654852788677725267541 1217796736556117317092979)
                    ·
                      rfl

theorem cell23_7114952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_7114952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114952 prefixEnd_7114952 := by exact prefixLift 7114952
  have htrace : WordTrace (prefixWord ++ tailWord_7114952) baseStart_7114952 baseEnd_7114952 := by
    simpa [prefixWord, tailWord_7114952, baseEnd_7114952] using wordTrace_append hprefix tailTrace_7114952
  have hstable : (prefixWord ++ tailWord_7114952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114952).length < 2 ^ (prefixWord ++ tailWord_7114952).sum := by decide
  have hdescent : baseEnd_7114952 < baseStart_7114952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114976 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 1, 4, 2]
def baseStart_7114976 : Nat := 118140960795 + 7114976 * 2 ^ 59
def prefixEnd_7114976 : Nat := 4983230072969 + 3 ^ 40 * 7114976 * 2
def baseEnd_7114976 : Nat := 3653402533204059857378827

theorem tailTrace_7114976 : CollatzResearch.WordTrace tailWord_7114976 prefixEnd_7114976 3653402533204059857378827 := by
  unfold tailWord_7114976
  simp only [CollatzResearch.WordTrace]
  refine ⟨129752246935832284001790391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173002995914443045335720521 129752246935832284001790391)
  ·
    refine ⟨194628370403748426002685587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129752246935832284001790391 194628370403748426002685587)
    ·
      refine ⟨291942555605622639004028381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194628370403748426002685587 291942555605622639004028381)
      ·
        refine ⟨109478458352108489626510643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291942555605622639004028381 109478458352108489626510643)
        ·
          refine ⟨164217687528162734439765965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109478458352108489626510643 164217687528162734439765965)
          ·
            refine ⟨61581632823061025414912237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164217687528162734439765965 61581632823061025414912237)
            ·
              refine ⟨23093112308647884530592089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61581632823061025414912237 23093112308647884530592089)
              ·
                refine ⟨17319834231485913397944067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23093112308647884530592089 17319834231485913397944067)
                ·
                  refine ⟨25979751347228870096916101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17319834231485913397944067 25979751347228870096916101)
                  ·
                    refine ⟨4871203377605413143171769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25979751347228870096916101 4871203377605413143171769)
                    ·
                      refine ⟨3653402533204059857378827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871203377605413143171769 3653402533204059857378827)
                      ·
                        rfl

theorem cell23_7114976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_7114976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114976 prefixEnd_7114976 := by exact prefixLift 7114976
  have htrace : WordTrace (prefixWord ++ tailWord_7114976) baseStart_7114976 baseEnd_7114976 := by
    simpa [prefixWord, tailWord_7114976, baseEnd_7114976] using wordTrace_append hprefix tailTrace_7114976
  have hstable : (prefixWord ++ tailWord_7114976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114976).length < 2 ^ (prefixWord ++ tailWord_7114976).sum := by decide
  have hdescent : baseEnd_7114976 < baseStart_7114976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7114992 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_7114992 : Nat := 118140960795 + 7114992 * 2 ^ 59
def prefixEnd_7114992 : Nat := 4983230072969 + 3 ^ 40 * 7114992 * 2
def baseEnd_7114992 : Nat := 3653410748894531794778753

theorem tailTrace_7114992 : CollatzResearch.WordTrace tailWord_7114992 prefixEnd_7114992 3653410748894531794778753 := by
  unfold tailWord_7114992
  simp only [CollatzResearch.WordTrace]
  refine ⟨129752538719803301368081615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173003384959737735157442153 129752538719803301368081615)
  ·
    refine ⟨194628808079704952052122423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129752538719803301368081615 194628808079704952052122423)
    ·
      refine ⟨291943212119557428078183635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194628808079704952052122423 291943212119557428078183635)
      ·
        refine ⟨437914818179336142117275453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291943212119557428078183635 437914818179336142117275453)
        ·
          refine ⟨164218056817251053293978295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437914818179336142117275453 164218056817251053293978295)
          ·
            refine ⟨246327085225876579940967443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164218056817251053293978295 246327085225876579940967443)
            ·
              refine ⟨369490627838814869911451165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246327085225876579940967443 369490627838814869911451165)
              ·
                refine ⟨138558985439555576216794187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369490627838814869911451165 138558985439555576216794187)
                ·
                  refine ⟨207838478159333364325191281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138558985439555576216794187 207838478159333364325191281)
                  ·
                    refine ⟨155878858619500023243893461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 207838478159333364325191281 155878858619500023243893461)
                    ·
                      refine ⟨3653410748894531794778753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155878858619500023243893461 3653410748894531794778753)
                      ·
                        rfl

theorem cell23_7114992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_7114992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114992 prefixEnd_7114992 := by exact prefixLift 7114992
  have htrace : WordTrace (prefixWord ++ tailWord_7114992) baseStart_7114992 baseEnd_7114992 := by
    simpa [prefixWord, tailWord_7114992, baseEnd_7114992] using wordTrace_append hprefix tailTrace_7114992
  have hstable : (prefixWord ++ tailWord_7114992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114992).length < 2 ^ (prefixWord ++ tailWord_7114992).sum := by decide
  have hdescent : baseEnd_7114992 < baseStart_7114992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
