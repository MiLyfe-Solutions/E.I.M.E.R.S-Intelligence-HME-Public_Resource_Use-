import V185TrunkScan21Chunk056

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_691124 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 5]
def baseStart_691124 : Nat := 118140960795 + 691124 * 2 ^ 59
def prefixEnd_691124 : Nat := 4983230072969 + 3 ^ 40 * 691124 * 2
def baseEnd_691124 : Nat := 157723912825804092387371

theorem tailTrace_691124 : CollatzResearch.WordTrace tailWord_691124 prefixEnd_691124 157723912825804092387371 := by
  unfold tailWord_691124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12603681574091628713548213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16804908765455504951397617 12603681574091628713548213)
  ·
    refine ⟨1181595147571090191895145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12603681574091628713548213 1181595147571090191895145)
    ·
      refine ⟨886196360678317643921359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1181595147571090191895145 886196360678317643921359)
      ·
        refine ⟨1329294541017476465882039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886196360678317643921359 1329294541017476465882039)
        ·
          refine ⟨1993941811526214698823059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329294541017476465882039 1993941811526214698823059)
          ·
            refine ⟨2990912717289322048234589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993941811526214698823059 2990912717289322048234589)
            ·
              refine ⟨1121592268983495768087971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2990912717289322048234589 1121592268983495768087971)
              ·
                refine ⟨1682388403475243652131957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121592268983495768087971 1682388403475243652131957)
                ·
                  refine ⟨157723912825804092387371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1682388403475243652131957 157723912825804092387371)
                  ·
                    rfl

theorem cell21_691124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_691124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691124 prefixEnd_691124 := by exact prefixLift 691124
  have htrace : WordTrace (prefixWord ++ tailWord_691124) baseStart_691124 baseEnd_691124 := by
    simpa [prefixWord, tailWord_691124, baseEnd_691124] using wordTrace_append hprefix tailTrace_691124
  have hstable : (prefixWord ++ tailWord_691124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691124).length < 2 ^ (prefixWord ++ tailWord_691124).sum := by decide
  have hdescent : baseEnd_691124 < baseStart_691124 := by decide
  rcases family_descends (prefixWord ++ tailWord_691124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691183 : List Nat := [1, 1, 2, 1, 4, 4, 1, 4, 3]
def baseStart_691183 : Nat := 118140960795 + 691183 * 2 ^ 59
def prefixEnd_691183 : Nat := 4983230072969 + 3 ^ 40 * 691183 * 2
def baseEnd_691183 : Nat := 157737377429633100903917

theorem tailTrace_691183 : CollatzResearch.WordTrace tailWord_691183 prefixEnd_691183 157737377429633100903917 := by
  unfold tailWord_691183
  simp only [CollatzResearch.WordTrace]
  refine ⟨25209515054969510503494203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16806343369979673668996135 25209515054969510503494203)
  ·
    refine ⟨37814272582454265755241305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25209515054969510503494203 37814272582454265755241305)
    ·
      refine ⟨28360704436840699316430979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37814272582454265755241305 28360704436840699316430979)
      ·
        refine ⟨42541056655261048974646469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28360704436840699316430979 42541056655261048974646469)
        ·
          refine ⟨7976448122861446682746213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42541056655261048974646469 7976448122861446682746213)
          ·
            refine ⟨1495584023036521253014915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7976448122861446682746213 1495584023036521253014915)
            ·
              refine ⟨2243376034554781879522373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495584023036521253014915 2243376034554781879522373)
              ·
                refine ⟨420633006479021602410445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2243376034554781879522373 420633006479021602410445)
                ·
                  refine ⟨157737377429633100903917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420633006479021602410445 157737377429633100903917)
                  ·
                    rfl

theorem cell21_691183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 3].length) (baseStart_691183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691183 prefixEnd_691183 := by exact prefixLift 691183
  have htrace : WordTrace (prefixWord ++ tailWord_691183) baseStart_691183 baseEnd_691183 := by
    simpa [prefixWord, tailWord_691183, baseEnd_691183] using wordTrace_append hprefix tailTrace_691183
  have hstable : (prefixWord ++ tailWord_691183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691183).length < 2 ^ (prefixWord ++ tailWord_691183).sum := by decide
  have hdescent : baseEnd_691183 < baseStart_691183 := by decide
  rcases family_descends (prefixWord ++ tailWord_691183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691186 : List Nat := [3, 2, 1, 5, 2, 1, 1, 6]
def baseStart_691186 : Nat := 118140960795 + 691186 * 2 ^ 59
def prefixEnd_691186 : Nat := 4983230072969 + 3 ^ 40 * 691186 * 2
def baseEnd_691186 : Nat := 52579354023501920784637

theorem tailTrace_691186 : CollatzResearch.WordTrace tailWord_691186 prefixEnd_691186 52579354023501920784637 := by
  unfold tailWord_691186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302406118489660503963353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16806416315972428010568941 6302406118489660503963353)
  ·
    refine ⟨4726804588867245377972515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6302406118489660503963353 4726804588867245377972515)
    ·
      refine ⟨7090206883300868066958773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4726804588867245377972515 7090206883300868066958773)
      ·
        refine ⟨664706895309456381277385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7090206883300868066958773 664706895309456381277385)
        ·
          refine ⟨498530171482092285958039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 664706895309456381277385 498530171482092285958039)
          ·
            refine ⟨747795257223138428937059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498530171482092285958039 747795257223138428937059)
            ·
              refine ⟨1121692885834707643405589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747795257223138428937059 1121692885834707643405589)
              ·
                refine ⟨52579354023501920784637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1121692885834707643405589 52579354023501920784637)
                ·
                  rfl

theorem cell21_691186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_691186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691186 prefixEnd_691186 := by exact prefixLift 691186
  have htrace : WordTrace (prefixWord ++ tailWord_691186) baseStart_691186 baseEnd_691186 := by
    simpa [prefixWord, tailWord_691186, baseEnd_691186] using wordTrace_append hprefix tailTrace_691186
  have hstable : (prefixWord ++ tailWord_691186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691186).length < 2 ^ (prefixWord ++ tailWord_691186).sum := by decide
  have hdescent : baseEnd_691186 < baseStart_691186 := by decide
  rcases family_descends (prefixWord ++ tailWord_691186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691293 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 5]
def baseStart_691293 : Nat := 118140960795 + 691293 * 2 ^ 59
def prefixEnd_691293 : Nat := 4983230072969 + 3 ^ 40 * 691293 * 2
def baseEnd_691293 : Nat := 157762480928297354070359

theorem tailTrace_691293 : CollatzResearch.WordTrace tailWord_691293 prefixEnd_691293 157762480928297354070359 := by
  unfold tailWord_691293
  simp only [CollatzResearch.WordTrace]
  refine ⟨25213527084570999289998533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16809018056380666193332355 25213527084570999289998533)
  ·
    refine ⟨4727536328357062366874725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25213527084570999289998533 4727536328357062366874725)
    ·
      refine ⟨886413061566949193789011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4727536328357062366874725 886413061566949193789011)
      ·
        refine ⟨1329619592350423790683517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886413061566949193789011 1329619592350423790683517)
        ·
          refine ⟨498607347131408921506319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1329619592350423790683517 498607347131408921506319)
          ·
            refine ⟨747911020697113382259479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498607347131408921506319 747911020697113382259479)
            ·
              refine ⟨1121866531045670073389219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747911020697113382259479 1121866531045670073389219)
              ·
                refine ⟨1682799796568505110083829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121866531045670073389219 1682799796568505110083829)
                ·
                  refine ⟨157762480928297354070359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1682799796568505110083829 157762480928297354070359)
                  ·
                    rfl

theorem cell21_691293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_691293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691293 prefixEnd_691293 := by exact prefixLift 691293
  have htrace : WordTrace (prefixWord ++ tailWord_691293) baseStart_691293 baseEnd_691293 := by
    simpa [prefixWord, tailWord_691293, baseEnd_691293] using wordTrace_append hprefix tailTrace_691293
  have hstable : (prefixWord ++ tailWord_691293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691293).length < 2 ^ (prefixWord ++ tailWord_691293).sum := by decide
  have hdescent : baseEnd_691293 < baseStart_691293 := by decide
  rcases family_descends (prefixWord ++ tailWord_691293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691318 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_691318 : Nat := 118140960795 + 691318 * 2 ^ 59
def prefixEnd_691318 : Nat := 4983230072969 + 3 ^ 40 * 691318 * 2
def baseEnd_691318 : Nat := 157768186268902866153641

theorem tailTrace_691318 : CollatzResearch.WordTrace tailWord_691318 prefixEnd_691318 157768186268902866153641 := by
  unfold tailWord_691318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575902431842526784978663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16809625939653619039772405 1575902431842526784978663)
  ·
    refine ⟨2363853647763790177467995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1575902431842526784978663 2363853647763790177467995)
    ·
      refine ⟨3545780471645685266201993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2363853647763790177467995 3545780471645685266201993)
      ·
        refine ⟨2659335353734263949651495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3545780471645685266201993 2659335353734263949651495)
        ·
          refine ⟨3989003030601395924477243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2659335353734263949651495 3989003030601395924477243)
          ·
            refine ⟨5983504545902093886715865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3989003030601395924477243 5983504545902093886715865)
            ·
              refine ⟨4487628409426570415036899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5983504545902093886715865 4487628409426570415036899)
              ·
                refine ⟨6731442614139855622555349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4487628409426570415036899 6731442614139855622555349)
                ·
                  refine ⟨157768186268902866153641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6731442614139855622555349 157768186268902866153641)
                  ·
                    rfl

theorem cell21_691318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_691318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691318 prefixEnd_691318 := by exact prefixLift 691318
  have htrace : WordTrace (prefixWord ++ tailWord_691318) baseStart_691318 baseEnd_691318 := by
    simpa [prefixWord, tailWord_691318, baseEnd_691318] using wordTrace_append hprefix tailTrace_691318
  have hstable : (prefixWord ++ tailWord_691318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691318).length < 2 ^ (prefixWord ++ tailWord_691318).sum := by decide
  have hdescent : baseEnd_691318 < baseStart_691318 := by decide
  rcases family_descends (prefixWord ++ tailWord_691318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691352 : List Nat := [2, 1, 2, 4, 2, 1, 4, 2, 3]
def baseStart_691352 : Nat := 118140960795 + 691352 * 2 ^ 59
def prefixEnd_691352 : Nat := 4983230072969 + 3 ^ 40 * 691352 * 2
def baseEnd_691352 : Nat := 157775945532126362586905

theorem tailTrace_691352 : CollatzResearch.WordTrace tailWord_691352 prefixEnd_691352 157775945532126362586905 := by
  unfold tailWord_691352
  simp only [CollatzResearch.WordTrace]
  refine ⟨12607839495678626183198155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16810452660904834910930873 12607839495678626183198155)
  ·
    refine ⟨18911759243517939274797233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12607839495678626183198155 18911759243517939274797233)
    ·
      refine ⟨14183819432638454456097925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18911759243517939274797233 14183819432638454456097925)
      ·
        refine ⟨2659466143619710210518361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14183819432638454456097925 2659466143619710210518361)
        ·
          refine ⟨1994599607714782657888771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2659466143619710210518361 1994599607714782657888771)
          ·
            refine ⟨2991899411572173986833157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994599607714782657888771 2991899411572173986833157)
            ·
              refine ⟨560981139669782622531217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2991899411572173986833157 560981139669782622531217)
              ·
                refine ⟨420735854752336966898413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560981139669782622531217 420735854752336966898413)
                ·
                  refine ⟨157775945532126362586905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420735854752336966898413 157775945532126362586905)
                  ·
                    rfl

theorem cell21_691352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 3].length) (baseStart_691352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691352 prefixEnd_691352 := by exact prefixLift 691352
  have htrace : WordTrace (prefixWord ++ tailWord_691352) baseStart_691352 baseEnd_691352 := by
    simpa [prefixWord, tailWord_691352, baseEnd_691352] using wordTrace_append hprefix tailTrace_691352
  have hstable : (prefixWord ++ tailWord_691352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691352).length < 2 ^ (prefixWord ++ tailWord_691352).sum := by decide
  have hdescent : baseEnd_691352 < baseStart_691352 := by decide
  rcases family_descends (prefixWord ++ tailWord_691352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691439 : List Nat := [1, 1, 2, 1, 7, 1, 1, 7]
def baseStart_691439 : Nat := 118140960795 + 691439 * 2 ^ 59
def prefixEnd_691439 : Nat := 4983230072969 + 3 ^ 40 * 691439 * 2
def baseEnd_691439 : Nat := 52598600039144514878909

theorem tailTrace_691439 : CollatzResearch.WordTrace tailWord_691439 prefixEnd_691439 52598600039144514878909 := by
  unfold tailWord_691439
  simp only [CollatzResearch.WordTrace]
  refine ⟨25218852142042066224813371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16812568094694710816542247 25218852142042066224813371)
  ·
    refine ⟨37828278213063099337220057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25218852142042066224813371 37828278213063099337220057)
    ·
      refine ⟨28371208659797324502915043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37828278213063099337220057 28371208659797324502915043)
      ·
        refine ⟨42556812989695986754372565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28371208659797324502915043 42556812989695986754372565)
        ·
          refine ⟨997425304445999689555607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 42556812989695986754372565 997425304445999689555607)
          ·
            refine ⟨1496137956668999534333411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997425304445999689555607 1496137956668999534333411)
            ·
              refine ⟨2244206935003499301500117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496137956668999534333411 2244206935003499301500117)
              ·
                refine ⟨52598600039144514878909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2244206935003499301500117 52598600039144514878909)
                ·
                  rfl

theorem cell21_691439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 7].length) (baseStart_691439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691439 prefixEnd_691439 := by exact prefixLift 691439
  have htrace : WordTrace (prefixWord ++ tailWord_691439) baseStart_691439 baseEnd_691439 := by
    simpa [prefixWord, tailWord_691439, baseEnd_691439] using wordTrace_append hprefix tailTrace_691439
  have hstable : (prefixWord ++ tailWord_691439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691439).length < 2 ^ (prefixWord ++ tailWord_691439).sum := by decide
  have hdescent : baseEnd_691439 < baseStart_691439 := by decide
  rcases family_descends (prefixWord ++ tailWord_691439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691470 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_691470 : Nat := 118140960795 + 691470 * 2 ^ 59
def prefixEnd_691470 : Nat := 4983230072969 + 3 ^ 40 * 691470 * 2
def baseEnd_691470 : Nat := 157802874739784379619997

theorem tailTrace_691470 : CollatzResearch.WordTrace tailWord_691470 prefixEnd_691470 157802874739784379619997 := by
  unfold tailWord_691470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152497850616219814898983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16813321869953172346127909 3152497850616219814898983)
  ·
    refine ⟨4728746775924329722348475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3152497850616219814898983 4728746775924329722348475)
    ·
      refine ⟨7093120163886494583522713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4728746775924329722348475 7093120163886494583522713)
      ·
        refine ⟨5319840122914870937642035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7093120163886494583522713 5319840122914870937642035)
        ·
          refine ⟨7979760184372306406463053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5319840122914870937642035 7979760184372306406463053)
          ·
            refine ⟨2992410069139614902423645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7979760184372306406463053 2992410069139614902423645)
            ·
              refine ⟨1122153775927355588408867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2992410069139614902423645 1122153775927355588408867)
              ·
                refine ⟨1683230663891033382613301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122153775927355588408867 1683230663891033382613301)
                ·
                  refine ⟨157802874739784379619997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1683230663891033382613301 157802874739784379619997)
                  ·
                    rfl

theorem cell21_691470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_691470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691470 prefixEnd_691470 := by exact prefixLift 691470
  have htrace : WordTrace (prefixWord ++ tailWord_691470) baseStart_691470 baseEnd_691470 := by
    simpa [prefixWord, tailWord_691470, baseEnd_691470] using wordTrace_append hprefix tailTrace_691470
  have hstable : (prefixWord ++ tailWord_691470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691470).length < 2 ^ (prefixWord ++ tailWord_691470).sum := by decide
  have hdescent : baseEnd_691470 < baseStart_691470 := by decide
  rcases family_descends (prefixWord ++ tailWord_691470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691521 : List Nat := [1, 2, 5, 2, 1, 3, 2, 2, 3]
def baseStart_691521 : Nat := 118140960795 + 691521 * 2 ^ 59
def prefixEnd_691521 : Nat := 4983230072969 + 3 ^ 40 * 691521 * 2
def baseEnd_691521 : Nat := 157814513634619624269893

theorem tailTrace_691521 : CollatzResearch.WordTrace tailWord_691521 prefixEnd_691521 157814513634619624269893 := by
  unfold tailWord_691521
  simp only [CollatzResearch.WordTrace]
  refine ⟨25221842927744994229298417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16814561951829996152865611 25221842927744994229298417)
  ·
    refine ⟨18916382195808745671973813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25221842927744994229298417 18916382195808745671973813)
    ·
      refine ⟨1773410830857069906747545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18916382195808745671973813 1773410830857069906747545)
      ·
        refine ⟨1330058123142802430060659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1773410830857069906747545 1330058123142802430060659)
        ·
          refine ⟨1995087184714203645090989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330058123142802430060659 1995087184714203645090989)
          ·
            refine ⟨748157694267826366909121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1995087184714203645090989 748157694267826366909121)
            ·
              refine ⟨561118270700869775181841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748157694267826366909121 561118270700869775181841)
              ·
                refine ⟨420838703025652331386381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561118270700869775181841 420838703025652331386381)
                ·
                  refine ⟨157814513634619624269893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420838703025652331386381 157814513634619624269893)
                  ·
                    rfl

theorem cell21_691521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 3].length) (baseStart_691521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691521 prefixEnd_691521 := by exact prefixLift 691521
  have htrace : WordTrace (prefixWord ++ tailWord_691521) baseStart_691521 baseEnd_691521 := by
    simpa [prefixWord, tailWord_691521, baseEnd_691521] using wordTrace_append hprefix tailTrace_691521
  have hstable : (prefixWord ++ tailWord_691521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691521).length < 2 ^ (prefixWord ++ tailWord_691521).sum := by decide
  have hdescent : baseEnd_691521 < baseStart_691521 := by decide
  rcases family_descends (prefixWord ++ tailWord_691521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691605 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 5]
def baseStart_691605 : Nat := 118140960795 + 691605 * 2 ^ 59
def prefixEnd_691605 : Nat := 4983230072969 + 3 ^ 40 * 691605 * 2
def baseEnd_691605 : Nat := 157833683579054144869721

theorem tailTrace_691605 : CollatzResearch.WordTrace tailWord_691605 prefixEnd_691605 157833683579054144869721 := by
  unfold tailWord_691605
  simp only [CollatzResearch.WordTrace]
  refine ⟨25224906659440676575356269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16816604439627117716904179 25224906659440676575356269)
  ·
    refine ⟨9459339997290253715758601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25224906659440676575356269 9459339997290253715758601)
    ·
      refine ⟨7094504997967690286818951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9459339997290253715758601 7094504997967690286818951)
      ·
        refine ⟨10641757496951535430228427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7094504997967690286818951 10641757496951535430228427)
        ·
          refine ⟨15962636245427303145342641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10641757496951535430228427 15962636245427303145342641)
          ·
            refine ⟨11971977184070477359006981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15962636245427303145342641 11971977184070477359006981)
            ·
              refine ⟨2244745722013214504813809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11971977184070477359006981 2244745722013214504813809)
              ·
                refine ⟨1683559291509910878610357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244745722013214504813809 1683559291509910878610357)
                ·
                  refine ⟨157833683579054144869721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1683559291509910878610357 157833683579054144869721)
                  ·
                    rfl

theorem cell21_691605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_691605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691605 prefixEnd_691605 := by exact prefixLift 691605
  have htrace : WordTrace (prefixWord ++ tailWord_691605) baseStart_691605 baseEnd_691605 := by
    simpa [prefixWord, tailWord_691605, baseEnd_691605] using wordTrace_append hprefix tailTrace_691605
  have hstable : (prefixWord ++ tailWord_691605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691605).length < 2 ^ (prefixWord ++ tailWord_691605).sum := by decide
  have hdescent : baseEnd_691605 < baseStart_691605 := by decide
  rcases family_descends (prefixWord ++ tailWord_691605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691614 : List Nat := [4, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_691614 : Nat := 118140960795 + 691614 * 2 ^ 59
def prefixEnd_691614 : Nat := 4983230072969 + 3 ^ 40 * 691614 * 2
def baseEnd_691614 : Nat := 157835737501672129219703

theorem tailTrace_691614 : CollatzResearch.WordTrace tailWord_691614 prefixEnd_691614 157835737501672129219703 := by
  unfold tailWord_691614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3153154364551008889054237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16816823277605380741622597 3153154364551008889054237)
  ·
    refine ⟨1182432886706628333395339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3153154364551008889054237 1182432886706628333395339)
    ·
      refine ⟨1773649330059942500093009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1182432886706628333395339 1773649330059942500093009)
      ·
        refine ⟨1330236997544956875069757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1773649330059942500093009 1330236997544956875069757)
        ·
          refine ⟨498838874079358828151159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1330236997544956875069757 498838874079358828151159)
          ·
            refine ⟨748258311119038242226739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498838874079358828151159 748258311119038242226739)
            ·
              refine ⟨1122387466678557363340109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748258311119038242226739 1122387466678557363340109)
              ·
                refine ⟨420895300004459011252541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1122387466678557363340109 420895300004459011252541)
                ·
                  refine ⟨157835737501672129219703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420895300004459011252541 157835737501672129219703)
                  ·
                    rfl

theorem cell21_691614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_691614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691614 prefixEnd_691614 := by exact prefixLift 691614
  have htrace : WordTrace (prefixWord ++ tailWord_691614) baseStart_691614 baseEnd_691614 := by
    simpa [prefixWord, tailWord_691614, baseEnd_691614] using wordTrace_append hprefix tailTrace_691614
  have hstable : (prefixWord ++ tailWord_691614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691614).length < 2 ^ (prefixWord ++ tailWord_691614).sum := by decide
  have hdescent : baseEnd_691614 < baseStart_691614 := by decide
  rcases family_descends (prefixWord ++ tailWord_691614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691619 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 8]
def baseStart_691619 : Nat := 118140960795 + 691619 * 2 ^ 59
def prefixEnd_691619 : Nat := 4983230072969 + 3 ^ 40 * 691619 * 2
def baseEnd_691619 : Nat := 157836878569793231636359

theorem tailTrace_691619 : CollatzResearch.WordTrace tailWord_691619 prefixEnd_691619 157836878569793231636359 := by
  unfold tailWord_691619
  simp only [CollatzResearch.WordTrace]
  refine ⟨25225417281389956966365911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16816944854259971310910607 25225417281389956966365911)
  ·
    refine ⟨37838125922084935449548867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25225417281389956966365911 37838125922084935449548867)
    ·
      refine ⟨56757188883127403174323301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37838125922084935449548867 56757188883127403174323301)
      ·
        refine ⟨10641972915586388095185619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56757188883127403174323301 10641972915586388095185619)
        ·
          refine ⟨15962959373379582142778429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10641972915586388095185619 15962959373379582142778429)
          ·
            refine ⟨5986109765017343303541911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15962959373379582142778429 5986109765017343303541911)
            ·
              refine ⟨8979164647526014955312867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5986109765017343303541911 8979164647526014955312867)
              ·
                refine ⟨13468746971289022432969301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8979164647526014955312867 13468746971289022432969301)
                ·
                  refine ⟨157836878569793231636359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13468746971289022432969301 157836878569793231636359)
                  ·
                    rfl

theorem cell21_691619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_691619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691619 prefixEnd_691619 := by exact prefixLift 691619
  have htrace : WordTrace (prefixWord ++ tailWord_691619) baseStart_691619 baseEnd_691619 := by
    simpa [prefixWord, tailWord_691619, baseEnd_691619] using wordTrace_append hprefix tailTrace_691619
  have hstable : (prefixWord ++ tailWord_691619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691619).length < 2 ^ (prefixWord ++ tailWord_691619).sum := by decide
  have hdescent : baseEnd_691619 < baseStart_691619 := by decide
  rcases family_descends (prefixWord ++ tailWord_691619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691639 : List Nat := [1, 1, 3, 1, 3, 2, 5, 2, 3]
def baseStart_691639 : Nat := 118140960795 + 691639 * 2 ^ 59
def prefixEnd_691639 : Nat := 4983230072969 + 3 ^ 40 * 691639 * 2
def baseEnd_691639 : Nat := 157841442842277641302985

theorem tailTrace_691639 : CollatzResearch.WordTrace tailWord_691639 prefixEnd_691639 157841442842277641302985 := by
  unfold tailWord_691639
  simp only [CollatzResearch.WordTrace]
  refine ⟨25226146741317500382093971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16817431160878333588062647 25226146741317500382093971)
  ·
    refine ⟨37839220111976250573140957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25226146741317500382093971 37839220111976250573140957)
    ·
      refine ⟨14189707541991093964927859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37839220111976250573140957 14189707541991093964927859)
      ·
        refine ⟨21284561312986640947391789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14189707541991093964927859 21284561312986640947391789)
        ·
          refine ⟨7981710492369990355271921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21284561312986640947391789 7981710492369990355271921)
          ·
            refine ⟨5986282869277492766453941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7981710492369990355271921 5986282869277492766453941)
            ·
              refine ⟨561214018994764946855057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5986282869277492766453941 561214018994764946855057)
              ·
                refine ⟨420910514246073710141293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561214018994764946855057 420910514246073710141293)
                ·
                  refine ⟨157841442842277641302985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420910514246073710141293 157841442842277641302985)
                  ·
                    rfl

theorem cell21_691639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 3].length) (baseStart_691639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691639 prefixEnd_691639 := by exact prefixLift 691639
  have htrace : WordTrace (prefixWord ++ tailWord_691639) baseStart_691639 baseEnd_691639 := by
    simpa [prefixWord, tailWord_691639, baseEnd_691639] using wordTrace_append hprefix tailTrace_691639
  have hstable : (prefixWord ++ tailWord_691639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691639).length < 2 ^ (prefixWord ++ tailWord_691639).sum := by decide
  have hdescent : baseEnd_691639 < baseStart_691639 := by decide
  rcases family_descends (prefixWord ++ tailWord_691639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691695 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 6]
def baseStart_691695 : Nat := 118140960795 + 691695 * 2 ^ 59
def prefixEnd_691695 : Nat := 4983230072969 + 3 ^ 40 * 691695 * 2
def baseEnd_691695 : Nat := 157854222805233988369537

theorem tailTrace_691695 : CollatzResearch.WordTrace tailWord_691695 prefixEnd_691695 157854222805233988369537 := by
  unfold tailWord_691695
  simp only [CollatzResearch.WordTrace]
  refine ⟨25228189229114621946132539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16818792819409747964088359 25228189229114621946132539)
  ·
    refine ⟨37842283843671932919198809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25228189229114621946132539 37842283843671932919198809)
    ·
      refine ⟨28381712882753949689399107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37842283843671932919198809 28381712882753949689399107)
      ·
        refine ⟨42572569324130924534098661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28381712882753949689399107 42572569324130924534098661)
        ·
          refine ⟨7982356748274548350143499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42572569324130924534098661 7982356748274548350143499)
          ·
            refine ⟨11973535122411822525215249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7982356748274548350143499 11973535122411822525215249)
            ·
              refine ⟨8980151341808866893911437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11973535122411822525215249 8980151341808866893911437)
              ·
                refine ⟨3367556753178325085216789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8980151341808866893911437 3367556753178325085216789)
                ·
                  refine ⟨157854222805233988369537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3367556753178325085216789 157854222805233988369537)
                  ·
                    rfl

theorem cell21_691695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_691695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691695 prefixEnd_691695 := by exact prefixLift 691695
  have htrace : WordTrace (prefixWord ++ tailWord_691695) baseStart_691695 baseEnd_691695 := by
    simpa [prefixWord, tailWord_691695, baseEnd_691695] using wordTrace_append hprefix tailTrace_691695
  have hstable : (prefixWord ++ tailWord_691695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691695).length < 2 ^ (prefixWord ++ tailWord_691695).sum := by decide
  have hdescent : baseEnd_691695 < baseStart_691695 := by decide
  rcases family_descends (prefixWord ++ tailWord_691695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691864 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 4]
def baseStart_691864 : Nat := 118140960795 + 691864 * 2 ^ 59
def prefixEnd_691864 : Nat := 4983230072969 + 3 ^ 40 * 691864 * 2
def baseEnd_691864 : Nat := 157892790907727250052525

theorem tailTrace_691864 : CollatzResearch.WordTrace tailWord_691864 prefixEnd_691864 157892790907727250052525 := by
  unfold tailWord_691864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12617176582751181904517323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16822902110334909206023097 12617176582751181904517323)
  ·
    refine ⟨18925764874126772856775985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12617176582751181904517323 18925764874126772856775985)
    ·
      refine ⟨14194323655595079642581989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18925764874126772856775985 14194323655595079642581989)
      ·
        refine ⟨2661435685424077432984123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14194323655595079642581989 2661435685424077432984123)
        ·
          refine ⟨3992153528136116149476185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661435685424077432984123 3992153528136116149476185)
          ·
            refine ⟨2994115146102087112107139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3992153528136116149476185 2994115146102087112107139)
            ·
              refine ⟨4491172719153130668160709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994115146102087112107139 4491172719153130668160709)
              ·
                refine ⟨842094884841212000280133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4491172719153130668160709 842094884841212000280133)
                ·
                  refine ⟨157892790907727250052525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 842094884841212000280133 157892790907727250052525)
                  ·
                    rfl

theorem cell21_691864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_691864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691864 prefixEnd_691864 := by exact prefixLift 691864
  have htrace : WordTrace (prefixWord ++ tailWord_691864) baseStart_691864 baseEnd_691864 := by
    simpa [prefixWord, tailWord_691864, baseEnd_691864] using wordTrace_append hprefix tailTrace_691864
  have hstable : (prefixWord ++ tailWord_691864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691864).length < 2 ^ (prefixWord ++ tailWord_691864).sum := by decide
  have hdescent : baseEnd_691864 < baseStart_691864 := by decide
  rcases family_descends (prefixWord ++ tailWord_691864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691895 : List Nat := [1, 1, 3, 1, 5, 2, 3, 5]
def baseStart_691895 : Nat := 118140960795 + 691895 * 2 ^ 59
def prefixEnd_691895 : Nat := 4983230072969 + 3 ^ 40 * 691895 * 2
def baseEnd_691895 : Nat := 52633288510026028345265

theorem tailTrace_691895 : CollatzResearch.WordTrace tailWord_691895 prefixEnd_691895 52633288510026028345265 := by
  unfold tailWord_691895
  simp only [CollatzResearch.WordTrace]
  refine ⟨25235483828390056103413139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16823655885593370735608759 25235483828390056103413139)
  ·
    refine ⟨37853225742585084155119709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25235483828390056103413139 37853225742585084155119709)
    ·
      refine ⟨14194959653469406558169891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37853225742585084155119709 14194959653469406558169891)
      ·
        refine ⟨21292439480204109837254837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14194959653469406558169891 21292439480204109837254837)
        ·
          refine ⟨1996166201269135297242641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21292439480204109837254837 1996166201269135297242641)
          ·
            refine ⟨1497124650951851472931981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1996166201269135297242641 1497124650951851472931981)
            ·
              refine ⟨561421744106944302349493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1497124650951851472931981 561421744106944302349493)
              ·
                refine ⟨52633288510026028345265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 561421744106944302349493 52633288510026028345265)
                ·
                  rfl

theorem cell21_691895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 5].length) (baseStart_691895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691895 prefixEnd_691895 := by exact prefixLift 691895
  have htrace : WordTrace (prefixWord ++ tailWord_691895) baseStart_691895 baseEnd_691895 := by
    simpa [prefixWord, tailWord_691895, baseEnd_691895] using wordTrace_append hprefix tailTrace_691895
  have hstable : (prefixWord ++ tailWord_691895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691895).length < 2 ^ (prefixWord ++ tailWord_691895).sum := by decide
  have hdescent : baseEnd_691895 < baseStart_691895 := by decide
  rcases family_descends (prefixWord ++ tailWord_691895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691954 : List Nat := [3, 2, 1, 3, 1, 1, 3, 7]
def baseStart_691954 : Nat := 118140960795 + 691954 * 2 ^ 59
def prefixEnd_691954 : Nat := 4983230072969 + 3 ^ 40 * 691954 * 2
def baseEnd_691954 : Nat := 52637776711302364517447

theorem tailTrace_691954 : CollatzResearch.WordTrace tailWord_691954 prefixEnd_691954 52637776711302364517447 := by
  unfold tailWord_691954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6309408933794077294952729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16825090490117539453207277 6309408933794077294952729)
  ·
    refine ⟨4732056700345557971214547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6309408933794077294952729 4732056700345557971214547)
    ·
      refine ⟨7098085050518336956821821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4732056700345557971214547 7098085050518336956821821)
      ·
        refine ⟨2661781893944376358808183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7098085050518336956821821 2661781893944376358808183)
        ·
          refine ⟨3992672840916564538212275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661781893944376358808183 3992672840916564538212275)
          ·
            refine ⟨5989009261374846807318413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992672840916564538212275 5989009261374846807318413)
            ·
              refine ⟨2245878473015567552744405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5989009261374846807318413 2245878473015567552744405)
              ·
                refine ⟨52637776711302364517447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2245878473015567552744405 52637776711302364517447)
                ·
                  rfl

theorem cell21_691954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_691954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_691954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_691954 prefixEnd_691954 := by exact prefixLift 691954
  have htrace : WordTrace (prefixWord ++ tailWord_691954) baseStart_691954 baseEnd_691954 := by
    simpa [prefixWord, tailWord_691954, baseEnd_691954] using wordTrace_append hprefix tailTrace_691954
  have hstable : (prefixWord ++ tailWord_691954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691954).length < 2 ^ (prefixWord ++ tailWord_691954).sum := by decide
  have hdescent : baseEnd_691954 < baseStart_691954 := by decide
  rcases family_descends (prefixWord ++ tailWord_691954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692030 : List Nat := [4, 2, 1, 2, 2, 10]
def baseStart_692030 : Nat := 118140960795 + 692030 * 2 ^ 59
def prefixEnd_692030 : Nat := 4983230072969 + 3 ^ 40 * 692030 * 2
def baseEnd_692030 : Nat := 5849284235901772232797

theorem tailTrace_692030 : CollatzResearch.WordTrace tailWord_692030 prefixEnd_692030 5849284235901772232797 := by
  unfold tailWord_692030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3155050960362621769947193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16826938455267316106385029 3155050960362621769947193)
  ·
    refine ⟨2366288220271966327460395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3155050960362621769947193 2366288220271966327460395)
    ·
      refine ⟨3549432330407949491190593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2366288220271966327460395 3549432330407949491190593)
      ·
        refine ⟨2662074247805962118392945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3549432330407949491190593 2662074247805962118392945)
        ·
          refine ⟨1996555685854471588794709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2662074247805962118392945 1996555685854471588794709)
          ·
            refine ⟨5849284235901772232797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1996555685854471588794709 5849284235901772232797)
            ·
              rfl

theorem cell21_692030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 10].length) (baseStart_692030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692030 prefixEnd_692030 := by exact prefixLift 692030
  have htrace : WordTrace (prefixWord ++ tailWord_692030) baseStart_692030 baseEnd_692030 := by
    simpa [prefixWord, tailWord_692030, baseEnd_692030] using wordTrace_append hprefix tailTrace_692030
  have hstable : (prefixWord ++ tailWord_692030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692030).length < 2 ^ (prefixWord ++ tailWord_692030).sum := by decide
  have hdescent : baseEnd_692030 < baseStart_692030 := by decide
  rcases family_descends (prefixWord ++ tailWord_692030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692089 : List Nat := [1, 2, 1, 3, 2, 2, 10]
def baseStart_692089 : Nat := 118140960795 + 692089 * 2 ^ 59
def prefixEnd_692089 : Nat := 4983230072969 + 3 ^ 40 * 692089 * 2
def baseEnd_692089 : Nat := 17549348774797428755785

theorem tailTrace_692089 : CollatzResearch.WordTrace tailWord_692089 prefixEnd_692089 17549348774797428755785 := by
  unfold tailWord_692089
  simp only [CollatzResearch.WordTrace]
  refine ⟨25242559589687227235975321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16828373059791484823983547 25242559589687227235975321)
  ·
    refine ⟨18931919692265420426981491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25242559589687227235975321 18931919692265420426981491)
    ·
      refine ⟨28397879538398130640472237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18931919692265420426981491 28397879538398130640472237)
      ·
        refine ⟨10649204826899298990177089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28397879538398130640472237 10649204826899298990177089)
        ·
          refine ⟨7986903620174474242632817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10649204826899298990177089 7986903620174474242632817)
          ·
            refine ⟨5990177715130855681974613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7986903620174474242632817 5990177715130855681974613)
            ·
              refine ⟨17549348774797428755785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5990177715130855681974613 17549348774797428755785)
              ·
                rfl

theorem cell21_692089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 10].length) (baseStart_692089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692089 prefixEnd_692089 := by exact prefixLift 692089
  have htrace : WordTrace (prefixWord ++ tailWord_692089) baseStart_692089 baseEnd_692089 := by
    simpa [prefixWord, tailWord_692089, baseEnd_692089] using wordTrace_append hprefix tailTrace_692089
  have hstable : (prefixWord ++ tailWord_692089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692089).length < 2 ^ (prefixWord ++ tailWord_692089).sum := by decide
  have hdescent : baseEnd_692089 < baseStart_692089 := by decide
  rcases family_descends (prefixWord ++ tailWord_692089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692137 : List Nat := [1, 2, 1, 1, 1, 1, 4, 7, 3]
def baseStart_692137 : Nat := 118140960795 + 692137 * 2 ^ 59
def prefixEnd_692137 : Nat := 4983230072969 + 3 ^ 40 * 692137 * 2
def baseEnd_692137 : Nat := 157955093227139442001967

theorem tailTrace_692137 : CollatzResearch.WordTrace tailWord_692137 prefixEnd_692137 157955093227139442001967 := by
  unfold tailWord_692137
  simp only [CollatzResearch.WordTrace]
  refine ⟨25244310293513331433722665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16829540195675554289148443 25244310293513331433722665)
  ·
    refine ⟨18933232720134998575291999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25244310293513331433722665 18933232720134998575291999)
    ·
      refine ⟨28399849080202497862937999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18933232720134998575291999 28399849080202497862937999)
      ·
        refine ⟨42599773620303746794406999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28399849080202497862937999 42599773620303746794406999)
        ·
          refine ⟨63899660430455620191610499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42599773620303746794406999 63899660430455620191610499)
          ·
            refine ⟨95849490645683430287415749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63899660430455620191610499 95849490645683430287415749)
            ·
              refine ⟨17971779496065643178890453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95849490645683430287415749 17971779496065643178890453)
              ·
                refine ⟨421213581939038512005245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17971779496065643178890453 421213581939038512005245)
                ·
                  refine ⟨157955093227139442001967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421213581939038512005245 157955093227139442001967)
                  ·
                    rfl

theorem cell21_692137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 3].length) (baseStart_692137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692137 prefixEnd_692137 := by exact prefixLift 692137
  have htrace : WordTrace (prefixWord ++ tailWord_692137) baseStart_692137 baseEnd_692137 := by
    simpa [prefixWord, tailWord_692137, baseEnd_692137] using wordTrace_append hprefix tailTrace_692137
  have hstable : (prefixWord ++ tailWord_692137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692137).length < 2 ^ (prefixWord ++ tailWord_692137).sum := by decide
  have hdescent : baseEnd_692137 < baseStart_692137 := by decide
  rcases family_descends (prefixWord ++ tailWord_692137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692151 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 4]
def baseStart_692151 : Nat := 118140960795 + 692151 * 2 ^ 59
def prefixEnd_692151 : Nat := 4983230072969 + 3 ^ 40 * 692151 * 2
def baseEnd_692151 : Nat := 157958288217878528768605

theorem tailTrace_692151 : CollatzResearch.WordTrace tailWord_692151 prefixEnd_692151 157958288217878528768605 := by
  unfold tailWord_692151
  simp only [CollatzResearch.WordTrace]
  refine ⟨25244820915462611824732307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16829880610308407883154871 25244820915462611824732307)
  ·
    refine ⟨37867231373193917737098461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25244820915462611824732307 37867231373193917737098461)
    ·
      refine ⟨14200211764947719151411923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37867231373193917737098461 14200211764947719151411923)
      ·
        refine ⟨21300317647421578727117885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14200211764947719151411923 21300317647421578727117885)
        ·
          refine ⟨7987619117783092022669207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21300317647421578727117885 7987619117783092022669207)
          ·
            refine ⟨11981428676674638034003811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7987619117783092022669207 11981428676674638034003811)
            ·
              refine ⟨17972143015011957051005717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11981428676674638034003811 17972143015011957051005717)
              ·
                refine ⟨842444203828685486765893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17972143015011957051005717 842444203828685486765893)
                ·
                  refine ⟨157958288217878528768605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 842444203828685486765893 157958288217878528768605)
                  ·
                    rfl

theorem cell21_692151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 4].length) (baseStart_692151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692151 prefixEnd_692151 := by exact prefixLift 692151
  have htrace : WordTrace (prefixWord ++ tailWord_692151) baseStart_692151 baseEnd_692151 := by
    simpa [prefixWord, tailWord_692151, baseEnd_692151] using wordTrace_append hprefix tailTrace_692151
  have hstable : (prefixWord ++ tailWord_692151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692151).length < 2 ^ (prefixWord ++ tailWord_692151).sum := by decide
  have hdescent : baseEnd_692151 < baseStart_692151 := by decide
  rcases family_descends (prefixWord ++ tailWord_692151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692168 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 4]
def baseStart_692168 : Nat := 118140960795 + 692168 * 2 ^ 59
def prefixEnd_692168 : Nat := 4983230072969 + 3 ^ 40 * 692168 * 2
def baseEnd_692168 : Nat := 157962167849490276985237

theorem tailTrace_692168 : CollatzResearch.WordTrace tailWord_692168 prefixEnd_692168 157962167849490276985237 := by
  unfold tailWord_692168
  simp only [CollatzResearch.WordTrace]
  refine ⟨12622720478200511864050579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16830293970934015818734105 12622720478200511864050579)
  ·
    refine ⟨18934080717300767796075869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12622720478200511864050579 18934080717300767796075869)
    ·
      refine ⟨7100280268987787923528451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18934080717300767796075869 7100280268987787923528451)
      ·
        refine ⟨10650420403481681885292677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7100280268987787923528451 10650420403481681885292677)
        ·
          refine ⟨1996953825652815353492377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10650420403481681885292677 1996953825652815353492377)
          ·
            refine ⟨1497715369239611515119283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1996953825652815353492377 1497715369239611515119283)
            ·
              refine ⟨2246573053859417272678925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497715369239611515119283 2246573053859417272678925)
              ·
                refine ⟨842464895197281477254597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2246573053859417272678925 842464895197281477254597)
                ·
                  refine ⟨157962167849490276985237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 842464895197281477254597 157962167849490276985237)
                  ·
                    rfl

theorem cell21_692168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_692168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692168 prefixEnd_692168 := by exact prefixLift 692168
  have htrace : WordTrace (prefixWord ++ tailWord_692168) baseStart_692168 baseEnd_692168 := by
    simpa [prefixWord, tailWord_692168, baseEnd_692168] using wordTrace_append hprefix tailTrace_692168
  have hstable : (prefixWord ++ tailWord_692168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692168).length < 2 ^ (prefixWord ++ tailWord_692168).sum := by decide
  have hdescent : baseEnd_692168 < baseStart_692168 := by decide
  rcases family_descends (prefixWord ++ tailWord_692168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692205 : List Nat := [1, 5, 1, 4, 1, 2, 2, 2, 3]
def baseStart_692205 : Nat := 118140960795 + 692205 * 2 ^ 59
def prefixEnd_692205 : Nat := 4983230072969 + 3 ^ 40 * 692205 * 2
def baseEnd_692205 : Nat := 157970611753586434868495

theorem tailTrace_692205 : CollatzResearch.WordTrace tailWord_692205 prefixEnd_692205 157970611753586434868495 := by
  unfold tailWord_692205
  simp only [CollatzResearch.WordTrace]
  refine ⟨25246790457266979047198069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16831193638177986031465379 25246790457266979047198069)
  ·
    refine ⟨2366886605368779285674819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25246790457266979047198069 2366886605368779285674819)
    ·
      refine ⟨3550329908053168928512229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2366886605368779285674819 3550329908053168928512229)
      ·
        refine ⟨665686857759969174096043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3550329908053168928512229 665686857759969174096043)
        ·
          refine ⟨998530286639953761144065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665686857759969174096043 998530286639953761144065)
          ·
            refine ⟨748897714979965320858049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 998530286639953761144065 748897714979965320858049)
            ·
              refine ⟨561673286234973990643537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748897714979965320858049 561673286234973990643537)
              ·
                refine ⟨421254964676230492982653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561673286234973990643537 421254964676230492982653)
                ·
                  refine ⟨157970611753586434868495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421254964676230492982653 157970611753586434868495)
                  ·
                    rfl

theorem cell21_692205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_692205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692205 prefixEnd_692205 := by exact prefixLift 692205
  have htrace : WordTrace (prefixWord ++ tailWord_692205) baseStart_692205 baseEnd_692205 := by
    simpa [prefixWord, tailWord_692205, baseEnd_692205] using wordTrace_append hprefix tailTrace_692205
  have hstable : (prefixWord ++ tailWord_692205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692205).length < 2 ^ (prefixWord ++ tailWord_692205).sum := by decide
  have hdescent : baseEnd_692205 < baseStart_692205 := by decide
  rcases family_descends (prefixWord ++ tailWord_692205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692247 : List Nat := [1, 1, 3, 5, 2, 1, 2, 3, 3]
def baseStart_692247 : Nat := 118140960795 + 692247 * 2 ^ 59
def prefixEnd_692247 : Nat := 4983230072969 + 3 ^ 40 * 692247 * 2
def baseEnd_692247 : Nat := 157980196725803695168409

theorem tailTrace_692247 : CollatzResearch.WordTrace tailWord_692247 prefixEnd_692247 157980196725803695168409 := by
  unfold tailWord_692247
  simp only [CollatzResearch.WordTrace]
  refine ⟨25248322323114820220226995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16832214882076546813484663 25248322323114820220226995)
  ·
    refine ⟨37872483484672230330340493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25248322323114820220226995 37872483484672230330340493)
    ·
      refine ⟨14202181306752086373877685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37872483484672230330340493 14202181306752086373877685)
      ·
        refine ⟨1331454497508008097551033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14202181306752086373877685 1331454497508008097551033)
        ·
          refine ⟨998590873131006073163275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1331454497508008097551033 998590873131006073163275)
          ·
            refine ⟨1497886309696509109744913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998590873131006073163275 1497886309696509109744913)
            ·
              refine ⟨1123414732272381832308685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1497886309696509109744913 1123414732272381832308685)
              ·
                refine ⟨421280524602143187115757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1123414732272381832308685 421280524602143187115757)
                ·
                  refine ⟨157980196725803695168409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421280524602143187115757 157980196725803695168409)
                  ·
                    rfl

theorem cell21_692247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 3].length) (baseStart_692247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692247 prefixEnd_692247 := by exact prefixLift 692247
  have htrace : WordTrace (prefixWord ++ tailWord_692247) baseStart_692247 baseEnd_692247 := by
    simpa [prefixWord, tailWord_692247, baseEnd_692247] using wordTrace_append hprefix tailTrace_692247
  have hstable : (prefixWord ++ tailWord_692247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692247).length < 2 ^ (prefixWord ++ tailWord_692247).sum := by decide
  have hdescent : baseEnd_692247 < baseStart_692247 := by decide
  rcases family_descends (prefixWord ++ tailWord_692247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692272 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_692272 : Nat := 118140960795 + 692272 * 2 ^ 59
def prefixEnd_692272 : Nat := 4983230072969 + 3 ^ 40 * 692272 * 2
def baseEnd_692272 : Nat := 157985902066409207251691

theorem tailTrace_692272 : CollatzResearch.WordTrace tailWord_692272 prefixEnd_692272 157985902066409207251691 := by
  unfold tailWord_692272
  simp only [CollatzResearch.WordTrace]
  refine ⟨12624617074012124744943535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16832822765349499659924713 12624617074012124744943535)
  ·
    refine ⟨18936925611018187117415303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12624617074012124744943535 18936925611018187117415303)
    ·
      refine ⟨28405388416527280676122955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18936925611018187117415303 28405388416527280676122955)
      ·
        refine ⟨42608082624790921014184433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28405388416527280676122955 42608082624790921014184433)
        ·
          refine ⟨31956061968593190760638325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42608082624790921014184433 31956061968593190760638325)
          ·
            refine ⟨2995880809555611633809843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31956061968593190760638325 2995880809555611633809843)
            ·
              refine ⟨4493821214333417450714765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995880809555611633809843 4493821214333417450714765)
              ·
                refine ⟨1685182955375031544018037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4493821214333417450714765 1685182955375031544018037)
                ·
                  refine ⟨157985902066409207251691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1685182955375031544018037 157985902066409207251691)
                  ·
                    rfl

theorem cell21_692272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_692272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692272 prefixEnd_692272 := by exact prefixLift 692272
  have htrace : WordTrace (prefixWord ++ tailWord_692272) baseStart_692272 baseEnd_692272 := by
    simpa [prefixWord, tailWord_692272, baseEnd_692272] using wordTrace_append hprefix tailTrace_692272
  have hstable : (prefixWord ++ tailWord_692272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692272).length < 2 ^ (prefixWord ++ tailWord_692272).sum := by decide
  have hdescent : baseEnd_692272 < baseStart_692272 := by decide
  rcases family_descends (prefixWord ++ tailWord_692272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692289 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 5]
def baseStart_692289 : Nat := 118140960795 + 692289 * 2 ^ 59
def prefixEnd_692289 : Nat := 4983230072969 + 3 ^ 40 * 692289 * 2
def baseEnd_692289 : Nat := 157989781698020955468323

theorem tailTrace_692289 : CollatzResearch.WordTrace tailWord_692289 prefixEnd_692289 157989781698020955468323 := by
  unfold tailWord_692289
  simp only [CollatzResearch.WordTrace]
  refine ⟨25249854188962661393255921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16833236125975107595503947 25249854188962661393255921)
  ·
    refine ⟨18937390641721996044941941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25249854188962661393255921 18937390641721996044941941)
    ·
      refine ⟨1775380372661437129213307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18937390641721996044941941 1775380372661437129213307)
      ·
        refine ⟨2663070558992155693819961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775380372661437129213307 2663070558992155693819961)
        ·
          refine ⟨1997302919244116770364971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2663070558992155693819961 1997302919244116770364971)
          ·
            refine ⟨2995954378866175155547457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997302919244116770364971 2995954378866175155547457)
            ·
              refine ⟨2246965784149631366660593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2995954378866175155547457 2246965784149631366660593)
              ·
                refine ⟨1685224338112223524995445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2246965784149631366660593 1685224338112223524995445)
                ·
                  refine ⟨157989781698020955468323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1685224338112223524995445 157989781698020955468323)
                  ·
                    rfl

theorem cell21_692289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_692289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692289 prefixEnd_692289 := by exact prefixLift 692289
  have htrace : WordTrace (prefixWord ++ tailWord_692289) baseStart_692289 baseEnd_692289 := by
    simpa [prefixWord, tailWord_692289, baseEnd_692289] using wordTrace_append hprefix tailTrace_692289
  have hstable : (prefixWord ++ tailWord_692289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692289).length < 2 ^ (prefixWord ++ tailWord_692289).sum := by decide
  have hdescent : baseEnd_692289 < baseStart_692289 := by decide
  rcases family_descends (prefixWord ++ tailWord_692289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692334 : List Nat := [4, 1, 2, 2, 1, 1, 4, 6]
def baseStart_692334 : Nat := 118140960795 + 692334 * 2 ^ 59
def prefixEnd_692334 : Nat := 4983230072969 + 3 ^ 40 * 692334 * 2
def baseEnd_692334 : Nat := 52666683770370292406077

theorem tailTrace_692334 : CollatzResearch.WordTrace tailWord_692334 prefixEnd_692334 52666683770370292406077 := by
  unfold tailWord_692334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3156436934224954259830507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16834330315866422719096037 3156436934224954259830507)
  ·
    refine ⟨4734655401337431389745761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3156436934224954259830507 4734655401337431389745761)
    ·
      refine ⟨3550991551003073542309321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4734655401337431389745761 3550991551003073542309321)
      ·
        refine ⟨2663243663252305156731991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3550991551003073542309321 2663243663252305156731991)
        ·
          refine ⟨3994865494878457735097987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2663243663252305156731991 3994865494878457735097987)
          ·
            refine ⟨5992298242317686602646981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994865494878457735097987 5992298242317686602646981)
            ·
              refine ⟨1123555920434566237996309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5992298242317686602646981 1123555920434566237996309)
              ·
                refine ⟨52666683770370292406077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1123555920434566237996309 52666683770370292406077)
                ·
                  rfl

theorem cell21_692334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_692334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692334 prefixEnd_692334 := by exact prefixLift 692334
  have htrace : WordTrace (prefixWord ++ tailWord_692334) baseStart_692334 baseEnd_692334 := by
    simpa [prefixWord, tailWord_692334, baseEnd_692334] using wordTrace_append hprefix tailTrace_692334
  have hstable : (prefixWord ++ tailWord_692334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692334).length < 2 ^ (prefixWord ++ tailWord_692334).sum := by decide
  have hdescent : baseEnd_692334 < baseStart_692334 := by decide
  rcases family_descends (prefixWord ++ tailWord_692334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692374 : List Nat := [5, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_692374 : Nat := 118140960795 + 692374 * 2 ^ 59
def prefixEnd_692374 : Nat := 4983230072969 + 3 ^ 40 * 692374 * 2
def baseEnd_692374 : Nat := 158009179856079696551483

theorem tailTrace_692374 : CollatzResearch.WordTrace tailWord_692374 prefixEnd_692374 158009179856079696551483 := by
  unfold tailWord_692374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578309649603420056881261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16835302929103147273400117 1578309649603420056881261)
  ·
    refine ⟨591866118601282521330473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1578309649603420056881261 591866118601282521330473)
    ·
      refine ⟨443899588950961890997855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 591866118601282521330473 443899588950961890997855)
      ·
        refine ⟨665849383426442836496783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443899588950961890997855 665849383426442836496783)
        ·
          refine ⟨998774075139664254745175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665849383426442836496783 998774075139664254745175)
          ·
            refine ⟨1498161112709496382117763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998774075139664254745175 1498161112709496382117763)
            ·
              refine ⟨2247241669064244573176645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498161112709496382117763 2247241669064244573176645)
              ·
                refine ⟨421357812949545857470621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2247241669064244573176645 421357812949545857470621)
                ·
                  refine ⟨158009179856079696551483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421357812949545857470621 158009179856079696551483)
                  ·
                    rfl

theorem cell21_692374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_692374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692374 prefixEnd_692374 := by exact prefixLift 692374
  have htrace : WordTrace (prefixWord ++ tailWord_692374) baseStart_692374 baseEnd_692374 := by
    simpa [prefixWord, tailWord_692374, baseEnd_692374] using wordTrace_append hprefix tailTrace_692374
  have hstable : (prefixWord ++ tailWord_692374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692374).length < 2 ^ (prefixWord ++ tailWord_692374).sum := by decide
  have hdescent : baseEnd_692374 < baseStart_692374 := by decide
  rcases family_descends (prefixWord ++ tailWord_692374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692441 : List Nat := [1, 2, 1, 2, 3, 1, 4, 4, 3]
def baseStart_692441 : Nat := 118140960795 + 692441 * 2 ^ 59
def prefixEnd_692441 : Nat := 4983230072969 + 3 ^ 40 * 692441 * 2
def baseEnd_692441 : Nat := 158024470168902468934679

theorem tailTrace_692441 : CollatzResearch.WordTrace tailWord_692441 prefixEnd_692441 158024470168902468934679 := by
  unfold tailWord_692441
  simp only [CollatzResearch.WordTrace]
  refine ⟨25255398084411991352789177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16836932056274660901859451 25255398084411991352789177)
  ·
    refine ⟨18941548563308993514591883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25255398084411991352789177 18941548563308993514591883)
    ·
      refine ⟨28412322844963490271887825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18941548563308993514591883 28412322844963490271887825)
      ·
        refine ⟨21309242133722617703915869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28412322844963490271887825 21309242133722617703915869)
        ·
          refine ⟨7990965800145981638968451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21309242133722617703915869 7990965800145981638968451)
          ·
            refine ⟨11986448700218972458452677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7990965800145981638968451 11986448700218972458452677)
            ·
              refine ⟨2247459131291057335959877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11986448700218972458452677 2247459131291057335959877)
              ·
                refine ⟨421398587117073250492477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2247459131291057335959877 421398587117073250492477)
                ·
                  refine ⟨158024470168902468934679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421398587117073250492477 158024470168902468934679)
                  ·
                    rfl

theorem cell21_692441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 3].length) (baseStart_692441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692441 prefixEnd_692441 := by exact prefixLift 692441
  have htrace : WordTrace (prefixWord ++ tailWord_692441) baseStart_692441 baseEnd_692441 := by
    simpa [prefixWord, tailWord_692441, baseEnd_692441] using wordTrace_append hprefix tailTrace_692441
  have hstable : (prefixWord ++ tailWord_692441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692441).length < 2 ^ (prefixWord ++ tailWord_692441).sum := by decide
  have hdescent : baseEnd_692441 < baseStart_692441 := by decide
  rcases family_descends (prefixWord ++ tailWord_692441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692506 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 4]
def baseStart_692506 : Nat := 118140960795 + 692506 * 2 ^ 59
def prefixEnd_692506 : Nat := 4983230072969 + 3 ^ 40 * 692506 * 2
def baseEnd_692506 : Nat := 158039304054476800351213

theorem tailTrace_692506 : CollatzResearch.WordTrace tailWord_692506 prefixEnd_692506 158039304054476800351213 := by
  unfold tailWord_692506
  simp only [CollatzResearch.WordTrace]
  refine ⟨6314442207294126863476343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16838512552784338302603581 6314442207294126863476343)
  ·
    refine ⟨9471663310941190295214515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6314442207294126863476343 9471663310941190295214515)
    ·
      refine ⟨14207494966411785442821773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9471663310941190295214515 14207494966411785442821773)
      ·
        refine ⟨5327810612404419541058165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14207494966411785442821773 5327810612404419541058165)
        ·
          refine ⟨499482244912914331974203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5327810612404419541058165 499482244912914331974203)
          ·
            refine ⟨749223367369371497961305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499482244912914331974203 749223367369371497961305)
            ·
              refine ⟨561917525527028623470979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749223367369371497961305 561917525527028623470979)
              ·
                refine ⟨842876288290542935206469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561917525527028623470979 842876288290542935206469)
                ·
                  refine ⟨158039304054476800351213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 842876288290542935206469 158039304054476800351213)
                  ·
                    rfl

theorem cell21_692506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_692506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692506 prefixEnd_692506 := by exact prefixLift 692506
  have htrace : WordTrace (prefixWord ++ tailWord_692506) baseStart_692506 baseEnd_692506 := by
    simpa [prefixWord, tailWord_692506, baseEnd_692506] using wordTrace_append hprefix tailTrace_692506
  have hstable : (prefixWord ++ tailWord_692506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692506).length < 2 ^ (prefixWord ++ tailWord_692506).sum := by decide
  have hdescent : baseEnd_692506 < baseStart_692506 := by decide
  rcases family_descends (prefixWord ++ tailWord_692506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692545 : List Nat := [1, 2, 5, 2, 11]
def baseStart_692545 : Nat := 118140960795 + 692545 * 2 ^ 59
def prefixEnd_692545 : Nat := 4983230072969 + 3 ^ 40 * 692545 * 2
def baseEnd_692545 : Nat := 1951212399824955545693

theorem tailTrace_692545 : CollatzResearch.WordTrace tailWord_692545 prefixEnd_692545 1951212399824955545693 := by
  unfold tailWord_692545
  simp only [CollatzResearch.WordTrace]
  refine ⟨25259191276035217114575089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16839460850690144743050059 25259191276035217114575089)
  ·
    refine ⟨18944393457026412835931317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25259191276035217114575089 18944393457026412835931317)
    ·
      refine ⟨1776036886596226203368561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18944393457026412835931317 1776036886596226203368561)
      ·
        refine ⟨1332027664947169652526421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1776036886596226203368561 1332027664947169652526421)
        ·
          refine ⟨1951212399824955545693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1332027664947169652526421 1951212399824955545693)
          ·
            rfl

theorem cell21_692545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 11].length) (baseStart_692545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692545 prefixEnd_692545 := by exact prefixLift 692545
  have htrace : WordTrace (prefixWord ++ tailWord_692545) baseStart_692545 baseEnd_692545 := by
    simpa [prefixWord, tailWord_692545, baseEnd_692545] using wordTrace_append hprefix tailTrace_692545
  have hstable : (prefixWord ++ tailWord_692545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692545).length < 2 ^ (prefixWord ++ tailWord_692545).sum := by decide
  have hdescent : baseEnd_692545 < baseStart_692545 := by decide
  rcases family_descends (prefixWord ++ tailWord_692545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692630 : List Nat := [5, 3, 1, 2, 1, 2, 2, 5]
def baseStart_692630 : Nat := 118140960795 + 692630 * 2 ^ 59
def prefixEnd_692630 : Nat := 4983230072969 + 3 ^ 40 * 692630 * 2
def baseEnd_692630 : Nat := 52689200847960046761431

theorem tailTrace_692630 : CollatzResearch.WordTrace tailWord_692630 prefixEnd_692630 52689200847960046761431 := by
  unfold tailWord_692630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578893217545454789463709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16841527653818184420946229 1578893217545454789463709)
  ·
    refine ⟨592084956579545546048891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1578893217545454789463709 592084956579545546048891)
    ·
      refine ⟨888127434869318319073337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592084956579545546048891 888127434869318319073337)
      ·
        refine ⟨666095576151988739305003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 888127434869318319073337 666095576151988739305003)
        ·
          refine ⟨999143364227983108957505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666095576151988739305003 999143364227983108957505)
          ·
            refine ⟨749357523170987331718129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 999143364227983108957505 749357523170987331718129)
            ·
              refine ⟨562018142378240498788597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749357523170987331718129 562018142378240498788597)
              ·
                refine ⟨52689200847960046761431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 562018142378240498788597 52689200847960046761431)
                ·
                  rfl

theorem cell21_692630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_692630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692630 prefixEnd_692630 := by exact prefixLift 692630
  have htrace : WordTrace (prefixWord ++ tailWord_692630) baseStart_692630 baseEnd_692630 := by
    simpa [prefixWord, tailWord_692630, baseEnd_692630] using wordTrace_append hprefix tailTrace_692630
  have hstable : (prefixWord ++ tailWord_692630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692630).length < 2 ^ (prefixWord ++ tailWord_692630).sum := by decide
  have hdescent : baseEnd_692630 < baseStart_692630 := by decide
  rcases family_descends (prefixWord ++ tailWord_692630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692669 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 5]
def baseStart_692669 : Nat := 118140960795 + 692669 * 2 ^ 59
def prefixEnd_692669 : Nat := 4983230072969 + 3 ^ 40 * 692669 * 2
def baseEnd_692669 : Nat := 158076502875224739134213

theorem tailTrace_692669 : CollatzResearch.WordTrace tailWord_692669 prefixEnd_692669 158076502875224739134213 := by
  unfold tailWord_692669
  simp only [CollatzResearch.WordTrace]
  refine ⟨25263713927585986292089061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16842475951723990861392707 25263713927585986292089061)
  ·
    refine ⟨4736946361422372429766699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25263713927585986292089061 4736946361422372429766699)
    ·
      refine ⟨7105419542133558644650049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4736946361422372429766699 7105419542133558644650049)
      ·
        refine ⟨5329064656600168983487537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7105419542133558644650049 5329064656600168983487537)
        ·
          refine ⟨3996798492450126737615653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5329064656600168983487537 3996798492450126737615653)
          ·
            refine ⟨749399717334398763302935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3996798492450126737615653 749399717334398763302935)
            ·
              refine ⟨1124099576001598144954403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749399717334398763302935 1124099576001598144954403)
              ·
                refine ⟨1686149364002397217431605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124099576001598144954403 1686149364002397217431605)
                ·
                  refine ⟨158076502875224739134213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1686149364002397217431605 158076502875224739134213)
                  ·
                    rfl

theorem cell21_692669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_692669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692669 prefixEnd_692669 := by exact prefixLift 692669
  have htrace : WordTrace (prefixWord ++ tailWord_692669) baseStart_692669 baseEnd_692669 := by
    simpa [prefixWord, tailWord_692669, baseEnd_692669] using wordTrace_append hprefix tailTrace_692669
  have hstable : (prefixWord ++ tailWord_692669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692669).length < 2 ^ (prefixWord ++ tailWord_692669).sum := by decide
  have hdescent : baseEnd_692669 < baseStart_692669 := by decide
  rcases family_descends (prefixWord ++ tailWord_692669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692776 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 4]
def baseStart_692776 : Nat := 118140960795 + 692776 * 2 ^ 59
def prefixEnd_692776 : Nat := 4983230072969 + 3 ^ 40 * 692776 * 2
def baseEnd_692776 : Nat := 158100921733016330850661

theorem tailTrace_692776 : CollatzResearch.WordTrace tailWord_692776 prefixEnd_692776 158100921733016330850661 := by
  unfold tailWord_692776
  simp only [CollatzResearch.WordTrace]
  refine ⟨12633808269099171783117091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16845077692132229044156121 12633808269099171783117091)
  ·
    refine ⟨18950712403648757674675637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12633808269099171783117091 18950712403648757674675637)
    ·
      refine ⟨1776629287842071032000841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18950712403648757674675637 1776629287842071032000841)
      ·
        refine ⟨1332471965881553274000631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1776629287842071032000841 1332471965881553274000631)
        ·
          refine ⟨1998707948822329911000947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332471965881553274000631 1998707948822329911000947)
          ·
            refine ⟨2998061923233494866501421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998707948822329911000947 2998061923233494866501421)
            ·
              refine ⟨1124273221212560574938033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2998061923233494866501421 1124273221212560574938033)
              ·
                refine ⟨843204915909420431203525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124273221212560574938033 843204915909420431203525)
                ·
                  refine ⟨158100921733016330850661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 843204915909420431203525 158100921733016330850661)
                  ·
                    rfl

theorem cell21_692776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_692776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692776 prefixEnd_692776 := by exact prefixLift 692776
  have htrace : WordTrace (prefixWord ++ tailWord_692776) baseStart_692776 baseEnd_692776 := by
    simpa [prefixWord, tailWord_692776, baseEnd_692776] using wordTrace_append hprefix tailTrace_692776
  have hstable : (prefixWord ++ tailWord_692776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692776).length < 2 ^ (prefixWord ++ tailWord_692776).sum := by decide
  have hdescent : baseEnd_692776 < baseStart_692776 := by decide
  rcases family_descends (prefixWord ++ tailWord_692776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692818 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_692818 : Nat := 118140960795 + 692818 * 2 ^ 59
def prefixEnd_692818 : Nat := 4983230072969 + 3 ^ 40 * 692818 * 2
def baseEnd_692818 : Nat := 158110506705233591150575

theorem tailTrace_692818 : CollatzResearch.WordTrace tailWord_692818 prefixEnd_692818 158110506705233591150575 := by
  unfold tailWord_692818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317287101011546184815777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16846098936030789826175405 6317287101011546184815777)
  ·
    refine ⟨4737965325758659638611833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6317287101011546184815777 4737965325758659638611833)
    ·
      refine ⟨3553473994318994728958875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4737965325758659638611833 3553473994318994728958875)
      ·
        refine ⟨5330210991478492093438313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553473994318994728958875 5330210991478492093438313)
        ·
          refine ⟨3997658243608869070078735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5330210991478492093438313 3997658243608869070078735)
          ·
            refine ⟨5996487365413303605118103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997658243608869070078735 5996487365413303605118103)
            ·
              refine ⟨8994731048119955407677155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5996487365413303605118103 8994731048119955407677155)
              ·
                refine ⟨13492096572179933111515733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8994731048119955407677155 13492096572179933111515733)
                ·
                  refine ⟨158110506705233591150575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13492096572179933111515733 158110506705233591150575)
                  ·
                    rfl

theorem cell21_692818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_692818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692818 prefixEnd_692818 := by exact prefixLift 692818
  have htrace : WordTrace (prefixWord ++ tailWord_692818) baseStart_692818 baseEnd_692818 := by
    simpa [prefixWord, tailWord_692818, baseEnd_692818] using wordTrace_append hprefix tailTrace_692818
  have hstable : (prefixWord ++ tailWord_692818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692818).length < 2 ^ (prefixWord ++ tailWord_692818).sum := by decide
  have hdescent : baseEnd_692818 < baseStart_692818 := by decide
  rcases family_descends (prefixWord ++ tailWord_692818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692821 : List Nat := [1, 3, 2, 2, 1, 1, 5, 3, 3]
def baseStart_692821 : Nat := 118140960795 + 692821 * 2 ^ 59
def prefixEnd_692821 : Nat := 4983230072969 + 3 ^ 40 * 692821 * 2
def baseEnd_692821 : Nat := 158111191346106252600569

theorem tailTrace_692821 : CollatzResearch.WordTrace tailWord_692821 prefixEnd_692821 158111191346106252600569 := by
  unfold tailWord_692821
  simp only [CollatzResearch.WordTrace]
  refine ⟨25269257823035316251622317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16846171882023544167748211 25269257823035316251622317)
  ·
    refine ⟨9475971683638243594358369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25269257823035316251622317 9475971683638243594358369)
    ·
      refine ⟨7106978762728682695768777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9475971683638243594358369 7106978762728682695768777)
      ·
        refine ⟨5330234072046512021826583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7106978762728682695768777 5330234072046512021826583)
        ·
          refine ⟨7995351108069768032739875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5330234072046512021826583 7995351108069768032739875)
          ·
            refine ⟨11993026662104652049109813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7995351108069768032739875 11993026662104652049109813)
            ·
              refine ⟨1124346249572311129604045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11993026662104652049109813 1124346249572311129604045)
              ·
                refine ⟨421629843589616673601517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1124346249572311129604045 421629843589616673601517)
                ·
                  refine ⟨158111191346106252600569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421629843589616673601517 158111191346106252600569)
                  ·
                    rfl

theorem cell21_692821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_692821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692821 prefixEnd_692821 := by exact prefixLift 692821
  have htrace : WordTrace (prefixWord ++ tailWord_692821) baseStart_692821 baseEnd_692821 := by
    simpa [prefixWord, tailWord_692821, baseEnd_692821] using wordTrace_append hprefix tailTrace_692821
  have hstable : (prefixWord ++ tailWord_692821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692821).length < 2 ^ (prefixWord ++ tailWord_692821).sum := by decide
  have hdescent : baseEnd_692821 < baseStart_692821 := by decide
  rcases family_descends (prefixWord ++ tailWord_692821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692832 : List Nat := [2, 1, 1, 3, 2, 1, 11]
def baseStart_692832 : Nat := 118140960795 + 692832 * 2 ^ 59
def prefixEnd_692832 : Nat := 4983230072969 + 3 ^ 40 * 692832 * 2
def baseEnd_692832 : Nat := 17568189077330297546357

theorem tailTrace_692832 : CollatzResearch.WordTrace tailWord_692832 prefixEnd_692832 17568189077330297546357 := by
  unfold tailWord_692832
  simp only [CollatzResearch.WordTrace]
  refine ⟨12634829512997732565136375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16846439350663643420181833 12634829512997732565136375)
  ·
    refine ⟨18952244269496598847704563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12634829512997732565136375 18952244269496598847704563)
    ·
      refine ⟨28428366404244898271556845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18952244269496598847704563 28428366404244898271556845)
      ·
        refine ⟨10660637401591836851833817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28428366404244898271556845 10660637401591836851833817)
        ·
          refine ⟨7995478051193877638875363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10660637401591836851833817 7995478051193877638875363)
          ·
            refine ⟨11993217076790816458313045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7995478051193877638875363 11993217076790816458313045)
            ·
              refine ⟨17568189077330297546357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11993217076790816458313045 17568189077330297546357)
              ·
                rfl

theorem cell21_692832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 11].length) (baseStart_692832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692832 prefixEnd_692832 := by exact prefixLift 692832
  have htrace : WordTrace (prefixWord ++ tailWord_692832) baseStart_692832 baseEnd_692832 := by
    simpa [prefixWord, tailWord_692832, baseEnd_692832] using wordTrace_append hprefix tailTrace_692832
  have hstable : (prefixWord ++ tailWord_692832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692832).length < 2 ^ (prefixWord ++ tailWord_692832).sum := by decide
  have hdescent : baseEnd_692832 < baseStart_692832 := by decide
  rcases family_descends (prefixWord ++ tailWord_692832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692984 : List Nat := [2, 1, 2, 1, 1, 2, 5, 7]
def baseStart_692984 : Nat := 118140960795 + 692984 * 2 ^ 59
def prefixEnd_692984 : Nat := 4983230072969 + 3 ^ 40 * 692984 * 2
def baseEnd_692984 : Nat := 52716130055618063794523

theorem tailTrace_692984 : CollatzResearch.WordTrace tailWord_692984 prefixEnd_692984 52716130055618063794523 := by
  unfold tailWord_692984
  simp only [CollatzResearch.WordTrace]
  refine ⟨12637601460722397544903003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16850135280963196726537337 12637601460722397544903003)
  ·
    refine ⟨18956402191083596317354505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12637601460722397544903003 18956402191083596317354505)
    ·
      refine ⟨14217301643312697238015879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18956402191083596317354505 14217301643312697238015879)
      ·
        refine ⟨21325952464969045857023819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14217301643312697238015879 21325952464969045857023819)
        ·
          refine ⟨31988928697453568785535729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21325952464969045857023819 31988928697453568785535729)
          ·
            refine ⟨23991696523090176589151797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31988928697453568785535729 23991696523090176589151797)
            ·
              refine ⟨2249221549039704055232981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23991696523090176589151797 2249221549039704055232981)
              ·
                refine ⟨52716130055618063794523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2249221549039704055232981 52716130055618063794523)
                ·
                  rfl

theorem cell21_692984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_692984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692984 prefixEnd_692984 := by exact prefixLift 692984
  have htrace : WordTrace (prefixWord ++ tailWord_692984) baseStart_692984 baseEnd_692984 := by
    simpa [prefixWord, tailWord_692984, baseEnd_692984] using wordTrace_append hprefix tailTrace_692984
  have hstable : (prefixWord ++ tailWord_692984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692984).length < 2 ^ (prefixWord ++ tailWord_692984).sum := by decide
  have hdescent : baseEnd_692984 < baseStart_692984 := by decide
  rcases family_descends (prefixWord ++ tailWord_692984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_692990 : List Nat := [4, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_692990 : Nat := 118140960795 + 692990 * 2 ^ 59
def prefixEnd_692990 : Nat := 4983230072969 + 3 ^ 40 * 692990 * 2
def baseEnd_692990 : Nat := 158149759448599514283557

theorem tailTrace_692990 : CollatzResearch.WordTrace tailWord_692990 prefixEnd_692990 158149759448599514283557 := by
  unfold tailWord_692990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3159427719927882264315553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16850281172948705409682949 3159427719927882264315553)
  ·
    refine ⟨2369570789945911698236665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3159427719927882264315553 2369570789945911698236665)
    ·
      refine ⟨1777178092459433773677499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2369570789945911698236665 1777178092459433773677499)
      ·
        refine ⟨2665767138689150660516249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1777178092459433773677499 2665767138689150660516249)
        ·
          refine ⟨1999325354016862995387187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2665767138689150660516249 1999325354016862995387187)
          ·
            refine ⟨2998988031025294493080781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999325354016862995387187 2998988031025294493080781)
            ·
              refine ⟨1124620511634485434905293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2998988031025294493080781 1124620511634485434905293)
              ·
                refine ⟨421732691862932038089485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1124620511634485434905293 421732691862932038089485)
                ·
                  refine ⟨158149759448599514283557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421732691862932038089485 158149759448599514283557)
                  ·
                    rfl

theorem cell21_692990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_692990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_692990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_692990 prefixEnd_692990 := by exact prefixLift 692990
  have htrace : WordTrace (prefixWord ++ tailWord_692990) baseStart_692990 baseEnd_692990 := by
    simpa [prefixWord, tailWord_692990, baseEnd_692990] using wordTrace_append hprefix tailTrace_692990
  have hstable : (prefixWord ++ tailWord_692990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_692990).length < 2 ^ (prefixWord ++ tailWord_692990).sum := by decide
  have hdescent : baseEnd_692990 < baseStart_692990 := by decide
  rcases family_descends (prefixWord ++ tailWord_692990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693091 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 7]
def baseStart_693091 : Nat := 118140960795 + 693091 * 2 ^ 59
def prefixEnd_693091 : Nat := 4983230072969 + 3 ^ 40 * 693091 * 2
def baseEnd_693091 : Nat := 158172809024645783100017

theorem tailTrace_693091 : CollatzResearch.WordTrace tailWord_693091 prefixEnd_693091 158172809024645783100017 := by
  unfold tailWord_693091
  simp only [CollatzResearch.WordTrace]
  refine ⟨25279105532057152363951127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16852737021371434909300751 25279105532057152363951127)
  ·
    refine ⟨37918658298085728545926691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25279105532057152363951127 37918658298085728545926691)
    ·
      refine ⟨56877987447128592818890037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37918658298085728545926691 56877987447128592818890037)
      ·
        refine ⟨5332311323168305576770941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56877987447128592818890037 5332311323168305576770941)
        ·
          refine ⟨1999616746188114591289103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5332311323168305576770941 1999616746188114591289103)
          ·
            refine ⟨2999425119282171886933655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999616746188114591289103 2999425119282171886933655)
            ·
              refine ⟨4499137678923257830400483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999425119282171886933655 4499137678923257830400483)
              ·
                refine ⟨6748706518384886745600725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499137678923257830400483 6748706518384886745600725)
                ·
                  refine ⟨158172809024645783100017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6748706518384886745600725 158172809024645783100017)
                  ·
                    rfl

theorem cell21_693091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_693091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693091 prefixEnd_693091 := by exact prefixLift 693091
  have htrace : WordTrace (prefixWord ++ tailWord_693091) baseStart_693091 baseEnd_693091 := by
    simpa [prefixWord, tailWord_693091, baseEnd_693091] using wordTrace_append hprefix tailTrace_693091
  have hstable : (prefixWord ++ tailWord_693091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693091).length < 2 ^ (prefixWord ++ tailWord_693091).sum := by decide
  have hdescent : baseEnd_693091 < baseStart_693091 := by decide
  rcases family_descends (prefixWord ++ tailWord_693091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693142 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_693142 : Nat := 118140960795 + 693142 * 2 ^ 59
def prefixEnd_693142 : Nat := 4983230072969 + 3 ^ 40 * 693142 * 2
def baseEnd_693142 : Nat := 158184447919481027749913

theorem tailTrace_693142 : CollatzResearch.WordTrace tailWord_693142 prefixEnd_693142 158184447919481027749913 := by
  unfold tailWord_693142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1580060353429524254628605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16853977103248258716038453 1580060353429524254628605)
  ·
    refine ⟨592522632536071595485727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1580060353429524254628605 592522632536071595485727)
    ·
      refine ⟨888783948804107393228591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592522632536071595485727 888783948804107393228591)
      ·
        refine ⟨1333175923206161089842887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888783948804107393228591 1333175923206161089842887)
        ·
          refine ⟨1999763884809241634764331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1333175923206161089842887 1999763884809241634764331)
          ·
            refine ⟨2999645827213862452146497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999763884809241634764331 2999645827213862452146497)
            ·
              refine ⟨2249734370410396839109873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2999645827213862452146497 2249734370410396839109873)
              ·
                refine ⟨1687300777807797629332405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2249734370410396839109873 1687300777807797629332405)
                ·
                  refine ⟨158184447919481027749913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1687300777807797629332405 158184447919481027749913)
                  ·
                    rfl

theorem cell21_693142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_693142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693142 prefixEnd_693142 := by exact prefixLift 693142
  have htrace : WordTrace (prefixWord ++ tailWord_693142) baseStart_693142 baseEnd_693142 := by
    simpa [prefixWord, tailWord_693142, baseEnd_693142] using wordTrace_append hprefix tailTrace_693142
  have hstable : (prefixWord ++ tailWord_693142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693142).length < 2 ^ (prefixWord ++ tailWord_693142).sum := by decide
  have hdescent : baseEnd_693142 < baseStart_693142 := by decide
  rcases family_descends (prefixWord ++ tailWord_693142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693153 : List Nat := [1, 2, 3, 4, 1, 2, 1, 7]
def baseStart_693153 : Nat := 118140960795 + 693153 * 2 ^ 59
def prefixEnd_693153 : Nat := 4983230072969 + 3 ^ 40 * 693153 * 2
def baseEnd_693153 : Nat := 52728986089782484355519

theorem tailTrace_693153 : CollatzResearch.WordTrace tailWord_693153 prefixEnd_693153 52728986089782484355519 := by
  unfold tailWord_693153
  simp only [CollatzResearch.WordTrace]
  refine ⟨25281366857832536952708113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16854244571888357968472075 25281366857832536952708113)
  ·
    refine ⟨18961025143374402714531085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25281366857832536952708113 18961025143374402714531085)
    ·
      refine ⟨7110384428765401017949157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18961025143374402714531085 7110384428765401017949157)
      ·
        refine ⟨1333197080393512690865467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7110384428765401017949157 1333197080393512690865467)
        ·
          refine ⟨1999795620590269036298201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1333197080393512690865467 1999795620590269036298201)
          ·
            refine ⟨1499846715442701777223651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1999795620590269036298201 1499846715442701777223651)
            ·
              refine ⟨2249770073164052665835477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499846715442701777223651 2249770073164052665835477)
              ·
                refine ⟨52728986089782484355519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2249770073164052665835477 52728986089782484355519)
                ·
                  rfl

theorem cell21_693153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 7].length) (baseStart_693153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693153 prefixEnd_693153 := by exact prefixLift 693153
  have htrace : WordTrace (prefixWord ++ tailWord_693153) baseStart_693153 baseEnd_693153 := by
    simpa [prefixWord, tailWord_693153, baseEnd_693153] using wordTrace_append hprefix tailTrace_693153
  have hstable : (prefixWord ++ tailWord_693153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693153).length < 2 ^ (prefixWord ++ tailWord_693153).sum := by decide
  have hdescent : baseEnd_693153 < baseStart_693153 := by decide
  rcases family_descends (prefixWord ++ tailWord_693153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693159 : List Nat := [1, 1, 6, 1, 4, 1, 1, 3, 3]
def baseStart_693159 : Nat := 118140960795 + 693159 * 2 ^ 59
def prefixEnd_693159 : Nat := 4983230072969 + 3 ^ 40 * 693159 * 2
def baseEnd_693159 : Nat := 158188327551092775966545

theorem tailTrace_693159 : CollatzResearch.WordTrace tailWord_693159 prefixEnd_693159 158188327551092775966545 := by
  unfold tailWord_693159
  simp only [CollatzResearch.WordTrace]
  refine ⟨25281585695810799977426531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16854390463873866651617687 25281585695810799977426531)
  ·
    refine ⟨37922378543716199966139797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25281585695810799977426531 37922378543716199966139797)
    ·
      refine ⟨1777611494236696873412803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37922378543716199966139797 1777611494236696873412803)
      ·
        refine ⟨2666417241355045310119205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1777611494236696873412803 2666417241355045310119205)
        ·
          refine ⟨499953232754070995647351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2666417241355045310119205 499953232754070995647351)
          ·
            refine ⟨749929849131106493471027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499953232754070995647351 749929849131106493471027)
            ·
              refine ⟨1124894773696659740206541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749929849131106493471027 1124894773696659740206541)
              ·
                refine ⟨421835540136247402577453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1124894773696659740206541 421835540136247402577453)
                ·
                  refine ⟨158188327551092775966545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421835540136247402577453 158188327551092775966545)
                  ·
                    rfl

theorem cell21_693159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 3].length) (baseStart_693159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693159 prefixEnd_693159 := by exact prefixLift 693159
  have htrace : WordTrace (prefixWord ++ tailWord_693159) baseStart_693159 baseEnd_693159 := by
    simpa [prefixWord, tailWord_693159, baseEnd_693159] using wordTrace_append hprefix tailTrace_693159
  have hstable : (prefixWord ++ tailWord_693159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693159).length < 2 ^ (prefixWord ++ tailWord_693159).sum := by decide
  have hdescent : baseEnd_693159 < baseStart_693159 := by decide
  rcases family_descends (prefixWord ++ tailWord_693159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693184 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 5]
def baseStart_693184 : Nat := 118140960795 + 693184 * 2 ^ 59
def prefixEnd_693184 : Nat := 4983230072969 + 3 ^ 40 * 693184 * 2
def baseEnd_693184 : Nat := 158194032891698288049827

theorem tailTrace_693184 : CollatzResearch.WordTrace tailWord_693184 prefixEnd_693184 158194032891698288049827 := by
  unfold tailWord_693184
  simp only [CollatzResearch.WordTrace]
  refine ⟨12641248760360114623543303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16854998347146819498057737 12641248760360114623543303)
  ·
    refine ⟨18961873140540171935314955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12641248760360114623543303 18961873140540171935314955)
    ·
      refine ⟨28442809710810257902972433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18961873140540171935314955 28442809710810257902972433)
      ·
        refine ⟨21332107283107693427229325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28442809710810257902972433 21332107283107693427229325)
        ·
          refine ⟨7999540231165385035210997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21332107283107693427229325 7999540231165385035210997)
          ·
            refine ⟨749956896671754847051031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7999540231165385035210997 749956896671754847051031)
            ·
              refine ⟨1124935345007632270576547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749956896671754847051031 1124935345007632270576547)
              ·
                refine ⟨1687403017511448405864821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1124935345007632270576547 1687403017511448405864821)
                ·
                  refine ⟨158194032891698288049827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1687403017511448405864821 158194032891698288049827)
                  ·
                    rfl

theorem cell21_693184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_693184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693184 prefixEnd_693184 := by exact prefixLift 693184
  have htrace : WordTrace (prefixWord ++ tailWord_693184) baseStart_693184 baseEnd_693184 := by
    simpa [prefixWord, tailWord_693184, baseEnd_693184] using wordTrace_append hprefix tailTrace_693184
  have hstable : (prefixWord ++ tailWord_693184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693184).length < 2 ^ (prefixWord ++ tailWord_693184).sum := by decide
  have hdescent : baseEnd_693184 < baseStart_693184 := by decide
  rcases family_descends (prefixWord ++ tailWord_693184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693319 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 5]
def baseStart_693319 : Nat := 118140960795 + 693319 * 2 ^ 59
def prefixEnd_693319 : Nat := 4983230072969 + 3 ^ 40 * 693319 * 2
def baseEnd_693319 : Nat := 158224841730968053299551

theorem tailTrace_693319 : CollatzResearch.WordTrace tailWord_693319 prefixEnd_693319 158224841730968053299551 := by
  unfold tailWord_693319
  simp only [CollatzResearch.WordTrace]
  refine ⟨25287421375231147303251011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16858280916820764868834007 25287421375231147303251011)
  ·
    refine ⟨37931132062846720954876517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25287421375231147303251011 37931132062846720954876517)
    ·
      refine ⟨7112087261783760179039347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37931132062846720954876517 7112087261783760179039347)
      ·
        refine ⟨10668130892675640268559021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7112087261783760179039347 10668130892675640268559021)
        ·
          refine ⟨4000549084753365100709633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10668130892675640268559021 4000549084753365100709633)
          ·
            refine ⟨3000411813565023825532225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4000549084753365100709633 3000411813565023825532225)
            ·
              refine ⟨2250308860173767869149169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000411813565023825532225 2250308860173767869149169)
              ·
                refine ⟨1687731645130325901861877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250308860173767869149169 1687731645130325901861877)
                ·
                  refine ⟨158224841730968053299551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1687731645130325901861877 158224841730968053299551)
                  ·
                    rfl

theorem cell21_693319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_693319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693319 prefixEnd_693319 := by exact prefixLift 693319
  have htrace : WordTrace (prefixWord ++ tailWord_693319) baseStart_693319 baseEnd_693319 := by
    simpa [prefixWord, tailWord_693319, baseEnd_693319] using wordTrace_append hprefix tailTrace_693319
  have hstable : (prefixWord ++ tailWord_693319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693319).length < 2 ^ (prefixWord ++ tailWord_693319).sum := by decide
  have hdescent : baseEnd_693319 < baseStart_693319 := by decide
  rcases family_descends (prefixWord ++ tailWord_693319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693333 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 8]
def baseStart_693333 : Nat := 118140960795 + 693333 * 2 ^ 59
def prefixEnd_693333 : Nat := 4983230072969 + 3 ^ 40 * 693333 * 2
def baseEnd_693333 : Nat := 158228036721707140066189

theorem tailTrace_693333 : CollatzResearch.WordTrace tailWord_693333 prefixEnd_693333 158228036721707140066189 := by
  unfold tailWord_693333
  simp only [CollatzResearch.WordTrace]
  refine ⟨25287931997180427694260653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16858621331453618462840435 25287931997180427694260653)
  ·
    refine ⟨9482974498942660385347745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25287931997180427694260653 9482974498942660385347745)
    ·
      refine ⟨7112230874206995289010809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9482974498942660385347745 7112230874206995289010809)
      ·
        refine ⟨5334173155655246466758107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7112230874206995289010809 5334173155655246466758107)
        ·
          refine ⟨8001259733482869700137161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5334173155655246466758107 8001259733482869700137161)
          ·
            refine ⟨6000944800112152275102871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8001259733482869700137161 6000944800112152275102871)
            ·
              refine ⟨9001417200168228412654307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6000944800112152275102871 9001417200168228412654307)
              ·
                refine ⟨13502125800252342618981461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9001417200168228412654307 13502125800252342618981461)
                ·
                  refine ⟨158228036721707140066189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13502125800252342618981461 158228036721707140066189)
                  ·
                    rfl

theorem cell21_693333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_693333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693333 prefixEnd_693333 := by exact prefixLift 693333
  have htrace : WordTrace (prefixWord ++ tailWord_693333) baseStart_693333 baseEnd_693333 := by
    simpa [prefixWord, tailWord_693333, baseEnd_693333] using wordTrace_append hprefix tailTrace_693333
  have hstable : (prefixWord ++ tailWord_693333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693333).length < 2 ^ (prefixWord ++ tailWord_693333).sum := by decide
  have hdescent : baseEnd_693333 < baseStart_693333 := by decide
  rcases family_descends (prefixWord ++ tailWord_693333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693353 : List Nat := [1, 2, 1, 1, 1, 7, 3, 2, 3]
def baseStart_693353 : Nat := 118140960795 + 693353 * 2 ^ 59
def prefixEnd_693353 : Nat := 4983230072969 + 3 ^ 40 * 693353 * 2
def baseEnd_693353 : Nat := 158232600994191549732815

theorem tailTrace_693353 : CollatzResearch.WordTrace tailWord_693353 prefixEnd_693353 158232600994191549732815 := by
  unfold tailWord_693353
  simp only [CollatzResearch.WordTrace]
  refine ⟨25288661457107971109988713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16859107638071980739992475 25288661457107971109988713)
  ·
    refine ⟨18966496092830978332491535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25288661457107971109988713 18966496092830978332491535)
    ·
      refine ⟨28449744139246467498737303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18966496092830978332491535 28449744139246467498737303)
      ·
        refine ⟨42674616208869701248105955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28449744139246467498737303 42674616208869701248105955)
        ·
          refine ⟨64011924313304551872158933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42674616208869701248105955 64011924313304551872158933)
          ·
            refine ⟨1500279476093075434503725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 64011924313304551872158933 1500279476093075434503725)
            ·
              refine ⟨562604803534903287938897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1500279476093075434503725 562604803534903287938897)
              ·
                refine ⟨421953602651177465954173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562604803534903287938897 421953602651177465954173)
                ·
                  refine ⟨158232600994191549732815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421953602651177465954173 158232600994191549732815)
                  ·
                    rfl

theorem cell21_693353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 3].length) (baseStart_693353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693353 prefixEnd_693353 := by exact prefixLift 693353
  have htrace : WordTrace (prefixWord ++ tailWord_693353) baseStart_693353 baseEnd_693353 := by
    simpa [prefixWord, tailWord_693353, baseEnd_693353] using wordTrace_append hprefix tailTrace_693353
  have hstable : (prefixWord ++ tailWord_693353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693353).length < 2 ^ (prefixWord ++ tailWord_693353).sum := by decide
  have hdescent : baseEnd_693353 < baseStart_693353 := by decide
  rcases family_descends (prefixWord ++ tailWord_693353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693398 : List Nat := [5, 3, 2, 11]
def baseStart_693398 : Nat := 118140960795 + 693398 * 2 ^ 59
def prefixEnd_693398 : Nat := 4983230072969 + 3 ^ 40 * 693398 * 2
def baseEnd_693398 : Nat := 651205228836549265361

theorem tailTrace_693398 : CollatzResearch.WordTrace tailWord_693398 prefixEnd_693398 651205228836549265361 := by
  unfold tailWord_693398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1580643921371558987211053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16860201827963295863584565 1580643921371558987211053)
  ·
    refine ⟨592741470514334620204145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1580643921371558987211053 592741470514334620204145)
    ·
      refine ⟨444556102885750965153109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 592741470514334620204145 444556102885750965153109)
      ·
        refine ⟨651205228836549265361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 444556102885750965153109 651205228836549265361)
        ·
          rfl

theorem cell21_693398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 11].length) (baseStart_693398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693398 prefixEnd_693398 := by exact prefixLift 693398
  have htrace : WordTrace (prefixWord ++ tailWord_693398) baseStart_693398 baseEnd_693398 := by
    simpa [prefixWord, tailWord_693398, baseEnd_693398] using wordTrace_append hprefix tailTrace_693398
  have hstable : (prefixWord ++ tailWord_693398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693398).length < 2 ^ (prefixWord ++ tailWord_693398).sum := by decide
  have hdescent : baseEnd_693398 < baseStart_693398 := by decide
  rcases family_descends (prefixWord ++ tailWord_693398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693426 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_693426 : Nat := 118140960795 + 693426 * 2 ^ 59
def prefixEnd_693426 : Nat := 4983230072969 + 3 ^ 40 * 693426 * 2
def baseEnd_693426 : Nat := 158249260588759645015999

theorem tailTrace_693426 : CollatzResearch.WordTrace tailWord_693426 prefixEnd_693426 158249260588759645015999 := by
  unfold tailWord_693426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6322830996460876144349033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16860882657229003051597421 6322830996460876144349033)
  ·
    refine ⟨4742123247345657108261775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6322830996460876144349033 4742123247345657108261775)
    ·
      refine ⟨7113184871018485662392663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4742123247345657108261775 7113184871018485662392663)
      ·
        refine ⟨10669777306527728493588995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7113184871018485662392663 10669777306527728493588995)
        ·
          refine ⟨16004665959791592740383493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10669777306527728493588995 16004665959791592740383493)
          ·
            refine ⟨3000874867460923638821905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16004665959791592740383493 3000874867460923638821905)
            ·
              refine ⟨2250656150595692729116429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000874867460923638821905 2250656150595692729116429)
              ·
                refine ⟨843996056473384773418661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2250656150595692729116429 843996056473384773418661)
                ·
                  refine ⟨158249260588759645015999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 843996056473384773418661 158249260588759645015999)
                  ·
                    rfl

theorem cell21_693426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_693426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693426 prefixEnd_693426 := by exact prefixLift 693426
  have htrace : WordTrace (prefixWord ++ tailWord_693426) baseStart_693426 baseEnd_693426 := by
    simpa [prefixWord, tailWord_693426, baseEnd_693426] using wordTrace_append hprefix tailTrace_693426
  have hstable : (prefixWord ++ tailWord_693426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693426).length < 2 ^ (prefixWord ++ tailWord_693426).sum := by decide
  have hdescent : baseEnd_693426 < baseStart_693426 := by decide
  rcases family_descends (prefixWord ++ tailWord_693426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693502 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_693502 : Nat := 118140960795 + 693502 * 2 ^ 59
def prefixEnd_693502 : Nat := 4983230072969 + 3 ^ 40 * 693502 * 2
def baseEnd_693502 : Nat := 158266604824200401749177

theorem tailTrace_693502 : CollatzResearch.WordTrace tailWord_693502 prefixEnd_693502 158266604824200401749177 := by
  unfold tailWord_693502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3161761991696021194645345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16862730622378779704775173 3161761991696021194645345)
  ·
    refine ⟨2371321493772015895984009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3161761991696021194645345 2371321493772015895984009)
    ·
      refine ⟨1778491120329011921988007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2371321493772015895984009 1778491120329011921988007)
      ·
        refine ⟨2667736680493517882982011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1778491120329011921988007 2667736680493517882982011)
        ·
          refine ⟨4001605020740276824473017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667736680493517882982011 4001605020740276824473017)
          ·
            refine ⟨3001203765555207618354763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4001605020740276824473017 3001203765555207618354763)
            ·
              refine ⟨4501805648332811427532145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001203765555207618354763 4501805648332811427532145)
              ·
                refine ⟨3376354236249608570649109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501805648332811427532145 3376354236249608570649109)
                ·
                  refine ⟨158266604824200401749177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3376354236249608570649109 158266604824200401749177)
                  ·
                    rfl

theorem cell21_693502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_693502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693502 prefixEnd_693502 := by exact prefixLift 693502
  have htrace : WordTrace (prefixWord ++ tailWord_693502) baseStart_693502 baseEnd_693502 := by
    simpa [prefixWord, tailWord_693502, baseEnd_693502] using wordTrace_append hprefix tailTrace_693502
  have hstable : (prefixWord ++ tailWord_693502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693502).length < 2 ^ (prefixWord ++ tailWord_693502).sum := by decide
  have hdescent : baseEnd_693502 < baseStart_693502 := by decide
  rcases family_descends (prefixWord ++ tailWord_693502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693505 : List Nat := [1, 2, 4, 1, 1, 5, 1, 3, 3]
def baseStart_693505 : Nat := 118140960795 + 693505 * 2 ^ 59
def prefixEnd_693505 : Nat := 4983230072969 + 3 ^ 40 * 693505 * 2
def baseEnd_693505 : Nat := 158267289465073063199171

theorem tailTrace_693505 : CollatzResearch.WordTrace tailWord_693505 prefixEnd_693505 158267289465073063199171 := by
  unfold tailWord_693505
  simp only [CollatzResearch.WordTrace]
  refine ⟨25294205352557301069521969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16862803568371534046347979 25294205352557301069521969)
  ·
    refine ⟨18970654014417975802141477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25294205352557301069521969 18970654014417975802141477)
    ·
      refine ⟨3556997627703370462901527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18970654014417975802141477 3556997627703370462901527)
      ·
        refine ⟨5335496441555055694352291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3556997627703370462901527 5335496441555055694352291)
        ·
          refine ⟨8003244662332583541528437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335496441555055694352291 8003244662332583541528437)
          ·
            refine ⟨750304187093679707018291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8003244662332583541528437 750304187093679707018291)
            ·
              refine ⟨1125456280640519560527437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750304187093679707018291 1125456280640519560527437)
              ·
                refine ⟨422046105240194835197789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1125456280640519560527437 422046105240194835197789)
                ·
                  refine ⟨158267289465073063199171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422046105240194835197789 158267289465073063199171)
                  ·
                    rfl

theorem cell21_693505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 3].length) (baseStart_693505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693505 prefixEnd_693505 := by exact prefixLift 693505
  have htrace : WordTrace (prefixWord ++ tailWord_693505) baseStart_693505 baseEnd_693505 := by
    simpa [prefixWord, tailWord_693505, baseEnd_693505] using wordTrace_append hprefix tailTrace_693505
  have hstable : (prefixWord ++ tailWord_693505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693505).length < 2 ^ (prefixWord ++ tailWord_693505).sum := by decide
  have hdescent : baseEnd_693505 < baseStart_693505 := by decide
  rcases family_descends (prefixWord ++ tailWord_693505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693516 : List Nat := [2, 2, 1, 2, 2, 5, 7]
def baseStart_693516 : Nat := 118140960795 + 693516 * 2 ^ 59
def prefixEnd_693516 : Nat := 4983230072969 + 3 ^ 40 * 693516 * 2
def baseEnd_693516 : Nat := 17585533312771054279535

theorem tailTrace_693516 : CollatzResearch.WordTrace tailWord_693516 prefixEnd_693516 17585533312771054279535 := by
  unfold tailWord_693516
  simp only [CollatzResearch.WordTrace]
  refine ⟨12647303277758724974086201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16863071037011633298781601 12647303277758724974086201)
  ·
    refine ⟨9485477458319043730564651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12647303277758724974086201 9485477458319043730564651)
    ·
      refine ⟨14228216187478565595846977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9485477458319043730564651 14228216187478565595846977)
      ·
        refine ⟨10671162140608924196885233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14228216187478565595846977 10671162140608924196885233)
        ·
          refine ⟨8003371605456693147663925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10671162140608924196885233 8003371605456693147663925)
          ·
            refine ⟨750316088011564982593493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8003371605456693147663925 750316088011564982593493)
            ·
              refine ⟨17585533312771054279535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 750316088011564982593493 17585533312771054279535)
              ·
                rfl

theorem cell21_693516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 7].length) (baseStart_693516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693516 prefixEnd_693516 := by exact prefixLift 693516
  have htrace : WordTrace (prefixWord ++ tailWord_693516) baseStart_693516 baseEnd_693516 := by
    simpa [prefixWord, tailWord_693516, baseEnd_693516] using wordTrace_append hprefix tailTrace_693516
  have hstable : (prefixWord ++ tailWord_693516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693516).length < 2 ^ (prefixWord ++ tailWord_693516).sum := by decide
  have hdescent : baseEnd_693516 < baseStart_693516 := by decide
  rcases family_descends (prefixWord ++ tailWord_693516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693522 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_693522 : Nat := 118140960795 + 693522 * 2 ^ 59
def prefixEnd_693522 : Nat := 4983230072969 + 3 ^ 40 * 693522 * 2
def baseEnd_693522 : Nat := 158271169096684811415803

theorem tailTrace_693522 : CollatzResearch.WordTrace tailWord_693522 prefixEnd_693522 158271169096684811415803 := by
  unfold tailWord_693522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323706348373928243222705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16863216928997141981927213 6323706348373928243222705)
  ·
    refine ⟨4742779761280446182417029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6323706348373928243222705 4742779761280446182417029)
    ·
      refine ⟨889271205240083659203193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4742779761280446182417029 889271205240083659203193)
      ·
        refine ⟨666953403930062744402395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 889271205240083659203193 666953403930062744402395)
        ·
          refine ⟨1000430105895094116603593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666953403930062744402395 1000430105895094116603593)
          ·
            refine ⟨750322579421320587452695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1000430105895094116603593 750322579421320587452695)
            ·
              refine ⟨1125483869131980881179043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750322579421320587452695 1125483869131980881179043)
              ·
                refine ⟨1688225803697971321768565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1125483869131980881179043 1688225803697971321768565)
                ·
                  refine ⟨158271169096684811415803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1688225803697971321768565 158271169096684811415803)
                  ·
                    rfl

theorem cell21_693522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_693522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693522 prefixEnd_693522 := by exact prefixLift 693522
  have htrace : WordTrace (prefixWord ++ tailWord_693522) baseStart_693522 baseEnd_693522 := by
    simpa [prefixWord, tailWord_693522, baseEnd_693522] using wordTrace_append hprefix tailTrace_693522
  have hstable : (prefixWord ++ tailWord_693522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693522).length < 2 ^ (prefixWord ++ tailWord_693522).sum := by decide
  have hdescent : baseEnd_693522 < baseStart_693522 := by decide
  rcases family_descends (prefixWord ++ tailWord_693522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693533 : List Nat := [1, 4, 2, 3, 1, 2, 2, 6]
def baseStart_693533 : Nat := 118140960795 + 693533 * 2 ^ 59
def prefixEnd_693533 : Nat := 4983230072969 + 3 ^ 40 * 693533 * 2
def baseEnd_693533 : Nat := 52757893148850412244149

theorem tailTrace_693533 : CollatzResearch.WordTrace tailWord_693533 prefixEnd_693533 52757893148850412244149 := by
  unfold tailWord_693533
  simp only [CollatzResearch.WordTrace]
  refine ⟨25295226596455861851541253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16863484397637241234360835 25295226596455861851541253)
  ·
    refine ⟨4742854986835474097163985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25295226596455861851541253 4742854986835474097163985)
    ·
      refine ⟨3557141240126605572872989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4742854986835474097163985 3557141240126605572872989)
      ·
        refine ⟨1333927965047477089827371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3557141240126605572872989 1333927965047477089827371)
        ·
          refine ⟨2000891947571215634741057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1333927965047477089827371 2000891947571215634741057)
          ·
            refine ⟨1500668960678411726055793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2000891947571215634741057 1500668960678411726055793)
            ·
              refine ⟨1125501720508808794541845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1500668960678411726055793 1125501720508808794541845)
              ·
                refine ⟨52757893148850412244149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1125501720508808794541845 52757893148850412244149)
                ·
                  rfl

theorem cell21_693533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 6].length) (baseStart_693533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693533 prefixEnd_693533 := by exact prefixLift 693533
  have htrace : WordTrace (prefixWord ++ tailWord_693533) baseStart_693533 baseEnd_693533 := by
    simpa [prefixWord, tailWord_693533, baseEnd_693533] using wordTrace_append hprefix tailTrace_693533
  have hstable : (prefixWord ++ tailWord_693533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693533).length < 2 ^ (prefixWord ++ tailWord_693533).sum := by decide
  have hdescent : baseEnd_693533 < baseStart_693533 := by decide
  rcases family_descends (prefixWord ++ tailWord_693533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693536 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 4]
def baseStart_693536 : Nat := 118140960795 + 693536 * 2 ^ 59
def prefixEnd_693536 : Nat := 4983230072969 + 3 ^ 40 * 693536 * 2
def baseEnd_693536 : Nat := 158274364087423898182441

theorem tailTrace_693536 : CollatzResearch.WordTrace tailWord_693536 prefixEnd_693536 158274364087423898182441 := by
  unfold tailWord_693536
  simp only [CollatzResearch.WordTrace]
  refine ⟨12647668007722496681950231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16863557343629995575933641 12647668007722496681950231)
  ·
    refine ⟨18971502011583745022925347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12647668007722496681950231 18971502011583745022925347)
    ·
      refine ⟨28457253017375617534388021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18971502011583745022925347 28457253017375617534388021)
      ·
        refine ⟨2667867470378964143848877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28457253017375617534388021 2667867470378964143848877)
        ·
          refine ⟨1000450301392111553943329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2667867470378964143848877 1000450301392111553943329)
          ·
            refine ⟨750337726044083665457497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1000450301392111553943329 750337726044083665457497)
            ·
              refine ⟨562753294533062749093123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750337726044083665457497 562753294533062749093123)
              ·
                refine ⟨844129941799594123639685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562753294533062749093123 844129941799594123639685)
                ·
                  refine ⟨158274364087423898182441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 844129941799594123639685 158274364087423898182441)
                  ·
                    rfl

theorem cell21_693536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_693536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693536 prefixEnd_693536 := by exact prefixLift 693536
  have htrace : WordTrace (prefixWord ++ tailWord_693536) baseStart_693536 baseEnd_693536 := by
    simpa [prefixWord, tailWord_693536, baseEnd_693536] using wordTrace_append hprefix tailTrace_693536
  have hstable : (prefixWord ++ tailWord_693536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693536).length < 2 ^ (prefixWord ++ tailWord_693536).sum := by decide
  have hdescent : baseEnd_693536 < baseStart_693536 := by decide
  rcases family_descends (prefixWord ++ tailWord_693536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693575 : List Nat := [1, 1, 4, 1, 2, 12]
def baseStart_693575 : Nat := 118140960795 + 693575 * 2 ^ 59
def prefixEnd_693575 : Nat := 4983230072969 + 3 ^ 40 * 693575 * 2
def baseEnd_693575 : Nat := 5862343126621055445643

theorem tailTrace_693575 : CollatzResearch.WordTrace tailWord_693575 prefixEnd_693575 5862343126621055445643 := by
  unfold tailWord_693575
  simp only [CollatzResearch.WordTrace]
  refine ⟨25296758462303703024570179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16864505641535802016380119 25296758462303703024570179)
  ·
    refine ⟨37945137693455554536855269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25296758462303703024570179 37945137693455554536855269)
    ·
      refine ⟨7114713317522916475660363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37945137693455554536855269 7114713317522916475660363)
      ·
        refine ⟨10672069976284374713490545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7114713317522916475660363 10672069976284374713490545)
        ·
          refine ⟨8004052482213281035117909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10672069976284374713490545 8004052482213281035117909)
          ·
            refine ⟨5862343126621055445643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8004052482213281035117909 5862343126621055445643)
            ·
              rfl

theorem cell21_693575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 12].length) (baseStart_693575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693575 prefixEnd_693575 := by exact prefixLift 693575
  have htrace : WordTrace (prefixWord ++ tailWord_693575) baseStart_693575 baseEnd_693575 := by
    simpa [prefixWord, tailWord_693575, baseEnd_693575] using wordTrace_append hprefix tailTrace_693575
  have hstable : (prefixWord ++ tailWord_693575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693575).length < 2 ^ (prefixWord ++ tailWord_693575).sum := by decide
  have hdescent : baseEnd_693575 < baseStart_693575 := by decide
  rcases family_descends (prefixWord ++ tailWord_693575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693640 : List Nat := [2, 1, 3, 3, 1, 2, 2, 4, 3]
def baseStart_693640 : Nat := 118140960795 + 693640 * 2 ^ 59
def prefixEnd_693640 : Nat := 4983230072969 + 3 ^ 40 * 693640 * 2
def baseEnd_693640 : Nat := 158298098304342828448895

theorem tailTrace_693640 : CollatzResearch.WordTrace tailWord_693640 prefixEnd_693640 158298098304342828448895 := by
  unfold tailWord_693640
  simp only [CollatzResearch.WordTrace]
  refine ⟨12649564603534109562843187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16866086138045479417124249 12649564603534109562843187)
  ·
    refine ⟨18974346905301164344264781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12649564603534109562843187 18974346905301164344264781)
    ·
      refine ⟨7115380089487936629099293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18974346905301164344264781 7115380089487936629099293)
      ·
        refine ⟨2668267533557976235912235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7115380089487936629099293 2668267533557976235912235)
        ·
          refine ⟨4002401300336964353868353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668267533557976235912235 4002401300336964353868353)
          ·
            refine ⟨3001800975252723265401265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4002401300336964353868353 3001800975252723265401265)
            ·
              refine ⟨2251350731439542449050949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3001800975252723265401265 2251350731439542449050949)
              ·
                refine ⟨422128262144914209197053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2251350731439542449050949 422128262144914209197053)
                ·
                  refine ⟨158298098304342828448895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422128262144914209197053 158298098304342828448895)
                  ·
                    rfl

theorem cell21_693640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 3].length) (baseStart_693640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693640 prefixEnd_693640 := by exact prefixLift 693640
  have htrace : WordTrace (prefixWord ++ tailWord_693640) baseStart_693640 baseEnd_693640 := by
    simpa [prefixWord, tailWord_693640, baseEnd_693640] using wordTrace_append hprefix tailTrace_693640
  have hstable : (prefixWord ++ tailWord_693640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693640).length < 2 ^ (prefixWord ++ tailWord_693640).sum := by decide
  have hdescent : baseEnd_693640 < baseStart_693640 := by decide
  rcases family_descends (prefixWord ++ tailWord_693640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693699 : List Nat := [1, 1, 1, 3, 1, 1, 4, 6, 3]
def baseStart_693699 : Nat := 118140960795 + 693699 * 2 ^ 59
def prefixEnd_693699 : Nat := 4983230072969 + 3 ^ 40 * 693699 * 2
def baseEnd_693699 : Nat := 158311562908171836965441

theorem tailTrace_693699 : CollatzResearch.WordTrace tailWord_693699 prefixEnd_693699 158311562908171836965441 := by
  unfold tailWord_693699
  simp only [CollatzResearch.WordTrace]
  refine ⟨25301281113854472202084151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16867520742569648134722767 25301281113854472202084151)
  ·
    refine ⟨37951921670781708303126227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25301281113854472202084151 37951921670781708303126227)
    ·
      refine ⟨56927882506172562454689341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37951921670781708303126227 56927882506172562454689341)
      ·
        refine ⟨21347955939814710920508503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56927882506172562454689341 21347955939814710920508503)
        ·
          refine ⟨32021933909722066380762755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21347955939814710920508503 32021933909722066380762755)
          ·
            refine ⟨48032900864583099571144133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32021933909722066380762755 48032900864583099571144133)
            ·
              refine ⟨9006168912109331169589525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48032900864583099571144133 9006168912109331169589525)
              ·
                refine ⟨422164167755124898574509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9006168912109331169589525 422164167755124898574509)
                ·
                  refine ⟨158311562908171836965441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422164167755124898574509 158311562908171836965441)
                  ·
                    rfl

theorem cell21_693699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 3].length) (baseStart_693699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693699 prefixEnd_693699 := by exact prefixLift 693699
  have htrace : WordTrace (prefixWord ++ tailWord_693699) baseStart_693699 baseEnd_693699 := by
    simpa [prefixWord, tailWord_693699, baseEnd_693699] using wordTrace_append hprefix tailTrace_693699
  have hstable : (prefixWord ++ tailWord_693699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693699).length < 2 ^ (prefixWord ++ tailWord_693699).sum := by decide
  have hdescent : baseEnd_693699 < baseStart_693699 := by decide
  rcases family_descends (prefixWord ++ tailWord_693699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693727 : List Nat := [1, 1, 2, 3, 3, 1, 1, 9]
def baseStart_693727 : Nat := 118140960795 + 693727 * 2 ^ 59
def prefixEnd_693727 : Nat := 4983230072969 + 3 ^ 40 * 693727 * 2
def baseEnd_693727 : Nat := 52772650963216670166239

theorem tailTrace_693727 : CollatzResearch.WordTrace tailWord_693727 prefixEnd_693727 52772650963216670166239 := by
  unfold tailWord_693727
  simp only [CollatzResearch.WordTrace]
  refine ⟨25302302357753032984103435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16868201571835355322735623 25302302357753032984103435)
  ·
    refine ⟨37953453536629549476155153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25302302357753032984103435 37953453536629549476155153)
    ·
      refine ⟨28465090152472162107116365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37953453536629549476155153 28465090152472162107116365)
      ·
        refine ⟨10674408807177060790168637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28465090152472162107116365 10674408807177060790168637)
        ·
          refine ⟨4002903302691397796313239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10674408807177060790168637 4002903302691397796313239)
          ·
            refine ⟨6004354954037096694469859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4002903302691397796313239 6004354954037096694469859)
            ·
              refine ⟨9006532431055645041704789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6004354954037096694469859 9006532431055645041704789)
              ·
                refine ⟨52772650963216670166239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9006532431055645041704789 52772650963216670166239)
                ·
                  rfl

theorem cell21_693727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 9].length) (baseStart_693727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693727 prefixEnd_693727 := by exact prefixLift 693727
  have htrace : WordTrace (prefixWord ++ tailWord_693727) baseStart_693727 baseEnd_693727 := by
    simpa [prefixWord, tailWord_693727, baseEnd_693727] using wordTrace_append hprefix tailTrace_693727
  have hstable : (prefixWord ++ tailWord_693727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693727).length < 2 ^ (prefixWord ++ tailWord_693727).sum := by decide
  have hdescent : baseEnd_693727 < baseStart_693727 := by decide
  rcases family_descends (prefixWord ++ tailWord_693727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693750 : List Nat := [5, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_693750 : Nat := 118140960795 + 693750 * 2 ^ 59
def prefixEnd_693750 : Nat := 4983230072969 + 3 ^ 40 * 693750 * 2
def baseEnd_693750 : Nat := 158323201803007081615337

theorem tailTrace_693750 : CollatzResearch.WordTrace tailWord_693750 prefixEnd_693750 158323201803007081615337 := by
  unfold tailWord_693750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581446327291856744511919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16868760824446471941460469 1581446327291856744511919)
  ·
    refine ⟨2372169490937785116767879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1581446327291856744511919 2372169490937785116767879)
    ·
      refine ⟨3558254236406677675151819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2372169490937785116767879 3558254236406677675151819)
      ·
        refine ⟨5337381354610016512727729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3558254236406677675151819 5337381354610016512727729)
        ·
          refine ⟨4003036015957512384545797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5337381354610016512727729 4003036015957512384545797)
          ·
            refine ⟨750569252992033572102337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4003036015957512384545797 750569252992033572102337)
            ·
              refine ⟨562926939744025179076753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750569252992033572102337 562926939744025179076753)
              ·
                refine ⟨422195204808018884307565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562926939744025179076753 422195204808018884307565)
                ·
                  refine ⟨158323201803007081615337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422195204808018884307565 158323201803007081615337)
                  ·
                    rfl

theorem cell21_693750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_693750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693750 prefixEnd_693750 := by exact prefixLift 693750
  have htrace : WordTrace (prefixWord ++ tailWord_693750) baseStart_693750 baseEnd_693750 := by
    simpa [prefixWord, tailWord_693750, baseEnd_693750] using wordTrace_append hprefix tailTrace_693750
  have hstable : (prefixWord ++ tailWord_693750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693750).length < 2 ^ (prefixWord ++ tailWord_693750).sum := by decide
  have hdescent : baseEnd_693750 < baseStart_693750 := by decide
  rcases family_descends (prefixWord ++ tailWord_693750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693761 : List Nat := [1, 2, 4, 1, 4, 2, 1, 6]
def baseStart_693761 : Nat := 118140960795 + 693761 * 2 ^ 59
def prefixEnd_693761 : Nat := 4983230072969 + 3 ^ 40 * 693761 * 2
def baseEnd_693761 : Nat := 52775237384291168977327

theorem tailTrace_693761 : CollatzResearch.WordTrace tailWord_693761 prefixEnd_693761 52775237384291168977327 := by
  unfold tailWord_693761
  simp only [CollatzResearch.WordTrace]
  refine ⟨25303542439629856790841137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16869028293086571193894091 25303542439629856790841137)
  ·
    refine ⟨18977656829722392593130853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25303542439629856790841137 18977656829722392593130853)
    ·
      refine ⟨3558310655572948611212035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18977656829722392593130853 3558310655572948611212035)
      ·
        refine ⟨5337465983359422916818053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3558310655572948611212035 5337465983359422916818053)
        ·
          refine ⟨1000774871879891796903385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5337465983359422916818053 1000774871879891796903385)
          ·
            refine ⟨750581153909918847677539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1000774871879891796903385 750581153909918847677539)
            ·
              refine ⟨1125871730864878271516309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750581153909918847677539 1125871730864878271516309)
              ·
                refine ⟨52775237384291168977327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1125871730864878271516309 52775237384291168977327)
                ·
                  rfl

theorem cell21_693761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 6].length) (baseStart_693761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693761 prefixEnd_693761 := by exact prefixLift 693761
  have htrace : WordTrace (prefixWord ++ tailWord_693761) baseStart_693761 baseEnd_693761 := by
    simpa [prefixWord, tailWord_693761, baseEnd_693761] using wordTrace_append hprefix tailTrace_693761
  have hstable : (prefixWord ++ tailWord_693761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693761).length < 2 ^ (prefixWord ++ tailWord_693761).sum := by decide
  have hdescent : baseEnd_693761 < baseStart_693761 := by decide
  rcases family_descends (prefixWord ++ tailWord_693761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693789 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 6]
def baseStart_693789 : Nat := 118140960795 + 693789 * 2 ^ 59
def prefixEnd_693789 : Nat := 4983230072969 + 3 ^ 40 * 693789 * 2
def baseEnd_693789 : Nat := 158332102134351680465257

theorem tailTrace_693789 : CollatzResearch.WordTrace tailWord_693789 prefixEnd_693789 158332102134351680465257 := by
  unfold tailWord_693789
  simp only [CollatzResearch.WordTrace]
  refine ⟨25304563683528417572860421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16869709122352278381906947 25304563683528417572860421)
  ·
    refine ⟨4744605690661578294911329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25304563683528417572860421 4744605690661578294911329)
    ·
      refine ⟨3558454267996183721183497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4744605690661578294911329 3558454267996183721183497)
      ·
        refine ⟨2668840700997137790887623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3558454267996183721183497 2668840700997137790887623)
        ·
          refine ⟨4003261051495706686331435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668840700997137790887623 4003261051495706686331435)
          ·
            refine ⟨6004891577243560029497153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4003261051495706686331435 6004891577243560029497153)
            ·
              refine ⟨4503668682932670022122865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6004891577243560029497153 4503668682932670022122865)
              ·
                refine ⟨3377751512199502516592149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4503668682932670022122865 3377751512199502516592149)
                ·
                  refine ⟨158332102134351680465257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3377751512199502516592149 158332102134351680465257)
                  ·
                    rfl

theorem cell21_693789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_693789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693789 prefixEnd_693789 := by exact prefixLift 693789
  have htrace : WordTrace (prefixWord ++ tailWord_693789) baseStart_693789 baseEnd_693789 := by
    simpa [prefixWord, tailWord_693789, baseEnd_693789] using wordTrace_append hprefix tailTrace_693789
  have hstable : (prefixWord ++ tailWord_693789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693789).length < 2 ^ (prefixWord ++ tailWord_693789).sum := by decide
  have hdescent : baseEnd_693789 < baseStart_693789 := by decide
  rcases family_descends (prefixWord ++ tailWord_693789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693792 : List Nat := [2, 1, 1, 6, 1, 1, 1, 5, 3]
def baseStart_693792 : Nat := 118140960795 + 693792 * 2 ^ 59
def prefixEnd_693792 : Nat := 4983230072969 + 3 ^ 40 * 693792 * 2
def baseEnd_693792 : Nat := 158332786775224341915251

theorem tailTrace_693792 : CollatzResearch.WordTrace tailWord_693792 prefixEnd_693792 158332786775224341915251 := by
  unfold tailWord_693792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12652336551258774542609815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16869782068345032723479753 12652336551258774542609815)
  ·
    refine ⟨18978504826888161813914723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12652336551258774542609815 18978504826888161813914723)
    ·
      refine ⟨28467757240332242720872085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18978504826888161813914723 28467757240332242720872085)
      ·
        refine ⟨1334426120640573877540879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28467757240332242720872085 1334426120640573877540879)
        ·
          refine ⟨2001639180960860816311319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334426120640573877540879 2001639180960860816311319)
          ·
            refine ⟨3002458771441291224466979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001639180960860816311319 3002458771441291224466979)
            ·
              refine ⟨4503688157161936836700469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002458771441291224466979 4503688157161936836700469)
              ·
                refine ⟨422220764733931578440669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4503688157161936836700469 422220764733931578440669)
                ·
                  refine ⟨158332786775224341915251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422220764733931578440669 158332786775224341915251)
                  ·
                    rfl

theorem cell21_693792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 3].length) (baseStart_693792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693792 prefixEnd_693792 := by exact prefixLift 693792
  have htrace : WordTrace (prefixWord ++ tailWord_693792) baseStart_693792 baseEnd_693792 := by
    simpa [prefixWord, tailWord_693792, baseEnd_693792] using wordTrace_append hprefix tailTrace_693792
  have hstable : (prefixWord ++ tailWord_693792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693792).length < 2 ^ (prefixWord ++ tailWord_693792).sum := by decide
  have hdescent : baseEnd_693792 < baseStart_693792 := by decide
  rcases family_descends (prefixWord ++ tailWord_693792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693806 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_693806 : Nat := 118140960795 + 693806 * 2 ^ 59
def prefixEnd_693806 : Nat := 4983230072969 + 3 ^ 40 * 693806 * 2
def baseEnd_693806 : Nat := 158335981765963428681889

theorem tailTrace_693806 : CollatzResearch.WordTrace tailWord_693806 prefixEnd_693806 158335981765963428681889 := by
  unfold tailWord_693806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3163147965558353684528659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16870122482977886317486181 3163147965558353684528659)
  ·
    refine ⟨4744721948337530526792989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3163147965558353684528659 4744721948337530526792989)
    ·
      refine ⟨1779270730626573947547371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4744721948337530526792989 1779270730626573947547371)
      ·
        refine ⟨2668906095939860921321057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1779270730626573947547371 2668906095939860921321057)
        ·
          refine ⟨2001679571954895690990793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2668906095939860921321057 2001679571954895690990793)
          ·
            refine ⟨1501259678966171768243095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2001679571954895690990793 1501259678966171768243095)
            ·
              refine ⟨2251889518449257652364643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501259678966171768243095 2251889518449257652364643)
              ·
                refine ⟨3377834277673886478546965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251889518449257652364643 3377834277673886478546965)
                ·
                  refine ⟨158335981765963428681889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3377834277673886478546965 158335981765963428681889)
                  ·
                    rfl

theorem cell21_693806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_693806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693806 prefixEnd_693806 := by exact prefixLift 693806
  have htrace : WordTrace (prefixWord ++ tailWord_693806) baseStart_693806 baseEnd_693806 := by
    simpa [prefixWord, tailWord_693806, baseEnd_693806] using wordTrace_append hprefix tailTrace_693806
  have hstable : (prefixWord ++ tailWord_693806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693806).length < 2 ^ (prefixWord ++ tailWord_693806).sum := by decide
  have hdescent : baseEnd_693806 < baseStart_693806 := by decide
  rcases family_descends (prefixWord ++ tailWord_693806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693834 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_693834 : Nat := 118140960795 + 693834 * 2 ^ 59
def prefixEnd_693834 : Nat := 4983230072969 + 3 ^ 40 * 693834 * 2
def baseEnd_693834 : Nat := 158342371747441602215165

theorem tailTrace_693834 : CollatzResearch.WordTrace tailWord_693834 prefixEnd_693834 158342371747441602215165 := by
  unfold tailWord_693834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6326551242091347564562139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16870803312243593505499037 6326551242091347564562139)
  ·
    refine ⟨9489826863137021346843209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6326551242091347564562139 9489826863137021346843209)
    ·
      refine ⟨7117370147352766010132407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9489826863137021346843209 7117370147352766010132407)
      ·
        refine ⟨10676055221029149015198611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7117370147352766010132407 10676055221029149015198611)
        ·
          refine ⟨16014082831543723522797917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10676055221029149015198611 16014082831543723522797917)
          ·
            refine ⟨6005281061828896321049219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16014082831543723522797917 6005281061828896321049219)
            ·
              refine ⟨9007921592743344481573829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6005281061828896321049219 9007921592743344481573829)
              ·
                refine ⟨1688985298639377090295093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9007921592743344481573829 1688985298639377090295093)
                ·
                  refine ⟨158342371747441602215165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1688985298639377090295093 158342371747441602215165)
                  ·
                    rfl

theorem cell21_693834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_693834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693834 prefixEnd_693834 := by exact prefixLift 693834
  have htrace : WordTrace (prefixWord ++ tailWord_693834) baseStart_693834 baseEnd_693834 := by
    simpa [prefixWord, tailWord_693834, baseEnd_693834] using wordTrace_append hprefix tailTrace_693834
  have hstable : (prefixWord ++ tailWord_693834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693834).length < 2 ^ (prefixWord ++ tailWord_693834).sum := by decide
  have hdescent : baseEnd_693834 < baseStart_693834 := by decide
  rcases family_descends (prefixWord ++ tailWord_693834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693837 : List Nat := [1, 6, 1, 1, 3, 1, 1, 7]
def baseStart_693837 : Nat := 118140960795 + 693837 * 2 ^ 59
def prefixEnd_693837 : Nat := 4983230072969 + 3 ^ 40 * 693837 * 2
def baseEnd_693837 : Nat := 52781018796104754555053

theorem tailTrace_693837 : CollatzResearch.WordTrace tailWord_693837 prefixEnd_693837 52781018796104754555053 := by
  unfold tailWord_693837
  simp only [CollatzResearch.WordTrace]
  refine ⟨25306314387354521770607765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16870876258236347847071843 25306314387354521770607765)
  ·
    refine ⟨1186233486907243207997239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25306314387354521770607765 1186233486907243207997239)
    ·
      refine ⟨1779350230360864811995859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1186233486907243207997239 1779350230360864811995859)
      ·
        refine ⟨2669025345541297217993789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1779350230360864811995859 2669025345541297217993789)
        ·
          refine ⟨1000884504577986456747671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2669025345541297217993789 1000884504577986456747671)
          ·
            refine ⟨1501326756866979685121507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000884504577986456747671 1501326756866979685121507)
            ·
              refine ⟨2251990135300469527682261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501326756866979685121507 2251990135300469527682261)
              ·
                refine ⟨52781018796104754555053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2251990135300469527682261 52781018796104754555053)
                ·
                  rfl

theorem cell21_693837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 7].length) (baseStart_693837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693837 prefixEnd_693837 := by exact prefixLift 693837
  have htrace : WordTrace (prefixWord ++ tailWord_693837) baseStart_693837 baseEnd_693837 := by
    simpa [prefixWord, tailWord_693837, baseEnd_693837] using wordTrace_append hprefix tailTrace_693837
  have hstable : (prefixWord ++ tailWord_693837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693837).length < 2 ^ (prefixWord ++ tailWord_693837).sum := by decide
  have hdescent : baseEnd_693837 < baseStart_693837 := by decide
  rcases family_descends (prefixWord ++ tailWord_693837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693919 : List Nat := [1, 1, 2, 7, 2, 1, 2, 2, 3]
def baseStart_693919 : Nat := 118140960795 + 693919 * 2 ^ 59
def prefixEnd_693919 : Nat := 4983230072969 + 3 ^ 40 * 693919 * 2
def baseEnd_693919 : Nat := 158361769905500343298325

theorem tailTrace_693919 : CollatzResearch.WordTrace tailWord_693919 prefixEnd_693919 158361769905500343298325 := by
  unfold tailWord_693919
  simp only [CollatzResearch.WordTrace]
  refine ⟨25309305173057449775092811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16872870115371633183395207 25309305173057449775092811)
  ·
    refine ⟨37963957759586174662639217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25309305173057449775092811 37963957759586174662639217)
    ·
      refine ⟨28472968319689630996979413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37963957759586174662639217 28472968319689630996979413)
      ·
        refine ⟨667335194992725726491705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28472968319689630996979413 667335194992725726491705)
        ·
          refine ⟨500501396244544294868779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 667335194992725726491705 500501396244544294868779)
          ·
            refine ⟨750752094366816442303169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500501396244544294868779 750752094366816442303169)
            ·
              refine ⟨563064070775112331727377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750752094366816442303169 563064070775112331727377)
              ·
                refine ⟨422298053081334248795533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563064070775112331727377 422298053081334248795533)
                ·
                  refine ⟨158361769905500343298325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422298053081334248795533 158361769905500343298325)
                  ·
                    rfl

theorem cell21_693919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 3].length) (baseStart_693919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693919 prefixEnd_693919 := by exact prefixLift 693919
  have htrace : WordTrace (prefixWord ++ tailWord_693919) baseStart_693919 baseEnd_693919 := by
    simpa [prefixWord, tailWord_693919, baseEnd_693919] using wordTrace_append hprefix tailTrace_693919
  have hstable : (prefixWord ++ tailWord_693919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693919).length < 2 ^ (prefixWord ++ tailWord_693919).sum := by decide
  have hdescent : baseEnd_693919 < baseStart_693919 := by decide
  rcases family_descends (prefixWord ++ tailWord_693919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693972 : List Nat := [2, 4, 1, 3, 1, 2, 8]
def baseStart_693972 : Nat := 118140960795 + 693972 * 2 ^ 59
def prefixEnd_693972 : Nat := 4983230072969 + 3 ^ 40 * 693972 * 2
def baseEnd_693972 : Nat := 17597096136398225434987

theorem tailTrace_693972 : CollatzResearch.WordTrace tailWord_693972 prefixEnd_693972 17597096136398225434987 := by
  unfold tailWord_693972
  simp only [CollatzResearch.WordTrace]
  refine ⟨12655619120932719913386085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16874158827910293217848113 12655619120932719913386085)
  ·
    refine ⟨2372928585174884983759891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12655619120932719913386085 2372928585174884983759891)
    ·
      refine ⟨3559392877762327475639837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2372928585174884983759891 3559392877762327475639837)
      ·
        refine ⟨1334772329160872803364939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3559392877762327475639837 1334772329160872803364939)
        ·
          refine ⟨2002158493741309205047409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334772329160872803364939 2002158493741309205047409)
          ·
            refine ⟨1501618870305981903785557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2002158493741309205047409 1501618870305981903785557)
            ·
              refine ⟨17597096136398225434987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1501618870305981903785557 17597096136398225434987)
              ·
                rfl

theorem cell21_693972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 8].length) (baseStart_693972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_693972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_693972 prefixEnd_693972 := by exact prefixLift 693972
  have htrace : WordTrace (prefixWord ++ tailWord_693972) baseStart_693972 baseEnd_693972 := by
    simpa [prefixWord, tailWord_693972, baseEnd_693972] using wordTrace_append hprefix tailTrace_693972
  have hstable : (prefixWord ++ tailWord_693972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693972).length < 2 ^ (prefixWord ++ tailWord_693972).sum := by decide
  have hdescent : baseEnd_693972 < baseStart_693972 := by decide
  rcases family_descends (prefixWord ++ tailWord_693972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694020 : List Nat := [2, 3, 2, 2, 1, 2, 3, 3, 3]
def baseStart_694020 : Nat := 118140960795 + 694020 * 2 ^ 59
def prefixEnd_694020 : Nat := 4983230072969 + 3 ^ 40 * 694020 * 2
def baseEnd_694020 : Nat := 158384819481546612114785

theorem tailTrace_694020 : CollatzResearch.WordTrace tailWord_694020 prefixEnd_694020 158384819481546612114785 := by
  unfold tailWord_694020
  simp only [CollatzResearch.WordTrace]
  refine ⟨12656494472845772012259757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16875325963794362683013009 12656494472845772012259757)
  ·
    refine ⟨4746185427317164504597409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12656494472845772012259757 4746185427317164504597409)
    ·
      refine ⟨3559639070487873378448057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4746185427317164504597409 3559639070487873378448057)
      ·
        refine ⟨2669729302865905033836043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3559639070487873378448057 2669729302865905033836043)
        ·
          refine ⟨4004593954298857550754065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2669729302865905033836043 4004593954298857550754065)
          ·
            refine ⟨3003445465724143163065549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4004593954298857550754065 3003445465724143163065549)
            ·
              refine ⟨1126292049646553686149581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3003445465724143163065549 1126292049646553686149581)
              ·
                refine ⟨422359518617457632306093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1126292049646553686149581 422359518617457632306093)
                ·
                  refine ⟨158384819481546612114785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422359518617457632306093 158384819481546612114785)
                  ·
                    rfl

theorem cell21_694020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_694020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694020 prefixEnd_694020 := by exact prefixLift 694020
  have htrace : WordTrace (prefixWord ++ tailWord_694020) baseStart_694020 baseEnd_694020 := by
    simpa [prefixWord, tailWord_694020, baseEnd_694020] using wordTrace_append hprefix tailTrace_694020
  have hstable : (prefixWord ++ tailWord_694020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694020).length < 2 ^ (prefixWord ++ tailWord_694020).sum := by decide
  have hdescent : baseEnd_694020 < baseStart_694020 := by decide
  rcases family_descends (prefixWord ++ tailWord_694020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694034 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_694034 : Nat := 118140960795 + 694034 * 2 ^ 59
def prefixEnd_694034 : Nat := 4983230072969 + 3 ^ 40 * 694034 * 2
def baseEnd_694034 : Nat := 158388014472285698881423

theorem tailTrace_694034 : CollatzResearch.WordTrace tailWord_694034 prefixEnd_694034 158388014472285698881423 := by
  unfold tailWord_694034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6328374891910206103882289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16875666378427216277019437 6328374891910206103882289)
  ·
    refine ⟨4746281168932654577911717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6328374891910206103882289 4746281168932654577911717)
    ·
      refine ⟨889927719174872733358447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4746281168932654577911717 889927719174872733358447)
      ·
        refine ⟨1334891578762309100037671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889927719174872733358447 1334891578762309100037671)
        ·
          refine ⟨2002337368143463650056507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334891578762309100037671 2002337368143463650056507)
          ·
            refine ⟨3003506052215195475084761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2002337368143463650056507 3003506052215195475084761)
            ·
              refine ⟨2252629539161396606313571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3003506052215195475084761 2252629539161396606313571)
              ·
                refine ⟨3378944308742094909470357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252629539161396606313571 3378944308742094909470357)
                ·
                  refine ⟨158388014472285698881423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3378944308742094909470357 158388014472285698881423)
                  ·
                    rfl

theorem cell21_694034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_694034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694034 prefixEnd_694034 := by exact prefixLift 694034
  have htrace : WordTrace (prefixWord ++ tailWord_694034) baseStart_694034 baseEnd_694034 := by
    simpa [prefixWord, tailWord_694034, baseEnd_694034] using wordTrace_append hprefix tailTrace_694034
  have hstable : (prefixWord ++ tailWord_694034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694034).length < 2 ^ (prefixWord ++ tailWord_694034).sum := by decide
  have hdescent : baseEnd_694034 < baseStart_694034 := by decide
  rcases family_descends (prefixWord ++ tailWord_694034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694076 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_694076 : Nat := 118140960795 + 694076 * 2 ^ 59
def prefixEnd_694076 : Nat := 4983230072969 + 3 ^ 40 * 694076 * 2
def baseEnd_694076 : Nat := 158397599444502959181337

theorem tailTrace_694076 : CollatzResearch.WordTrace tailWord_694076 prefixEnd_694076 158397599444502959181337 := by
  unfold tailWord_694076
  simp only [CollatzResearch.WordTrace]
  refine ⟨12657515716744332794279041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16876687622325777059038721 12657515716744332794279041)
  ·
    refine ⟨9493136787558249595709281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12657515716744332794279041 9493136787558249595709281)
    ·
      refine ⟨7119852590668687196781961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9493136787558249595709281 7119852590668687196781961)
      ·
        refine ⟨5339889443001515397586471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7119852590668687196781961 5339889443001515397586471)
        ·
          refine ⟨8009834164502273096379707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5339889443001515397586471 8009834164502273096379707)
          ·
            refine ⟨12014751246753409644569561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8009834164502273096379707 12014751246753409644569561)
            ·
              refine ⟨9011063435065057233427171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12014751246753409644569561 9011063435065057233427171)
              ·
                refine ⟨13516595152597585850140757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9011063435065057233427171 13516595152597585850140757)
                ·
                  refine ⟨158397599444502959181337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13516595152597585850140757 158397599444502959181337)
                  ·
                    rfl

theorem cell21_694076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_694076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694076 prefixEnd_694076 := by exact prefixLift 694076
  have htrace : WordTrace (prefixWord ++ tailWord_694076) baseStart_694076 baseEnd_694076 := by
    simpa [prefixWord, tailWord_694076, baseEnd_694076] using wordTrace_append hprefix tailTrace_694076
  have hstable : (prefixWord ++ tailWord_694076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694076).length < 2 ^ (prefixWord ++ tailWord_694076).sum := by decide
  have hdescent : baseEnd_694076 < baseStart_694076 := by decide
  rcases family_descends (prefixWord ++ tailWord_694076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694124 : List Nat := [2, 2, 1, 1, 4, 3, 3, 5]
def baseStart_694124 : Nat := 118140960795 + 694124 * 2 ^ 59
def prefixEnd_694124 : Nat := 4983230072969 + 3 ^ 40 * 694124 * 2
def baseEnd_694124 : Nat := 52802851232821847460413

theorem tailTrace_694124 : CollatzResearch.WordTrace tailWord_694124 prefixEnd_694124 52802851232821847460413 := by
  unfold tailWord_694124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12658391068657384893152713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16877854758209846524203617 12658391068657384893152713)
  ·
    refine ⟨9493793301493038669864535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12658391068657384893152713 9493793301493038669864535)
    ·
      refine ⟨14240689952239558004796803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9493793301493038669864535 14240689952239558004796803)
      ·
        refine ⟨21361034928359337007195205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14240689952239558004796803 21361034928359337007195205)
        ·
          refine ⟨4005194049067375688849101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21361034928359337007195205 4005194049067375688849101)
          ·
            refine ⟨1501947768400265883318413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4005194049067375688849101 1501947768400265883318413)
            ·
              refine ⟨563230413150099706244405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1501947768400265883318413 563230413150099706244405)
              ·
                refine ⟨52802851232821847460413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 563230413150099706244405 52802851232821847460413)
                ·
                  rfl

theorem cell21_694124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_694124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694124 prefixEnd_694124 := by exact prefixLift 694124
  have htrace : WordTrace (prefixWord ++ tailWord_694124) baseStart_694124 baseEnd_694124 := by
    simpa [prefixWord, tailWord_694124, baseEnd_694124] using wordTrace_append hprefix tailTrace_694124
  have hstable : (prefixWord ++ tailWord_694124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694124).length < 2 ^ (prefixWord ++ tailWord_694124).sum := by decide
  have hdescent : baseEnd_694124 < baseStart_694124 := by decide
  rcases family_descends (prefixWord ++ tailWord_694124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694307 : List Nat := [1, 1, 1, 4, 3, 1, 4, 3, 3]
def baseStart_694307 : Nat := 118140960795 + 694307 * 2 ^ 59
def prefixEnd_694307 : Nat := 4983230072969 + 3 ^ 40 * 694307 * 2
def baseEnd_694307 : Nat := 158450316791697890830865

theorem tailTrace_694307 : CollatzResearch.WordTrace tailWord_694307 prefixEnd_694307 158450316791697890830865 := by
  unfold tailWord_694307
  simp only [CollatzResearch.WordTrace]
  refine ⟨25323456695651792040217175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16882304463767861360144783 25323456695651792040217175)
  ·
    refine ⟨37985185043477688060325763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25323456695651792040217175 37985185043477688060325763)
    ·
      refine ⟨56977777565216532090488645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37985185043477688060325763 56977777565216532090488645)
      ·
        refine ⟨10683333293478099766966621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56977777565216532090488645 10683333293478099766966621)
        ·
          refine ⟨4006249985054287412612483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10683333293478099766966621 4006249985054287412612483)
          ·
            refine ⟨6009374977581431118918725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006249985054287412612483 6009374977581431118918725)
            ·
              refine ⟨1126757808296518334797261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6009374977581431118918725 1126757808296518334797261)
              ·
                refine ⟨422534178111194375548973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1126757808296518334797261 422534178111194375548973)
                ·
                  refine ⟨158450316791697890830865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422534178111194375548973 158450316791697890830865)
                  ·
                    rfl

theorem cell21_694307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 3].length) (baseStart_694307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694307 prefixEnd_694307 := by exact prefixLift 694307
  have htrace : WordTrace (prefixWord ++ tailWord_694307) baseStart_694307 baseEnd_694307 := by
    simpa [prefixWord, tailWord_694307, baseEnd_694307] using wordTrace_append hprefix tailTrace_694307
  have hstable : (prefixWord ++ tailWord_694307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694307).length < 2 ^ (prefixWord ++ tailWord_694307).sum := by decide
  have hdescent : baseEnd_694307 < baseStart_694307 := by decide
  rcases family_descends (prefixWord ++ tailWord_694307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694321 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 4]
def baseStart_694321 : Nat := 118140960795 + 694321 * 2 ^ 59
def prefixEnd_694321 : Nat := 4983230072969 + 3 ^ 40 * 694321 * 2
def baseEnd_694321 : Nat := 158453511782436977597503

theorem tailTrace_694321 : CollatzResearch.WordTrace tailWord_694321 prefixEnd_694321 158453511782436977597503 := by
  unfold tailWord_694321
  simp only [CollatzResearch.WordTrace]
  refine ⟨25323967317601072431226817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16882644878400714954151211 25323967317601072431226817)
  ·
    refine ⟨18992975488200804323420113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25323967317601072431226817 18992975488200804323420113)
    ·
      refine ⟨14244731616150603242565085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18992975488200804323420113 14244731616150603242565085)
      ·
        refine ⟨5341774356056476215961907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14244731616150603242565085 5341774356056476215961907)
        ·
          refine ⟨8012661534084714323942861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5341774356056476215961907 8012661534084714323942861)
          ·
            refine ⟨3004748075281767871478573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8012661534084714323942861 3004748075281767871478573)
            ·
              refine ⟨1126780528230662951804465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3004748075281767871478573 1126780528230662951804465)
              ·
                refine ⟨845085396172997213853349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1126780528230662951804465 845085396172997213853349)
                ·
                  refine ⟨158453511782436977597503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 845085396172997213853349 158453511782436977597503)
                  ·
                    rfl

theorem cell21_694321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_694321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694321 prefixEnd_694321 := by exact prefixLift 694321
  have htrace : WordTrace (prefixWord ++ tailWord_694321) baseStart_694321 baseEnd_694321 := by
    simpa [prefixWord, tailWord_694321, baseEnd_694321] using wordTrace_append hprefix tailTrace_694321
  have hstable : (prefixWord ++ tailWord_694321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694321).length < 2 ^ (prefixWord ++ tailWord_694321).sum := by decide
  have hdescent : baseEnd_694321 < baseStart_694321 := by decide
  rcases family_descends (prefixWord ++ tailWord_694321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694324 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 5]
def baseStart_694324 : Nat := 118140960795 + 694324 * 2 ^ 59
def prefixEnd_694324 : Nat := 4983230072969 + 3 ^ 40 * 694324 * 2
def baseEnd_694324 : Nat := 158454196423309639047497

theorem tailTrace_694324 : CollatzResearch.WordTrace tailWord_694324 prefixEnd_694324 158454196423309639047497 := by
  unfold tailWord_694324
  simp only [CollatzResearch.WordTrace]
  refine ⟨12662038368295101971793013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16882717824393469295724017 12662038368295101971793013)
  ·
    refine ⟨1187066097027665809855595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12662038368295101971793013 1187066097027665809855595)
    ·
      refine ⟨1780599145541498714783393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1187066097027665809855595 1780599145541498714783393)
      ·
        refine ⟨1335449359156124036087545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1780599145541498714783393 1335449359156124036087545)
        ·
          refine ⟨1001587019367093027065659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1335449359156124036087545 1001587019367093027065659)
          ·
            refine ⟨1502380529050639540598489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001587019367093027065659 1502380529050639540598489)
            ·
              refine ⟨1126785396787979655448867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1502380529050639540598489 1126785396787979655448867)
              ·
                refine ⟨1690178095181969483173301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126785396787979655448867 1690178095181969483173301)
                ·
                  refine ⟨158454196423309639047497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1690178095181969483173301 158454196423309639047497)
                  ·
                    rfl

theorem cell21_694324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_694324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694324 prefixEnd_694324 := by exact prefixLift 694324
  have htrace : WordTrace (prefixWord ++ tailWord_694324) baseStart_694324 baseEnd_694324 := by
    simpa [prefixWord, tailWord_694324, baseEnd_694324] using wordTrace_append hprefix tailTrace_694324
  have hstable : (prefixWord ++ tailWord_694324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694324).length < 2 ^ (prefixWord ++ tailWord_694324).sum := by decide
  have hdescent : baseEnd_694324 < baseStart_694324 := by decide
  rcases family_descends (prefixWord ++ tailWord_694324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694358 : List Nat := [5, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_694358 : Nat := 118140960795 + 694358 * 2 ^ 59
def prefixEnd_694358 : Nat := 4983230072969 + 3 ^ 40 * 694358 * 2
def baseEnd_694358 : Nat := 158461955686533135480761

theorem tailTrace_694358 : CollatzResearch.WordTrace tailWord_694358 prefixEnd_694358 158461955686533135480761 := by
  unfold tailWord_694358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582832301154189234395233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16883544545644685166882485 1582832301154189234395233)
  ·
    refine ⟨1187124225865641925796425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1582832301154189234395233 1187124225865641925796425)
    ·
      refine ⟨890343169399231444347319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1187124225865641925796425 890343169399231444347319)
      ·
        refine ⟨1335514754098847166520979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890343169399231444347319 1335514754098847166520979)
        ·
          refine ⟨2003272131148270749781469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335514754098847166520979 2003272131148270749781469)
          ·
            refine ⟨751227049180601531168051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2003272131148270749781469 751227049180601531168051)
            ·
              refine ⟨1126840573770902296752077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751227049180601531168051 1126840573770902296752077)
              ·
                refine ⟨422565215164088361282029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1126840573770902296752077 422565215164088361282029)
                ·
                  refine ⟨158461955686533135480761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422565215164088361282029 158461955686533135480761)
                  ·
                    rfl

theorem cell21_694358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_694358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694358 prefixEnd_694358 := by exact prefixLift 694358
  have htrace : WordTrace (prefixWord ++ tailWord_694358) baseStart_694358 baseEnd_694358 := by
    simpa [prefixWord, tailWord_694358, baseEnd_694358] using wordTrace_append hprefix tailTrace_694358
  have hstable : (prefixWord ++ tailWord_694358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694358).length < 2 ^ (prefixWord ++ tailWord_694358).sum := by decide
  have hdescent : baseEnd_694358 < baseStart_694358 := by decide
  rcases family_descends (prefixWord ++ tailWord_694358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694380 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_694380 : Nat := 118140960795 + 694380 * 2 ^ 59
def prefixEnd_694380 : Nat := 4983230072969 + 3 ^ 40 * 694380 * 2
def baseEnd_694380 : Nat := 158466976386265986114049

theorem tailTrace_694380 : CollatzResearch.WordTrace tailWord_694380 prefixEnd_694380 158466976386265986114049 := by
  unfold tailWord_694380
  simp only [CollatzResearch.WordTrace]
  refine ⟨12663059612193662753812297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16884079482924883671749729 12663059612193662753812297)
  ·
    refine ⟨9497294709145247065359223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12663059612193662753812297 9497294709145247065359223)
    ·
      refine ⟨14245942063717870598038835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9497294709145247065359223 14245942063717870598038835)
      ·
        refine ⟨21368913095576805897058253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14245942063717870598038835 21368913095576805897058253)
        ·
          refine ⟨8013342410841302211396845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21368913095576805897058253 8013342410841302211396845)
          ·
            refine ⟨3005003404065488329273817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8013342410841302211396845 3005003404065488329273817)
            ·
              refine ⟨2253752553049116246955363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005003404065488329273817 2253752553049116246955363)
              ·
                refine ⟨3380628829573674370433045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253752553049116246955363 3380628829573674370433045)
                ·
                  refine ⟨158466976386265986114049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3380628829573674370433045 158466976386265986114049)
                  ·
                    rfl

theorem cell21_694380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_694380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694380 prefixEnd_694380 := by exact prefixLift 694380
  have htrace : WordTrace (prefixWord ++ tailWord_694380) baseStart_694380 baseEnd_694380 := by
    simpa [prefixWord, tailWord_694380, baseEnd_694380] using wordTrace_append hprefix tailTrace_694380
  have hstable : (prefixWord ++ tailWord_694380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694380).length < 2 ^ (prefixWord ++ tailWord_694380).sum := by decide
  have hdescent : baseEnd_694380 < baseStart_694380 := by decide
  rcases family_descends (prefixWord ++ tailWord_694380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694397 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 4]
def baseStart_694397 : Nat := 118140960795 + 694397 * 2 ^ 59
def prefixEnd_694397 : Nat := 4983230072969 + 3 ^ 40 * 694397 * 2
def baseEnd_694397 : Nat := 158470856017877734330681

theorem tailTrace_694397 : CollatzResearch.WordTrace tailWord_694397 prefixEnd_694397 158470856017877734330681 := by
  unfold tailWord_694397
  simp only [CollatzResearch.WordTrace]
  refine ⟨25326739265325737410993445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16884492843550491607328963 25326739265325737410993445)
  ·
    refine ⟨4748763612248575764561271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25326739265325737410993445 4748763612248575764561271)
    ·
      refine ⟨7123145418372863646841907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4748763612248575764561271 7123145418372863646841907)
      ·
        refine ⟨10684718127559295470262861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7123145418372863646841907 10684718127559295470262861)
        ·
          refine ⟨4006769297834735801348573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10684718127559295470262861 4006769297834735801348573)
          ·
            refine ⟨1502538486688025925505715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4006769297834735801348573 1502538486688025925505715)
            ·
              refine ⟨2253807730032038888258573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502538486688025925505715 2253807730032038888258573)
              ·
                refine ⟨845177898762014583096965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2253807730032038888258573 845177898762014583096965)
                ·
                  refine ⟨158470856017877734330681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 845177898762014583096965 158470856017877734330681)
                  ·
                    rfl

theorem cell21_694397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_694397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694397 prefixEnd_694397 := by exact prefixLift 694397
  have htrace : WordTrace (prefixWord ++ tailWord_694397) baseStart_694397 baseEnd_694397 := by
    simpa [prefixWord, tailWord_694397, baseEnd_694397] using wordTrace_append hprefix tailTrace_694397
  have hstable : (prefixWord ++ tailWord_694397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694397).length < 2 ^ (prefixWord ++ tailWord_694397).sum := by decide
  have hdescent : baseEnd_694397 < baseStart_694397 := by decide
  rcases family_descends (prefixWord ++ tailWord_694397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694456 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 4]
def baseStart_694456 : Nat := 118140960795 + 694456 * 2 ^ 59
def prefixEnd_694456 : Nat := 4983230072969 + 3 ^ 40 * 694456 * 2
def baseEnd_694456 : Nat := 158484320621706742847227

theorem tailTrace_694456 : CollatzResearch.WordTrace tailWord_694456 prefixEnd_694456 158484320621706742847227 := by
  unfold tailWord_694456
  simp only [CollatzResearch.WordTrace]
  refine ⟨12664445586055995243695611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16885927448074660324927481 12664445586055995243695611)
  ·
    refine ⟨18996668379083992865543417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12664445586055995243695611 18996668379083992865543417)
    ·
      refine ⟨14247501284312994649157563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18996668379083992865543417 14247501284312994649157563)
      ·
        refine ⟨21371251926469491973736345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14247501284312994649157563 21371251926469491973736345)
        ·
          refine ⟨16028438944852118980302259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21371251926469491973736345 16028438944852118980302259)
          ·
            refine ⟨24042658417278178470453389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16028438944852118980302259 24042658417278178470453389)
            ·
              refine ⟨9015996906479316926420021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24042658417278178470453389 9015996906479316926420021)
              ·
                refine ⟨845249709982435961851877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9015996906479316926420021 845249709982435961851877)
                ·
                  refine ⟨158484320621706742847227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 845249709982435961851877 158484320621706742847227)
                  ·
                    rfl

theorem cell21_694456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_694456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694456 prefixEnd_694456 := by exact prefixLift 694456
  have htrace : WordTrace (prefixWord ++ tailWord_694456) baseStart_694456 baseEnd_694456 := by
    simpa [prefixWord, tailWord_694456, baseEnd_694456] using wordTrace_append hprefix tailTrace_694456
  have hstable : (prefixWord ++ tailWord_694456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694456).length < 2 ^ (prefixWord ++ tailWord_694456).sum := by decide
  have hdescent : baseEnd_694456 < baseStart_694456 := by decide
  rcases family_descends (prefixWord ++ tailWord_694456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694518 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_694518 : Nat := 118140960795 + 694518 * 2 ^ 59
def prefixEnd_694518 : Nat := 4983230072969 + 3 ^ 40 * 694518 * 2
def baseEnd_694518 : Nat := 158498469866408412813767

theorem tailTrace_694518 : CollatzResearch.WordTrace tailWord_694518 prefixEnd_694518 158498469866408412813767 := by
  unfold tailWord_694518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583197031117960942259263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16887434998591583384098805 1583197031117960942259263)
  ·
    refine ⟨2374795546676941413388895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1583197031117960942259263 2374795546676941413388895)
    ·
      refine ⟨3562193320015412120083343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2374795546676941413388895 3562193320015412120083343)
      ·
        refine ⟨5343289980023118180125015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3562193320015412120083343 5343289980023118180125015)
        ·
          refine ⟨8014934970034677270187523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5343289980023118180125015 8014934970034677270187523)
          ·
            refine ⟨12022402455052015905281285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8014934970034677270187523 12022402455052015905281285)
            ·
              refine ⟨2254200460322252982240241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12022402455052015905281285 2254200460322252982240241)
              ·
                refine ⟨1690650345241689736680181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254200460322252982240241 1690650345241689736680181)
                ·
                  refine ⟨158498469866408412813767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1690650345241689736680181 158498469866408412813767)
                  ·
                    rfl

theorem cell21_694518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_694518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694518 prefixEnd_694518 := by exact prefixLift 694518
  have htrace : WordTrace (prefixWord ++ tailWord_694518) baseStart_694518 baseEnd_694518 := by
    simpa [prefixWord, tailWord_694518, baseEnd_694518] using wordTrace_append hprefix tailTrace_694518
  have hstable : (prefixWord ++ tailWord_694518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694518).length < 2 ^ (prefixWord ++ tailWord_694518).sum := by decide
  have hdescent : baseEnd_694518 < baseStart_694518 := by decide
  rcases family_descends (prefixWord ++ tailWord_694518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694608 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 4]
def baseStart_694608 : Nat := 118140960795 + 694608 * 2 ^ 59
def prefixEnd_694608 : Nat := 4983230072969 + 3 ^ 40 * 694608 * 2
def baseEnd_694608 : Nat := 158519009092588256313583

theorem tailTrace_694608 : CollatzResearch.WordTrace tailWord_694608 prefixEnd_694608 158519009092588256313583 := by
  unfold tailWord_694608
  simp only [CollatzResearch.WordTrace]
  refine ⟨12667217533780660223462239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16889623378374213631282985 12667217533780660223462239)
  ·
    refine ⟨19000826300670990335193359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12667217533780660223462239 19000826300670990335193359)
    ·
      refine ⟨28501239451006485502790039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19000826300670990335193359 28501239451006485502790039)
      ·
        refine ⟨42751859176509728254185059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28501239451006485502790039 42751859176509728254185059)
        ·
          refine ⟨64127788764764592381277589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42751859176509728254185059 64127788764764592381277589)
          ·
            refine ⟨3005990098348340267872387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64127788764764592381277589 3005990098348340267872387)
            ·
              refine ⟨4508985147522510401808581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005990098348340267872387 4508985147522510401808581)
              ·
                refine ⟨845434715160470700339109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4508985147522510401808581 845434715160470700339109)
                ·
                  refine ⟨158519009092588256313583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 845434715160470700339109 158519009092588256313583)
                  ·
                    rfl

theorem cell21_694608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_694608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694608 prefixEnd_694608 := by exact prefixLift 694608
  have htrace : WordTrace (prefixWord ++ tailWord_694608) baseStart_694608 baseEnd_694608 := by
    simpa [prefixWord, tailWord_694608, baseEnd_694608] using wordTrace_append hprefix tailTrace_694608
  have hstable : (prefixWord ++ tailWord_694608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694608).length < 2 ^ (prefixWord ++ tailWord_694608).sum := by decide
  have hdescent : baseEnd_694608 < baseStart_694608 := by decide
  rcases family_descends (prefixWord ++ tailWord_694608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694670 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_694670 : Nat := 118140960795 + 694670 * 2 ^ 59
def prefixEnd_694670 : Nat := 4983230072969 + 3 ^ 40 * 694670 * 2
def baseEnd_694670 : Nat := 158533158337289926280123

theorem tailTrace_694670 : CollatzResearch.WordTrace tailWord_694670 prefixEnd_694670 158533158337289926280123 := by
  unfold tailWord_694670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167087049167088129460183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16891130928891136690454309 3167087049167088129460183)
  ·
    refine ⟨4750630573750632194190275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3167087049167088129460183 4750630573750632194190275)
    ·
      refine ⟨7125945860625948291285413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4750630573750632194190275 7125945860625948291285413)
      ·
        refine ⟨1336114848867365304616015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7125945860625948291285413 1336114848867365304616015)
        ·
          refine ⟨2004172273301047956924023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336114848867365304616015 2004172273301047956924023)
          ·
            refine ⟨3006258409951571935386035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004172273301047956924023 3006258409951571935386035)
            ·
              refine ⟨4509387614927357903079053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006258409951571935386035 4509387614927357903079053)
              ·
                refine ⟨1691020355597759213654645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4509387614927357903079053 1691020355597759213654645)
                ·
                  refine ⟨158533158337289926280123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1691020355597759213654645 158533158337289926280123)
                  ·
                    rfl

theorem cell21_694670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_694670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694670 prefixEnd_694670 := by exact prefixLift 694670
  have htrace : WordTrace (prefixWord ++ tailWord_694670) baseStart_694670 baseEnd_694670 := by
    simpa [prefixWord, tailWord_694670, baseEnd_694670] using wordTrace_append hprefix tailTrace_694670
  have hstable : (prefixWord ++ tailWord_694670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694670).length < 2 ^ (prefixWord ++ tailWord_694670).sum := by decide
  have hdescent : baseEnd_694670 < baseStart_694670 := by decide
  rcases family_descends (prefixWord ++ tailWord_694670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694721 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 5]
def baseStart_694721 : Nat := 118140960795 + 694721 * 2 ^ 59
def prefixEnd_694721 : Nat := 4983230072969 + 3 ^ 40 * 694721 * 2
def baseEnd_694721 : Nat := 158544797232125170930019

theorem tailTrace_694721 : CollatzResearch.WordTrace tailWord_694721 prefixEnd_694721 158544797232125170930019 := by
  unfold tailWord_694721
  simp only [CollatzResearch.WordTrace]
  refine ⟨25338556516151940745788017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16892371010767960497192011 25338556516151940745788017)
  ·
    refine ⟨19003917387113955559341013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25338556516151940745788017 19003917387113955559341013)
    ·
      refine ⟨445404313760483333422055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19003917387113955559341013 445404313760483333422055)
      ·
        refine ⟨668106470640725000133083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445404313760483333422055 668106470640725000133083)
        ·
          refine ⟨1002159705961087500199625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668106470640725000133083 1002159705961087500199625)
          ·
            refine ⟨751619779470815625149719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002159705961087500199625 751619779470815625149719)
            ·
              refine ⟨1127429669206223437724579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751619779470815625149719 1127429669206223437724579)
              ·
                refine ⟨1691144503809335156586869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127429669206223437724579 1691144503809335156586869)
                ·
                  refine ⟨158544797232125170930019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1691144503809335156586869 158544797232125170930019)
                  ·
                    rfl

theorem cell21_694721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 5].length) (baseStart_694721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694721 prefixEnd_694721 := by exact prefixLift 694721
  have htrace : WordTrace (prefixWord ++ tailWord_694721) baseStart_694721 baseEnd_694721 := by
    simpa [prefixWord, tailWord_694721, baseEnd_694721] using wordTrace_append hprefix tailTrace_694721
  have hstable : (prefixWord ++ tailWord_694721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694721).length < 2 ^ (prefixWord ++ tailWord_694721).sum := by decide
  have hdescent : baseEnd_694721 < baseStart_694721 := by decide
  rcases family_descends (prefixWord ++ tailWord_694721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694729 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 5]
def baseStart_694729 : Nat := 118140960795 + 694729 * 2 ^ 59
def prefixEnd_694729 : Nat := 4983230072969 + 3 ^ 40 * 694729 * 2
def baseEnd_694729 : Nat := 158546622941118934796669

theorem tailTrace_694729 : CollatzResearch.WordTrace tailWord_694729 prefixEnd_694729 158546622941118934796669 := by
  unfold tailWord_694729
  simp only [CollatzResearch.WordTrace]
  refine ⟨25338848300122958112079241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16892565533415305408052827 25338848300122958112079241)
  ·
    refine ⟨19004136225092218584059431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25338848300122958112079241 19004136225092218584059431)
    ·
      refine ⟨28506204337638327876089147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19004136225092218584059431 28506204337638327876089147)
      ·
        refine ⟨42759306506457491814133721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28506204337638327876089147 42759306506457491814133721)
        ·
          refine ⟨32069479879843118860600291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42759306506457491814133721 32069479879843118860600291)
          ·
            refine ⟨48104219819764678290900437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32069479879843118860600291 48104219819764678290900437)
            ·
              refine ⟨1127442652025734647442979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48104219819764678290900437 1127442652025734647442979)
              ·
                refine ⟨1691163978038601971164469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127442652025734647442979 1691163978038601971164469)
                ·
                  refine ⟨158546622941118934796669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1691163978038601971164469 158546622941118934796669)
                  ·
                    rfl

theorem cell21_694729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_694729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694729 prefixEnd_694729 := by exact prefixLift 694729
  have htrace : WordTrace (prefixWord ++ tailWord_694729) baseStart_694729 baseEnd_694729 := by
    simpa [prefixWord, tailWord_694729, baseEnd_694729] using wordTrace_append hprefix tailTrace_694729
  have hstable : (prefixWord ++ tailWord_694729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694729).length < 2 ^ (prefixWord ++ tailWord_694729).sum := by decide
  have hdescent : baseEnd_694729 < baseStart_694729 := by decide
  rcases family_descends (prefixWord ++ tailWord_694729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694805 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 5]
def baseStart_694805 : Nat := 118140960795 + 694805 * 2 ^ 59
def prefixEnd_694805 : Nat := 4983230072969 + 3 ^ 40 * 694805 * 2
def baseEnd_694805 : Nat := 158563967176559691529847

theorem tailTrace_694805 : CollatzResearch.WordTrace tailWord_694805 prefixEnd_694805 158563967176559691529847 := by
  unfold tailWord_694805
  simp only [CollatzResearch.WordTrace]
  refine ⟨25341620247847623091845869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16894413498565082061230579 25341620247847623091845869)
  ·
    refine ⟨9503107592942858659442201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25341620247847623091845869 9503107592942858659442201)
    ·
      refine ⟨7127330694707143994581651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9503107592942858659442201 7127330694707143994581651)
      ·
        refine ⟨10690996042060715991872477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7127330694707143994581651 10690996042060715991872477)
        ·
          refine ⟨4009123515772768496952179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10690996042060715991872477 4009123515772768496952179)
          ·
            refine ⟨6013685273659152745428269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009123515772768496952179 6013685273659152745428269)
            ·
              refine ⟨2255131977622182279535601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6013685273659152745428269 2255131977622182279535601)
              ·
                refine ⟨1691348983216636709651701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2255131977622182279535601 1691348983216636709651701)
                ·
                  refine ⟨158563967176559691529847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1691348983216636709651701 158563967176559691529847)
                  ·
                    rfl

theorem cell21_694805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_694805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694805 prefixEnd_694805 := by exact prefixLift 694805
  have htrace : WordTrace (prefixWord ++ tailWord_694805) baseStart_694805 baseEnd_694805 := by
    simpa [prefixWord, tailWord_694805, baseEnd_694805] using wordTrace_append hprefix tailTrace_694805
  have hstable : (prefixWord ++ tailWord_694805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694805).length < 2 ^ (prefixWord ++ tailWord_694805).sum := by decide
  have hdescent : baseEnd_694805 < baseStart_694805 := by decide
  rcases family_descends (prefixWord ++ tailWord_694805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694853 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 4]
def baseStart_694853 : Nat := 118140960795 + 694853 * 2 ^ 59
def prefixEnd_694853 : Nat := 4983230072969 + 3 ^ 40 * 694853 * 2
def baseEnd_694853 : Nat := 158574921430522274729749

theorem tailTrace_694853 : CollatzResearch.WordTrace tailWord_694853 prefixEnd_694853 158574921430522274729749 := by
  unfold tailWord_694853
  simp only [CollatzResearch.WordTrace]
  refine ⟨25343370951673727289593213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16895580634449151526395475 25343370951673727289593213)
  ·
    refine ⟨9503764106877647733597455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25343370951673727289593213 9503764106877647733597455)
    ·
      refine ⟨14255646160316471600396183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9503764106877647733597455 14255646160316471600396183)
      ·
        refine ⟨21383469240474707400594275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14255646160316471600396183 21383469240474707400594275)
        ·
          refine ⟨32075203860712061100891413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21383469240474707400594275 32075203860712061100891413)
          ·
            refine ⟨1503525180970877864104285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32075203860712061100891413 1503525180970877864104285)
            ·
              refine ⟨563821942864079199039107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1503525180970877864104285 563821942864079199039107)
              ·
                refine ⟨845732914296118798558661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563821942864079199039107 845732914296118798558661)
                ·
                  refine ⟨158574921430522274729749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 845732914296118798558661 158574921430522274729749)
                  ·
                    rfl

theorem cell21_694853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_694853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694853 prefixEnd_694853 := by exact prefixLift 694853
  have htrace : WordTrace (prefixWord ++ tailWord_694853) baseStart_694853 baseEnd_694853 := by
    simpa [prefixWord, tailWord_694853, baseEnd_694853] using wordTrace_append hprefix tailTrace_694853
  have hstable : (prefixWord ++ tailWord_694853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694853).length < 2 ^ (prefixWord ++ tailWord_694853).sum := by decide
  have hdescent : baseEnd_694853 < baseStart_694853 := by decide
  rcases family_descends (prefixWord ++ tailWord_694853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694864 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_694864 : Nat := 118140960795 + 694864 * 2 ^ 59
def prefixEnd_694864 : Nat := 4983230072969 + 3 ^ 40 * 694864 * 2
def baseEnd_694864 : Nat := 158577431780388700046393

theorem tailTrace_694864 : CollatzResearch.WordTrace tailWord_694864 prefixEnd_694864 158577431780388700046393 := by
  unfold tailWord_694864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12671886077316938084121823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16895848103089250778829097 12671886077316938084121823)
  ·
    refine ⟨19007829115975407126182735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12671886077316938084121823 19007829115975407126182735)
    ·
      refine ⟨28511743673963110689274103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19007829115975407126182735 28511743673963110689274103)
      ·
        refine ⟨42767615510944666033911155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28511743673963110689274103 42767615510944666033911155)
        ·
          refine ⟨64151423266416999050866733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42767615510944666033911155 64151423266416999050866733)
          ·
            refine ⟨24056783724906374644075025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64151423266416999050866733 24056783724906374644075025)
            ·
              refine ⟨18042587793679780983056269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24056783724906374644075025 18042587793679780983056269)
              ·
                refine ⟨6765970422629917868646101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18042587793679780983056269 6765970422629917868646101)
                ·
                  refine ⟨158577431780388700046393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6765970422629917868646101 158577431780388700046393)
                  ·
                    rfl

theorem cell21_694864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_694864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694864 prefixEnd_694864 := by exact prefixLift 694864
  have htrace : WordTrace (prefixWord ++ tailWord_694864) baseStart_694864 baseEnd_694864 := by
    simpa [prefixWord, tailWord_694864, baseEnd_694864] using wordTrace_append hprefix tailTrace_694864
  have hstable : (prefixWord ++ tailWord_694864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694864).length < 2 ^ (prefixWord ++ tailWord_694864).sum := by decide
  have hdescent : baseEnd_694864 < baseStart_694864 := by decide
  rcases family_descends (prefixWord ++ tailWord_694864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694895 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 6]
def baseStart_694895 : Nat := 118140960795 + 694895 * 2 ^ 59
def prefixEnd_694895 : Nat := 4983230072969 + 3 ^ 40 * 694895 * 2
def baseEnd_694895 : Nat := 158584506402739535029663

theorem tailTrace_694895 : CollatzResearch.WordTrace tailWord_694895 prefixEnd_694895 158584506402739535029663 := by
  unfold tailWord_694895
  simp only [CollatzResearch.WordTrace]
  refine ⟨25344902817521568462622139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16896601878347712308414759 25344902817521568462622139)
  ·
    refine ⟨38017354226282352693933209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25344902817521568462622139 38017354226282352693933209)
    ·
      refine ⟨28513015669711764520449907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38017354226282352693933209 28513015669711764520449907)
      ·
        refine ⟨42769523504567646780674861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28513015669711764520449907 42769523504567646780674861)
        ·
          refine ⟨16038571314212867542753073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42769523504567646780674861 16038571314212867542753073)
          ·
            refine ⟨12028928485659650657064805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16038571314212867542753073 12028928485659650657064805)
            ·
              refine ⟨2255424091061184498199651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12028928485659650657064805 2255424091061184498199651)
              ·
                refine ⟨3383136136591776747299477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255424091061184498199651 3383136136591776747299477)
                ·
                  refine ⟨158584506402739535029663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3383136136591776747299477 158584506402739535029663)
                  ·
                    rfl

theorem cell21_694895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_694895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694895 prefixEnd_694895 := by exact prefixLift 694895
  have htrace : WordTrace (prefixWord ++ tailWord_694895) baseStart_694895 baseEnd_694895 := by
    simpa [prefixWord, tailWord_694895, baseEnd_694895] using wordTrace_append hprefix tailTrace_694895
  have hstable : (prefixWord ++ tailWord_694895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694895).length < 2 ^ (prefixWord ++ tailWord_694895).sum := by decide
  have hdescent : baseEnd_694895 < baseStart_694895 := by decide
  rcases family_descends (prefixWord ++ tailWord_694895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694912 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 4]
def baseStart_694912 : Nat := 118140960795 + 694912 * 2 ^ 59
def prefixEnd_694912 : Nat := 4983230072969 + 3 ^ 40 * 694912 * 2
def baseEnd_694912 : Nat := 158588386034351283246295

theorem tailTrace_694912 : CollatzResearch.WordTrace tailWord_694912 prefixEnd_694912 158588386034351283246295 := by
  unfold tailWord_694912
  simp only [CollatzResearch.WordTrace]
  refine ⟨12672761429229990182995495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16897015238973320243993993 12672761429229990182995495)
  ·
    refine ⟨19009142143844985274493243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12672761429229990182995495 19009142143844985274493243)
    ·
      refine ⟨28513713215767477911739865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19009142143844985274493243 28513713215767477911739865)
      ·
        refine ⟨21385284911825608433804899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28513713215767477911739865 21385284911825608433804899)
        ·
          refine ⟨32077927367738412650707349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21385284911825608433804899 32077927367738412650707349)
          ·
            refine ⟨1503652845362738093001907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32077927367738412650707349 1503652845362738093001907)
            ·
              refine ⟨2255479268044107139502861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503652845362738093001907 2255479268044107139502861)
              ·
                refine ⟨845804725516540177313573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2255479268044107139502861 845804725516540177313573)
                ·
                  refine ⟨158588386034351283246295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 845804725516540177313573 158588386034351283246295)
                  ·
                    rfl

theorem cell21_694912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_694912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694912 prefixEnd_694912 := by exact prefixLift 694912
  have htrace : WordTrace (prefixWord ++ tailWord_694912) baseStart_694912 baseEnd_694912 := by
    simpa [prefixWord, tailWord_694912, baseEnd_694912] using wordTrace_append hprefix tailTrace_694912
  have hstable : (prefixWord ++ tailWord_694912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694912).length < 2 ^ (prefixWord ++ tailWord_694912).sum := by decide
  have hdescent : baseEnd_694912 < baseStart_694912 := by decide
  rcases family_descends (prefixWord ++ tailWord_694912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694926 : List Nat := [4, 1, 1, 3, 1, 1, 1, 9]
def baseStart_694926 : Nat := 118140960795 + 694926 * 2 ^ 59
def prefixEnd_694926 : Nat := 4983230072969 + 3 ^ 40 * 694926 * 2
def baseEnd_694926 : Nat := 52863860341696790004311

theorem tailTrace_694926 : CollatzResearch.WordTrace tailWord_694926 prefixEnd_694926 52863860341696790004311 := by
  unfold tailWord_694926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3168254185051157594625079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16897355653606173838000421 3168254185051157594625079)
  ·
    refine ⟨4752381277576736391937619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3168254185051157594625079 4752381277576736391937619)
    ·
      refine ⟨7128571916365104587906429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4752381277576736391937619 7128571916365104587906429)
      ·
        refine ⟨2673214468636914220464911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7128571916365104587906429 2673214468636914220464911)
        ·
          refine ⟨4009821702955371330697367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2673214468636914220464911 4009821702955371330697367)
          ·
            refine ⟨6014732554433056996046051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009821702955371330697367 6014732554433056996046051)
            ·
              refine ⟨9022098831649585494069077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6014732554433056996046051 9022098831649585494069077)
              ·
                refine ⟨52863860341696790004311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9022098831649585494069077 52863860341696790004311)
                ·
                  rfl

theorem cell21_694926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_694926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694926 prefixEnd_694926 := by exact prefixLift 694926
  have htrace : WordTrace (prefixWord ++ tailWord_694926) baseStart_694926 baseEnd_694926 := by
    simpa [prefixWord, tailWord_694926, baseEnd_694926] using wordTrace_append hprefix tailTrace_694926
  have hstable : (prefixWord ++ tailWord_694926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694926).length < 2 ^ (prefixWord ++ tailWord_694926).sum := by decide
  have hdescent : baseEnd_694926 < baseStart_694926 := by decide
  rcases family_descends (prefixWord ++ tailWord_694926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694977 : List Nat := [1, 2, 6, 2, 1, 1, 3, 5]
def baseStart_694977 : Nat := 118140960795 + 694977 * 2 ^ 59
def prefixEnd_694977 : Nat := 4983230072969 + 3 ^ 40 * 694977 * 2
def baseEnd_694977 : Nat := 52867739973308538220943

theorem tailTrace_694977 : CollatzResearch.WordTrace tailWord_694977 prefixEnd_694977 52867739973308538220943 := by
  unfold tailWord_694977
  simp only [CollatzResearch.WordTrace]
  refine ⟨25347893603224496467107185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16898595735482997644738123 25347893603224496467107185)
  ·
    refine ⟨19010920202418372350330389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25347893603224496467107185 19010920202418372350330389)
    ·
      refine ⟨891136884488361203921737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19010920202418372350330389 891136884488361203921737)
      ·
        refine ⟨668352663366270902941303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 891136884488361203921737 668352663366270902941303)
        ·
          refine ⟨1002528995049406354411955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668352663366270902941303 1002528995049406354411955)
          ·
            refine ⟨1503793492574109531617933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002528995049406354411955 1503793492574109531617933)
            ·
              refine ⟨563922559715291074356725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1503793492574109531617933 563922559715291074356725)
              ·
                refine ⟨52867739973308538220943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 563922559715291074356725 52867739973308538220943)
                ·
                  rfl

theorem cell21_694977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 5].length) (baseStart_694977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_694977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_694977 prefixEnd_694977 := by exact prefixLift 694977
  have htrace : WordTrace (prefixWord ++ tailWord_694977) baseStart_694977 baseEnd_694977 := by
    simpa [prefixWord, tailWord_694977, baseEnd_694977] using wordTrace_append hprefix tailTrace_694977
  have hstable : (prefixWord ++ tailWord_694977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694977).length < 2 ^ (prefixWord ++ tailWord_694977).sum := by decide
  have hdescent : baseEnd_694977 < baseStart_694977 := by decide
  rcases family_descends (prefixWord ++ tailWord_694977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695137 : List Nat := [1, 2, 3, 1, 1, 1, 2, 10]
def baseStart_695137 : Nat := 118140960795 + 695137 * 2 ^ 59
def prefixEnd_695137 : Nat := 4983230072969 + 3 ^ 40 * 695137 * 2
def baseEnd_695137 : Nat := 52879911366600297331945

theorem tailTrace_695137 : CollatzResearch.WordTrace tailWord_695137 prefixEnd_695137 52879911366600297331945 := by
  unfold tailWord_695137
  simp only [CollatzResearch.WordTrace]
  refine ⟨25353729282644843792931665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16902486188429895861954443 25353729282644843792931665)
  ·
    refine ⟨19015296961983632844698749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25353729282644843792931665 19015296961983632844698749)
    ·
      refine ⟨7130736360743862316762031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19015296961983632844698749 7130736360743862316762031)
      ·
        refine ⟨10696104541115793475143047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7130736360743862316762031 10696104541115793475143047)
        ·
          refine ⟨16044156811673690212714571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10696104541115793475143047 16044156811673690212714571)
          ·
            refine ⟨24066235217510535319071857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16044156811673690212714571 24066235217510535319071857)
            ·
              refine ⟨18049676413132901489303893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24066235217510535319071857 18049676413132901489303893)
              ·
                refine ⟨52879911366600297331945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18049676413132901489303893 52879911366600297331945)
                ·
                  rfl

theorem cell21_695137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 10].length) (baseStart_695137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695137 prefixEnd_695137 := by exact prefixLift 695137
  have htrace : WordTrace (prefixWord ++ tailWord_695137) baseStart_695137 baseEnd_695137 := by
    simpa [prefixWord, tailWord_695137, baseEnd_695137] using wordTrace_append hprefix tailTrace_695137
  have hstable : (prefixWord ++ tailWord_695137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695137).length < 2 ^ (prefixWord ++ tailWord_695137).sum := by decide
  have hdescent : baseEnd_695137 < baseStart_695137 := by decide
  rcases family_descends (prefixWord ++ tailWord_695137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695140 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 4]
def baseStart_695140 : Nat := 118140960795 + 695140 * 2 ^ 59
def prefixEnd_695140 : Nat := 4983230072969 + 3 ^ 40 * 695140 * 2
def baseEnd_695140 : Nat := 158640418740673553445829

theorem tailTrace_695140 : CollatzResearch.WordTrace tailWord_695140 prefixEnd_695140 158640418740673553445829 := by
  unfold tailWord_695140
  simp only [CollatzResearch.WordTrace]
  refine ⟨12676919350816987652645437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16902559134422650203527249 12676919350816987652645437)
  ·
    refine ⟨4753844756556370369742039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12676919350816987652645437 4753844756556370369742039)
    ·
      refine ⟨7130767134834555554613059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4753844756556370369742039 7130767134834555554613059)
      ·
        refine ⟨10696150702251833331919589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7130767134834555554613059 10696150702251833331919589)
        ·
          refine ⟨2005528256672218749734923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10696150702251833331919589 2005528256672218749734923)
          ·
            refine ⟨3008292385008328124602385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005528256672218749734923 3008292385008328124602385)
            ·
              refine ⟨2256219288756246093451789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3008292385008328124602385 2256219288756246093451789)
              ·
                refine ⟨846082233283592285044421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2256219288756246093451789 846082233283592285044421)
                ·
                  refine ⟨158640418740673553445829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846082233283592285044421 158640418740673553445829)
                  ·
                    rfl

theorem cell21_695140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_695140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695140 prefixEnd_695140 := by exact prefixLift 695140
  have htrace : WordTrace (prefixWord ++ tailWord_695140) baseStart_695140 baseEnd_695140 := by
    simpa [prefixWord, tailWord_695140, baseEnd_695140] using wordTrace_append hprefix tailTrace_695140
  have hstable : (prefixWord ++ tailWord_695140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695140).length < 2 ^ (prefixWord ++ tailWord_695140).sum := by decide
  have hdescent : baseEnd_695140 < baseStart_695140 := by decide
  rcases family_descends (prefixWord ++ tailWord_695140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695222 : List Nat := [5, 1, 4, 1, 2, 1, 7]
def baseStart_695222 : Nat := 118140960795 + 695222 * 2 ^ 59
def prefixEnd_695222 : Nat := 4983230072969 + 3 ^ 40 * 695222 * 2
def baseEnd_695222 : Nat := 17628792473095514786555

theorem tailTrace_695222 : CollatzResearch.WordTrace tailWord_695222 prefixEnd_695222 17628792473095514786555 := by
  unfold tailWord_695222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1584801842958556456860995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16904552991557935539850613 1584801842958556456860995)
  ·
    refine ⟨2377202764437834685291493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1584801842958556456860995 2377202764437834685291493)
    ·
      refine ⟨445725518332094003492155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2377202764437834685291493 445725518332094003492155)
      ·
        refine ⟨668588277498141005238233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445725518332094003492155 668588277498141005238233)
        ·
          refine ⟨501441208123605753928675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668588277498141005238233 501441208123605753928675)
          ·
            refine ⟨752161812185408630893013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501441208123605753928675 752161812185408630893013)
            ·
              refine ⟨17628792473095514786555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 752161812185408630893013 17628792473095514786555)
              ·
                rfl

theorem cell21_695222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 7].length) (baseStart_695222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695222 prefixEnd_695222 := by exact prefixLift 695222
  have htrace : WordTrace (prefixWord ++ tailWord_695222) baseStart_695222 baseEnd_695222 := by
    simpa [prefixWord, tailWord_695222, baseEnd_695222] using wordTrace_append hprefix tailTrace_695222
  have hstable : (prefixWord ++ tailWord_695222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695222).length < 2 ^ (prefixWord ++ tailWord_695222).sum := by decide
  have hdescent : baseEnd_695222 < baseStart_695222 := by decide
  rcases family_descends (prefixWord ++ tailWord_695222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695236 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 5]
def baseStart_695236 : Nat := 118140960795 + 695236 * 2 ^ 59
def prefixEnd_695236 : Nat := 4983230072969 + 3 ^ 40 * 695236 * 2
def baseEnd_695236 : Nat := 158662327248598719845633

theorem tailTrace_695236 : CollatzResearch.WordTrace tailWord_695236 prefixEnd_695236 158662327248598719845633 := by
  unfold tailWord_695236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12678670054643091850392781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16904893406190789133857041 12678670054643091850392781)
  ·
    refine ⟨4754501270491159443897293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12678670054643091850392781 4754501270491159443897293)
    ·
      refine ⟨1782937976434184791461485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4754501270491159443897293 1782937976434184791461485)
      ·
        refine ⟨668601741162819296798057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1782937976434184791461485 668601741162819296798057)
        ·
          refine ⟨501451305872114472598543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668601741162819296798057 501451305872114472598543)
          ·
            refine ⟨752176958808171708897815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501451305872114472598543 752176958808171708897815)
            ·
              refine ⟨1128265438212257563346723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752176958808171708897815 1128265438212257563346723)
              ·
                refine ⟨1692398157318386345020085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128265438212257563346723 1692398157318386345020085)
                ·
                  refine ⟨158662327248598719845633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1692398157318386345020085 158662327248598719845633)
                  ·
                    rfl

theorem cell21_695236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_695236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695236 prefixEnd_695236 := by exact prefixLift 695236
  have htrace : WordTrace (prefixWord ++ tailWord_695236) baseStart_695236 baseEnd_695236 := by
    simpa [prefixWord, tailWord_695236, baseEnd_695236] using wordTrace_append hprefix tailTrace_695236
  have hstable : (prefixWord ++ tailWord_695236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695236).length < 2 ^ (prefixWord ++ tailWord_695236).sum := by decide
  have hdescent : baseEnd_695236 < baseStart_695236 := by decide
  rcases family_descends (prefixWord ++ tailWord_695236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695250 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_695250 : Nat := 118140960795 + 695250 * 2 ^ 59
def prefixEnd_695250 : Nat := 4983230072969 + 3 ^ 40 * 695250 * 2
def baseEnd_695250 : Nat := 158665522239337806612271

theorem tailTrace_695250 : CollatzResearch.WordTrace tailWord_695250 prefixEnd_695250 158665522239337806612271 := by
  unfold tailWord_695250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6339462682808866022948801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16905233820823642727863469 6339462682808866022948801)
  ·
    refine ⟨4754597012106649517211601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6339462682808866022948801 4754597012106649517211601)
    ·
      refine ⟨3565947759079987137908701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4754597012106649517211601 3565947759079987137908701)
      ·
        refine ⟨1337230409654995176715763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3565947759079987137908701 1337230409654995176715763)
        ·
          refine ⟨2005845614482492765073645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337230409654995176715763 2005845614482492765073645)
          ·
            refine ⟨752192105430934786902617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2005845614482492765073645 752192105430934786902617)
            ·
              refine ⟨564144079073201090176963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752192105430934786902617 564144079073201090176963)
              ·
                refine ⟨846216118609801635265445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564144079073201090176963 846216118609801635265445)
                ·
                  refine ⟨158665522239337806612271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846216118609801635265445 158665522239337806612271)
                  ·
                    rfl

theorem cell21_695250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_695250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695250 prefixEnd_695250 := by exact prefixLift 695250
  have htrace : WordTrace (prefixWord ++ tailWord_695250) baseStart_695250 baseEnd_695250 := by
    simpa [prefixWord, tailWord_695250, baseEnd_695250] using wordTrace_append hprefix tailTrace_695250
  have hstable : (prefixWord ++ tailWord_695250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695250).length < 2 ^ (prefixWord ++ tailWord_695250).sum := by decide
  have hdescent : baseEnd_695250 < baseStart_695250 := by decide
  rcases family_descends (prefixWord ++ tailWord_695250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695284 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 4]
def baseStart_695284 : Nat := 118140960795 + 695284 * 2 ^ 59
def prefixEnd_695284 : Nat := 4983230072969 + 3 ^ 40 * 695284 * 2
def baseEnd_695284 : Nat := 158673281502561303045535

theorem tailTrace_695284 : CollatzResearch.WordTrace tailWord_695284 prefixEnd_695284 158673281502561303045535 := by
  unfold tailWord_695284
  simp only [CollatzResearch.WordTrace]
  refine ⟨12679545406556143949266453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16906060542074858599021937 12679545406556143949266453)
  ·
    refine ⟨594353690932319247621865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12679545406556143949266453 594353690932319247621865)
    ·
      refine ⟨445765268199239435716399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 594353690932319247621865 445765268199239435716399)
      ·
        refine ⟨668647902298859153574599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445765268199239435716399 668647902298859153574599)
        ·
          refine ⟨1002971853448288730361899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668647902298859153574599 1002971853448288730361899)
          ·
            refine ⟨1504457780172433095542849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002971853448288730361899 1504457780172433095542849)
            ·
              refine ⟨1128343335129324821657137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504457780172433095542849 1128343335129324821657137)
              ·
                refine ⟨846257501346993616242853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128343335129324821657137 846257501346993616242853)
                ·
                  refine ⟨158673281502561303045535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846257501346993616242853 158673281502561303045535)
                  ·
                    rfl

theorem cell21_695284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_695284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695284 prefixEnd_695284 := by exact prefixLift 695284
  have htrace : WordTrace (prefixWord ++ tailWord_695284) baseStart_695284 baseEnd_695284 := by
    simpa [prefixWord, tailWord_695284, baseEnd_695284] using wordTrace_append hprefix tailTrace_695284
  have hstable : (prefixWord ++ tailWord_695284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695284).length < 2 ^ (prefixWord ++ tailWord_695284).sum := by decide
  have hdescent : baseEnd_695284 < baseStart_695284 := by decide
  rcases family_descends (prefixWord ++ tailWord_695284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695292 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 4]
def baseStart_695292 : Nat := 118140960795 + 695292 * 2 ^ 59
def prefixEnd_695292 : Nat := 4983230072969 + 3 ^ 40 * 695292 * 2
def baseEnd_695292 : Nat := 158675107211555066912185

theorem tailTrace_695292 : CollatzResearch.WordTrace tailWord_695292 prefixEnd_695292 158675107211555066912185 := by
  unfold tailWord_695292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12679691298541652632412065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16906255064722203509882753 12679691298541652632412065)
  ·
    refine ⟨9509768473906239474309049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12679691298541652632412065 9509768473906239474309049)
    ·
      refine ⟨7132326355429679605731787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9509768473906239474309049 7132326355429679605731787)
      ·
        refine ⟨10698489533144519408597681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7132326355429679605731787 10698489533144519408597681)
        ·
          refine ⟨8023867149858389556448261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10698489533144519408597681 8023867149858389556448261)
          ·
            refine ⟨1504475090598448041834049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8023867149858389556448261 1504475090598448041834049)
            ·
              refine ⟨1128356317948836031375537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504475090598448041834049 1128356317948836031375537)
              ·
                refine ⟨846267238461627023531653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128356317948836031375537 846267238461627023531653)
                ·
                  refine ⟨158675107211555066912185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846267238461627023531653 158675107211555066912185)
                  ·
                    rfl

theorem cell21_695292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_695292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695292 prefixEnd_695292 := by exact prefixLift 695292
  have htrace : WordTrace (prefixWord ++ tailWord_695292) baseStart_695292 baseEnd_695292 := by
    simpa [prefixWord, tailWord_695292, baseEnd_695292] using wordTrace_append hprefix tailTrace_695292
  have hstable : (prefixWord ++ tailWord_695292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695292).length < 2 ^ (prefixWord ++ tailWord_695292).sum := by decide
  have hdescent : baseEnd_695292 < baseStart_695292 := by decide
  rcases family_descends (prefixWord ++ tailWord_695292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695306 : List Nat := [3, 1, 2, 2, 3, 1, 3, 6]
def baseStart_695306 : Nat := 118140960795 + 695306 * 2 ^ 59
def prefixEnd_695306 : Nat := 4983230072969 + 3 ^ 40 * 695306 * 2
def baseEnd_695306 : Nat := 52892767400764717892941

theorem tailTrace_695306 : CollatzResearch.WordTrace tailWord_695306 prefixEnd_695306 52892767400764717892941 := by
  unfold tailWord_695306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6339973304758146413958443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16906595479355057103889181 6339973304758146413958443)
  ·
    refine ⟨9509959957137219620937665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6339973304758146413958443 9509959957137219620937665)
    ·
      refine ⟨7132469967852914715703249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9509959957137219620937665 7132469967852914715703249)
      ·
        refine ⟨5349352475889686036777437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7132469967852914715703249 5349352475889686036777437)
        ·
          refine ⟨2006007178458632263791539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5349352475889686036777437 2006007178458632263791539)
          ·
            refine ⟨3009010767687948395687309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006007178458632263791539 3009010767687948395687309)
            ·
              refine ⟨1128379037882980648382741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3009010767687948395687309 1128379037882980648382741)
              ·
                refine ⟨52892767400764717892941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1128379037882980648382741 52892767400764717892941)
                ·
                  rfl

theorem cell21_695306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_695306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695306 prefixEnd_695306 := by exact prefixLift 695306
  have htrace : WordTrace (prefixWord ++ tailWord_695306) baseStart_695306 baseEnd_695306 := by
    simpa [prefixWord, tailWord_695306, baseEnd_695306] using wordTrace_append hprefix tailTrace_695306
  have hstable : (prefixWord ++ tailWord_695306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695306).length < 2 ^ (prefixWord ++ tailWord_695306).sum := by decide
  have hdescent : baseEnd_695306 < baseStart_695306 := by decide
  rcases family_descends (prefixWord ++ tailWord_695306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695320 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_695320 : Nat := 118140960795 + 695320 * 2 ^ 59
def prefixEnd_695320 : Nat := 4983230072969 + 3 ^ 40 * 695320 * 2
def baseEnd_695320 : Nat := 158681497193033240445461

theorem tailTrace_695320 : CollatzResearch.WordTrace tailWord_695320 prefixEnd_695320 158681497193033240445461 := by
  unfold tailWord_695320
  simp only [CollatzResearch.WordTrace]
  refine ⟨12680201920490933023421707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16906935893987910697895609 12680201920490933023421707)
  ·
    refine ⟨19020302880736399535132561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12680201920490933023421707 19020302880736399535132561)
    ·
      refine ⟨14265227160552299651349421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19020302880736399535132561 14265227160552299651349421)
      ·
        refine ⟨5349460185207112369256033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14265227160552299651349421 5349460185207112369256033)
        ·
          refine ⟨4012095138905334276942025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5349460185207112369256033 4012095138905334276942025)
          ·
            refine ⟨3009071354179000707706519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4012095138905334276942025 3009071354179000707706519)
            ·
              refine ⟨4513607031268501061559779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009071354179000707706519 4513607031268501061559779)
              ·
                refine ⟨6770410546902751592339669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513607031268501061559779 6770410546902751592339669)
                ·
                  refine ⟨158681497193033240445461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6770410546902751592339669 158681497193033240445461)
                  ·
                    rfl

theorem cell21_695320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_695320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695320 prefixEnd_695320 := by exact prefixLift 695320
  have htrace : WordTrace (prefixWord ++ tailWord_695320) baseStart_695320 baseEnd_695320 := by
    simpa [prefixWord, tailWord_695320, baseEnd_695320] using wordTrace_append hprefix tailTrace_695320
  have hstable : (prefixWord ++ tailWord_695320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695320).length < 2 ^ (prefixWord ++ tailWord_695320).sum := by decide
  have hdescent : baseEnd_695320 < baseStart_695320 := by decide
  rcases family_descends (prefixWord ++ tailWord_695320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695368 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 4]
def baseStart_695368 : Nat := 118140960795 + 695368 * 2 ^ 59
def prefixEnd_695368 : Nat := 4983230072969 + 3 ^ 40 * 695368 * 2
def baseEnd_695368 : Nat := 158692451446995823645363

theorem tailTrace_695368 : CollatzResearch.WordTrace tailWord_695368 prefixEnd_695368 158692451446995823645363 := by
  unfold tailWord_695368
  simp only [CollatzResearch.WordTrace]
  refine ⟨12681077272403985122295379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16908103029871980163060505 12681077272403985122295379)
  ·
    refine ⟨19021615908605977683443069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12681077272403985122295379 19021615908605977683443069)
    ·
      refine ⟨7133105965727241631291151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19021615908605977683443069 7133105965727241631291151)
      ·
        refine ⟨10699658948590862446936727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7133105965727241631291151 10699658948590862446936727)
        ·
          refine ⟨16049488422886293670405091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10699658948590862446936727 16049488422886293670405091)
          ·
            refine ⟨24074232634329440505607637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16049488422886293670405091 24074232634329440505607637)
            ·
              refine ⟨564239827367096261850179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24074232634329440505607637 564239827367096261850179)
              ·
                refine ⟨846359741050644392775269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564239827367096261850179 846359741050644392775269)
                ·
                  refine ⟨158692451446995823645363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846359741050644392775269 158692451446995823645363)
                  ·
                    rfl

theorem cell21_695368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_695368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695368 prefixEnd_695368 := by exact prefixLift 695368
  have htrace : WordTrace (prefixWord ++ tailWord_695368) baseStart_695368 baseEnd_695368 := by
    simpa [prefixWord, tailWord_695368, baseEnd_695368] using wordTrace_append hprefix tailTrace_695368
  have hstable : (prefixWord ++ tailWord_695368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695368).length < 2 ^ (prefixWord ++ tailWord_695368).sum := by decide
  have hdescent : baseEnd_695368 < baseStart_695368 := by decide
  rcases family_descends (prefixWord ++ tailWord_695368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695427 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 4]
def baseStart_695427 : Nat := 118140960795 + 695427 * 2 ^ 59
def prefixEnd_695427 : Nat := 4983230072969 + 3 ^ 40 * 695427 * 2
def baseEnd_695427 : Nat := 158705916050824832161909

theorem tailTrace_695427 : CollatzResearch.WordTrace tailWord_695427 prefixEnd_695427 158705916050824832161909 := by
  unfold tailWord_695427
  simp only [CollatzResearch.WordTrace]
  refine ⟨25364306451594223320988535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16909537634396148880659023 25364306451594223320988535)
  ·
    refine ⟨38046459677391334981482803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25364306451594223320988535 38046459677391334981482803)
    ·
      refine ⟨57069689516087002472224205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38046459677391334981482803 57069689516087002472224205)
      ·
        refine ⟨21401133568532625927084077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57069689516087002472224205 21401133568532625927084077)
        ·
          refine ⟨8025425088199734722656529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21401133568532625927084077 8025425088199734722656529)
          ·
            refine ⟨6019068816149801041992397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8025425088199734722656529 6019068816149801041992397)
            ·
              refine ⟨2257150806056175390747149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6019068816149801041992397 2257150806056175390747149)
              ·
                refine ⟨846431552271065771530181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2257150806056175390747149 846431552271065771530181)
                ·
                  refine ⟨158705916050824832161909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846431552271065771530181 158705916050824832161909)
                  ·
                    rfl

theorem cell21_695427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 4].length) (baseStart_695427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695427 prefixEnd_695427 := by exact prefixLift 695427
  have htrace : WordTrace (prefixWord ++ tailWord_695427) baseStart_695427 baseEnd_695427 := by
    simpa [prefixWord, tailWord_695427, baseEnd_695427] using wordTrace_append hprefix tailTrace_695427
  have hstable : (prefixWord ++ tailWord_695427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695427).length < 2 ^ (prefixWord ++ tailWord_695427).sum := by decide
  have hdescent : baseEnd_695427 < baseStart_695427 := by decide
  rcases family_descends (prefixWord ++ tailWord_695427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695458 : List Nat := [3, 3, 1, 3, 2, 9]
def baseStart_695458 : Nat := 118140960795 + 695458 * 2 ^ 59
def prefixEnd_695458 : Nat := 4983230072969 + 3 ^ 40 * 695458 * 2
def baseEnd_695458 : Nat := 5878258913821321005377

theorem tailTrace_695458 : CollatzResearch.WordTrace tailWord_695458 prefixEnd_695458 5878258913821321005377 := by
  unfold tailWord_695458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341359278620478903841757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16910291409654610410244685 6341359278620478903841757)
  ·
    refine ⟨2378009729482679588940659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6341359278620478903841757 2378009729482679588940659)
    ·
      refine ⟨3567014594224019383410989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2378009729482679588940659 3567014594224019383410989)
      ·
        refine ⟨1337630472834007268779121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3567014594224019383410989 1337630472834007268779121)
        ·
          refine ⟨1003222854625505451584341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1337630472834007268779121 1003222854625505451584341)
          ·
            refine ⟨5878258913821321005377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1003222854625505451584341 5878258913821321005377)
            ·
              rfl

theorem cell21_695458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 9].length) (baseStart_695458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695458 prefixEnd_695458 := by exact prefixLift 695458
  have htrace : WordTrace (prefixWord ++ tailWord_695458) baseStart_695458 baseEnd_695458 := by
    simpa [prefixWord, tailWord_695458, baseEnd_695458] using wordTrace_append hprefix tailTrace_695458
  have hstable : (prefixWord ++ tailWord_695458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695458).length < 2 ^ (prefixWord ++ tailWord_695458).sum := by decide
  have hdescent : baseEnd_695458 < baseStart_695458 := by decide
  rcases family_descends (prefixWord ++ tailWord_695458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695489 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 7]
def baseStart_695489 : Nat := 118140960795 + 695489 * 2 ^ 59
def prefixEnd_695489 : Nat := 4983230072969 + 3 ^ 40 * 695489 * 2
def baseEnd_695489 : Nat := 158720065295526502128449

theorem tailTrace_695489 : CollatzResearch.WordTrace tailWord_695489 prefixEnd_695489 158720065295526502128449 := by
  unfold tailWord_695489
  simp only [CollatzResearch.WordTrace]
  refine ⟨25366567777369607909745521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16911045184913071939830347 25366567777369607909745521)
  ·
    refine ⟨19024925833027205932309141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25366567777369607909745521 19024925833027205932309141)
    ·
      refine ⟨891793398423150278076991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19024925833027205932309141 891793398423150278076991)
      ·
        refine ⟨1337690097634725417115487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891793398423150278076991 1337690097634725417115487)
        ·
          refine ⟨2006535146452088125673231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337690097634725417115487 2006535146452088125673231)
          ·
            refine ⟨3009802719678132188509847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006535146452088125673231 3009802719678132188509847)
            ·
              refine ⟨4514704079517198282764771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009802719678132188509847 4514704079517198282764771)
              ·
                refine ⟨6772056119275797424147157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4514704079517198282764771 6772056119275797424147157)
                ·
                  refine ⟨158720065295526502128449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6772056119275797424147157 158720065295526502128449)
                  ·
                    rfl

theorem cell21_695489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_695489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695489 prefixEnd_695489 := by exact prefixLift 695489
  have htrace : WordTrace (prefixWord ++ tailWord_695489) baseStart_695489 baseEnd_695489 := by
    simpa [prefixWord, tailWord_695489, baseEnd_695489] using wordTrace_append hprefix tailTrace_695489
  have hstable : (prefixWord ++ tailWord_695489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695489).length < 2 ^ (prefixWord ++ tailWord_695489).sum := by decide
  have hdescent : baseEnd_695489 < baseStart_695489 := by decide
  rcases family_descends (prefixWord ++ tailWord_695489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695506 : List Nat := [3, 2, 2, 2, 1, 1, 4, 3, 3]
def baseStart_695506 : Nat := 118140960795 + 695506 * 2 ^ 59
def prefixEnd_695506 : Nat := 4983230072969 + 3 ^ 40 * 695506 * 2
def baseEnd_695506 : Nat := 158723944927138250345081

theorem tailTrace_695506 : CollatzResearch.WordTrace tailWord_695506 prefixEnd_695506 158723944927138250345081 := by
  unfold tailWord_695506
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341796954577004953278593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16911458545538679875409581 6341796954577004953278593)
  ·
    refine ⟨4756347715932753714958945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6341796954577004953278593 4756347715932753714958945)
    ·
      refine ⟨3567260786949565286219209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4756347715932753714958945 3567260786949565286219209)
      ·
        refine ⟨2675445590212173964664407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3567260786949565286219209 2675445590212173964664407)
        ·
          refine ⟨4013168385318260946996611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675445590212173964664407 4013168385318260946996611)
          ·
            refine ⟨6019752577977391420494917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4013168385318260946996611 6019752577977391420494917)
            ·
              refine ⟨1128703608370760891342797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6019752577977391420494917 1128703608370760891342797)
              ·
                refine ⟨423263853139035334253549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1128703608370760891342797 423263853139035334253549)
                ·
                  refine ⟨158723944927138250345081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423263853139035334253549 158723944927138250345081)
                  ·
                    rfl

theorem cell21_695506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_695506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695506 prefixEnd_695506 := by exact prefixLift 695506
  have htrace : WordTrace (prefixWord ++ tailWord_695506) baseStart_695506 baseEnd_695506 := by
    simpa [prefixWord, tailWord_695506, baseEnd_695506] using wordTrace_append hprefix tailTrace_695506
  have hstable : (prefixWord ++ tailWord_695506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695506).length < 2 ^ (prefixWord ++ tailWord_695506).sum := by decide
  have hdescent : baseEnd_695506 < baseStart_695506 := by decide
  rcases family_descends (prefixWord ++ tailWord_695506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695520 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 4]
def baseStart_695520 : Nat := 118140960795 + 695520 * 2 ^ 59
def prefixEnd_695520 : Nat := 4983230072969 + 3 ^ 40 * 695520 * 2
def baseEnd_695520 : Nat := 158727139917877337111719

theorem tailTrace_695520 : CollatzResearch.WordTrace tailWord_695520 prefixEnd_695520 158727139917877337111719 := by
  unfold tailWord_695520
  simp only [CollatzResearch.WordTrace]
  refine ⟨12683849220128650102062007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16911798960171533469416009 12683849220128650102062007)
  ·
    refine ⟨19025773830192975153093011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12683849220128650102062007 19025773830192975153093011)
    ·
      refine ⟨28538660745289462729639517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19025773830192975153093011 28538660745289462729639517)
      ·
        refine ⟨10701997779483548523614819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28538660745289462729639517 10701997779483548523614819)
        ·
          refine ⟨16052996669225322785422229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10701997779483548523614819 16052996669225322785422229)
          ·
            refine ⟨752484218869937005566667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16052996669225322785422229 752484218869937005566667)
            ·
              refine ⟨1128726328304905508350001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752484218869937005566667 1128726328304905508350001)
              ·
                refine ⟨846544746228679131262501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128726328304905508350001 846544746228679131262501)
                ·
                  refine ⟨158727139917877337111719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846544746228679131262501 158727139917877337111719)
                  ·
                    rfl

theorem cell21_695520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_695520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695520 prefixEnd_695520 := by exact prefixLift 695520
  have htrace : WordTrace (prefixWord ++ tailWord_695520) baseStart_695520 baseEnd_695520 := by
    simpa [prefixWord, tailWord_695520, baseEnd_695520] using wordTrace_append hprefix tailTrace_695520
  have hstable : (prefixWord ++ tailWord_695520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695520).length < 2 ^ (prefixWord ++ tailWord_695520).sum := by decide
  have hdescent : baseEnd_695520 < baseStart_695520 := by decide
  rcases family_descends (prefixWord ++ tailWord_695520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695689 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 4]
def baseStart_695689 : Nat := 118140960795 + 695689 * 2 ^ 59
def prefixEnd_695689 : Nat := 4983230072969 + 3 ^ 40 * 695689 * 2
def baseEnd_695689 : Nat := 158765708020370598794707

theorem tailTrace_695689 : CollatzResearch.WordTrace tailWord_695689 prefixEnd_695689 158765708020370598794707 := by
  unfold tailWord_695689
  simp only [CollatzResearch.WordTrace]
  refine ⟨25373862376645042067026121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16915908251096694711350747 25373862376645042067026121)
  ·
    refine ⟨19030396782483781550269591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25373862376645042067026121 19030396782483781550269591)
    ·
      refine ⟨28545595173725672325404387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19030396782483781550269591 28545595173725672325404387)
      ·
        refine ⟨42818392760588508488106581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28545595173725672325404387 42818392760588508488106581)
        ·
          refine ⟨501778040163146583844999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 42818392760588508488106581 501778040163146583844999)
          ·
            refine ⟨752667060244719875767499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501778040163146583844999 752667060244719875767499)
            ·
              refine ⟨1129000590367079813651249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752667060244719875767499 1129000590367079813651249)
              ·
                refine ⟨846750442775309860238437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129000590367079813651249 846750442775309860238437)
                ·
                  refine ⟨158765708020370598794707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846750442775309860238437 158765708020370598794707)
                  ·
                    rfl

theorem cell21_695689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 4].length) (baseStart_695689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695689 prefixEnd_695689 := by exact prefixLift 695689
  have htrace : WordTrace (prefixWord ++ tailWord_695689) baseStart_695689 baseEnd_695689 := by
    simpa [prefixWord, tailWord_695689, baseEnd_695689] using wordTrace_append hprefix tailTrace_695689
  have hstable : (prefixWord ++ tailWord_695689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695689).length < 2 ^ (prefixWord ++ tailWord_695689).sum := by decide
  have hdescent : baseEnd_695689 < baseStart_695689 := by decide
  rcases family_descends (prefixWord ++ tailWord_695689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695720 : List Nat := [2, 1, 6, 1, 2, 2, 2, 5]
def baseStart_695720 : Nat := 118140960795 + 695720 * 2 ^ 59
def prefixEnd_695720 : Nat := 4983230072969 + 3 ^ 40 * 695720 * 2
def baseEnd_695720 : Nat := 52924260880907144592659

theorem tailTrace_695720 : CollatzResearch.WordTrace tailWord_695720 prefixEnd_695720 52924260880907144592659 := by
  unfold tailWord_695720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12687496519766367180702307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16916662026355156240936409 12687496519766367180702307)
  ·
    refine ⟨19031244779649550771053461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12687496519766367180702307 19031244779649550771053461)
    ·
      refine ⟨892089599046072692393131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19031244779649550771053461 892089599046072692393131)
      ·
        refine ⟨1338134398569109038589697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892089599046072692393131 1338134398569109038589697)
        ·
          refine ⟨1003600798926831778942273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1338134398569109038589697 1003600798926831778942273)
          ·
            refine ⟨752700599195123834206705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1003600798926831778942273 752700599195123834206705)
            ·
              refine ⟨564525449396342875655029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752700599195123834206705 564525449396342875655029)
              ·
                refine ⟨52924260880907144592659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 564525449396342875655029 52924260880907144592659)
                ·
                  rfl

theorem cell21_695720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_695720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695720 prefixEnd_695720 := by exact prefixLift 695720
  have htrace : WordTrace (prefixWord ++ tailWord_695720) baseStart_695720 baseEnd_695720 := by
    simpa [prefixWord, tailWord_695720, baseEnd_695720] using wordTrace_append hprefix tailTrace_695720
  have hstable : (prefixWord ++ tailWord_695720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695720).length < 2 ^ (prefixWord ++ tailWord_695720).sum := by decide
  have hdescent : baseEnd_695720 < baseStart_695720 := by decide
  rcases family_descends (prefixWord ++ tailWord_695720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695866 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_695866 : Nat := 118140960795 + 695866 * 2 ^ 59
def prefixEnd_695866 : Nat := 4983230072969 + 3 ^ 40 * 695866 * 2
def baseEnd_695866 : Nat := 158806101831857624344345

theorem tailTrace_695866 : CollatzResearch.WordTrace tailWord_695866 prefixEnd_695866 158806101831857624344345 := by
  unfold tailWord_695866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6345079524250950324054863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16920212064669200864146301 6345079524250950324054863)
  ·
    refine ⟨9517619286376425486082295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6345079524250950324054863 9517619286376425486082295)
    ·
      refine ⟨14276428929564638229123443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9517619286376425486082295 14276428929564638229123443)
      ·
        refine ⟨21414643394346957343685165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14276428929564638229123443 21414643394346957343685165)
        ·
          refine ⟨8030491272880109003881937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21414643394346957343685165 8030491272880109003881937)
          ·
            refine ⟨6022868454660081752911453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8030491272880109003881937 6022868454660081752911453)
            ·
              refine ⟨2258575670497530657341795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6022868454660081752911453 2258575670497530657341795)
              ·
                refine ⟨3387863505746295986012693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258575670497530657341795 3387863505746295986012693)
                ·
                  refine ⟨158806101831857624344345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3387863505746295986012693 158806101831857624344345)
                  ·
                    rfl

theorem cell21_695866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_695866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695866 prefixEnd_695866 := by exact prefixLift 695866
  have htrace : WordTrace (prefixWord ++ tailWord_695866) baseStart_695866 baseEnd_695866 := by
    simpa [prefixWord, tailWord_695866, baseEnd_695866] using wordTrace_append hprefix tailTrace_695866
  have hstable : (prefixWord ++ tailWord_695866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695866).length < 2 ^ (prefixWord ++ tailWord_695866).sum := by decide
  have hdescent : baseEnd_695866 < baseStart_695866 := by decide
  rcases family_descends (prefixWord ++ tailWord_695866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695869 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 5]
def baseStart_695869 : Nat := 118140960795 + 695869 * 2 ^ 59
def prefixEnd_695869 : Nat := 4983230072969 + 3 ^ 40 * 695869 * 2
def baseEnd_695869 : Nat := 158806786472730285794339

theorem tailTrace_695869 : CollatzResearch.WordTrace tailWord_695869 prefixEnd_695869 158806786472730285794339 := by
  unfold tailWord_695869
  simp only [CollatzResearch.WordTrace]
  refine ⟨25380427515992932808578661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16920285010661955205719107 25380427515992932808578661)
  ·
    refine ⟨4758830159248674901608499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25380427515992932808578661 4758830159248674901608499)
    ·
      refine ⟨7138245238873012352412749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4758830159248674901608499 7138245238873012352412749)
      ·
        refine ⟨2676841964577379632154781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7138245238873012352412749 2676841964577379632154781)
        ·
          refine ⟨1003815736716517362058043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2676841964577379632154781 1003815736716517362058043)
          ·
            refine ⟨1505723605074776043087065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003815736716517362058043 1505723605074776043087065)
            ·
              refine ⟨1129292703806082032315299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505723605074776043087065 1129292703806082032315299)
              ·
                refine ⟨1693939055709123048472949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129292703806082032315299 1693939055709123048472949)
                ·
                  refine ⟨158806786472730285794339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1693939055709123048472949 158806786472730285794339)
                  ·
                    rfl

theorem cell21_695869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_695869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695869 prefixEnd_695869 := by exact prefixLift 695869
  have htrace : WordTrace (prefixWord ++ tailWord_695869) baseStart_695869 baseEnd_695869 := by
    simpa [prefixWord, tailWord_695869, baseEnd_695869] using wordTrace_append hprefix tailTrace_695869
  have hstable : (prefixWord ++ tailWord_695869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695869).length < 2 ^ (prefixWord ++ tailWord_695869).sum := by decide
  have hdescent : baseEnd_695869 < baseStart_695869 := by decide
  rcases family_descends (prefixWord ++ tailWord_695869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695911 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 7]
def baseStart_695911 : Nat := 118140960795 + 695911 * 2 ^ 59
def prefixEnd_695911 : Nat := 4983230072969 + 3 ^ 40 * 695911 * 2
def baseEnd_695911 : Nat := 158816371444947546094253

theorem tailTrace_695911 : CollatzResearch.WordTrace tailWord_695911 prefixEnd_695911 158816371444947546094253 := by
  unfold tailWord_695911
  simp only [CollatzResearch.WordTrace]
  refine ⟨25381959381840773981607587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16921306254560515987738391 25381959381840773981607587)
  ·
    refine ⟨38072939072761160972411381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25381959381840773981607587 38072939072761160972411381)
    ·
      refine ⟨3569338038071358841163567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38072939072761160972411381 3569338038071358841163567)
      ·
        refine ⟨5354007057107038261745351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3569338038071358841163567 5354007057107038261745351)
        ·
          refine ⟨8031010585660557392618027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5354007057107038261745351 8031010585660557392618027)
          ·
            refine ⟨12046515878490836088927041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8031010585660557392618027 12046515878490836088927041)
            ·
              refine ⟨9034886908868127066695281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12046515878490836088927041 9034886908868127066695281)
              ·
                refine ⟨6776165181651095300021461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9034886908868127066695281 6776165181651095300021461)
                ·
                  refine ⟨158816371444947546094253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6776165181651095300021461 158816371444947546094253)
                  ·
                    rfl

theorem cell21_695911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_695911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695911 prefixEnd_695911 := by exact prefixLift 695911
  have htrace : WordTrace (prefixWord ++ tailWord_695911) baseStart_695911 baseEnd_695911 := by
    simpa [prefixWord, tailWord_695911, baseEnd_695911] using wordTrace_append hprefix tailTrace_695911
  have hstable : (prefixWord ++ tailWord_695911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695911).length < 2 ^ (prefixWord ++ tailWord_695911).sum := by decide
  have hdescent : baseEnd_695911 < baseStart_695911 := by decide
  rcases family_descends (prefixWord ++ tailWord_695911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695987 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 5]
def baseStart_695987 : Nat := 118140960795 + 695987 * 2 ^ 59
def prefixEnd_695987 : Nat := 4983230072969 + 3 ^ 40 * 695987 * 2
def baseEnd_695987 : Nat := 158833715680388302827431

theorem tailTrace_695987 : CollatzResearch.WordTrace tailWord_695987 prefixEnd_695987 158833715680388302827431 := by
  unfold tailWord_695987
  simp only [CollatzResearch.WordTrace]
  refine ⟨25384731329565438961374215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16923154219710292640916143 25384731329565438961374215)
  ·
    refine ⟨38077096994348158442061323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25384731329565438961374215 38077096994348158442061323)
    ·
      refine ⟨57115645491522237663091985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38077096994348158442061323 57115645491522237663091985)
      ·
        refine ⟨42836734118641678247318989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57115645491522237663091985 42836734118641678247318989)
        ·
          refine ⟨16063775294490629342744621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42836734118641678247318989 16063775294490629342744621)
          ·
            refine ⟨6023915735433986003529233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16063775294490629342744621 6023915735433986003529233)
            ·
              refine ⟨4517936801575489502646925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6023915735433986003529233 4517936801575489502646925)
              ·
                refine ⟨1694226300590808563492597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4517936801575489502646925 1694226300590808563492597)
                ·
                  refine ⟨158833715680388302827431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1694226300590808563492597 158833715680388302827431)
                  ·
                    rfl

theorem cell21_695987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_695987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_695987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_695987 prefixEnd_695987 := by exact prefixLift 695987
  have htrace : WordTrace (prefixWord ++ tailWord_695987) baseStart_695987 baseEnd_695987 := by
    simpa [prefixWord, tailWord_695987, baseEnd_695987] using wordTrace_append hprefix tailTrace_695987
  have hstable : (prefixWord ++ tailWord_695987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695987).length < 2 ^ (prefixWord ++ tailWord_695987).sum := by decide
  have hdescent : baseEnd_695987 < baseStart_695987 := by decide
  rcases family_descends (prefixWord ++ tailWord_695987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696004 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_696004 : Nat := 118140960795 + 696004 * 2 ^ 59
def prefixEnd_696004 : Nat := 4983230072969 + 3 ^ 40 * 696004 * 2
def baseEnd_696004 : Nat := 158837595312000051044063

theorem tailTrace_696004 : CollatzResearch.WordTrace tailWord_696004 prefixEnd_696004 158837595312000051044063 := by
  unfold tailWord_696004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12692675685251925432371533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16923567580335900576495377 12692675685251925432371533)
  ·
    refine ⟨4759753381969472037139325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12692675685251925432371533 4759753381969472037139325)
    ·
      refine ⟨1784907518238552013927247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4759753381969472037139325 1784907518238552013927247)
      ·
        refine ⟨2677361277357828020890871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784907518238552013927247 2677361277357828020890871)
        ·
          refine ⟨4016041916036742031336307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677361277357828020890871 4016041916036742031336307)
          ·
            refine ⟨6024062874055113047004461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016041916036742031336307 6024062874055113047004461)
            ·
              refine ⟨2259023577770667392626673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6024062874055113047004461 2259023577770667392626673)
              ·
                refine ⟨1694267683328000544470005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2259023577770667392626673 1694267683328000544470005)
                ·
                  refine ⟨158837595312000051044063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1694267683328000544470005 158837595312000051044063)
                  ·
                    rfl

theorem cell21_696004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_696004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696004 prefixEnd_696004 := by exact prefixLift 696004
  have htrace : WordTrace (prefixWord ++ tailWord_696004) baseStart_696004 baseEnd_696004 := by
    simpa [prefixWord, tailWord_696004, baseEnd_696004] using wordTrace_append hprefix tailTrace_696004
  have hstable : (prefixWord ++ tailWord_696004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696004).length < 2 ^ (prefixWord ++ tailWord_696004).sum := by decide
  have hdescent : baseEnd_696004 < baseStart_696004 := by decide
  rcases family_descends (prefixWord ++ tailWord_696004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696035 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 6]
def baseStart_696035 : Nat := 118140960795 + 696035 * 2 ^ 59
def prefixEnd_696035 : Nat := 4983230072969 + 3 ^ 40 * 696035 * 2
def baseEnd_696035 : Nat := 158844669934350886027333

theorem tailTrace_696035 : CollatzResearch.WordTrace tailWord_696035 prefixEnd_696035 158844669934350886027333 := by
  unfold tailWord_696035
  simp only [CollatzResearch.WordTrace]
  refine ⟨25386482033391543159121559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16924321355594362106081039 25386482033391543159121559)
  ·
    refine ⟨38079723050087314738682339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25386482033391543159121559 38079723050087314738682339)
    ·
      refine ⟨57119584575130972108023509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38079723050087314738682339 57119584575130972108023509)
      ·
        refine ⟨1338740263479632158781801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 57119584575130972108023509 1338740263479632158781801)
        ·
          refine ⟨1004055197609724119086351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1338740263479632158781801 1004055197609724119086351)
          ·
            refine ⟨1506082796414586178629527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004055197609724119086351 1506082796414586178629527)
            ·
              refine ⟨2259124194621879267944291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506082796414586178629527 2259124194621879267944291)
              ·
                refine ⟨3388686291932818901916437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259124194621879267944291 3388686291932818901916437)
                ·
                  refine ⟨158844669934350886027333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3388686291932818901916437 158844669934350886027333)
                  ·
                    rfl

theorem cell21_696035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 6].length) (baseStart_696035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696035 prefixEnd_696035 := by exact prefixLift 696035
  have htrace : WordTrace (prefixWord ++ tailWord_696035) baseStart_696035 baseEnd_696035 := by
    simpa [prefixWord, tailWord_696035, baseEnd_696035] using wordTrace_append hprefix tailTrace_696035
  have hstable : (prefixWord ++ tailWord_696035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696035).length < 2 ^ (prefixWord ++ tailWord_696035).sum := by decide
  have hdescent : baseEnd_696035 < baseStart_696035 := by decide
  rcases family_descends (prefixWord ++ tailWord_696035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696063 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 5]
def baseStart_696063 : Nat := 118140960795 + 696063 * 2 ^ 59
def prefixEnd_696063 : Nat := 4983230072969 + 3 ^ 40 * 696063 * 2
def baseEnd_696063 : Nat := 158851059915829059560609

theorem tailTrace_696063 : CollatzResearch.WordTrace tailWord_696063 prefixEnd_696063 158851059915829059560609 := by
  unfold tailWord_696063
  simp only [CollatzResearch.WordTrace]
  refine ⟨25387503277290103941140843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16925002184860069294093895 25387503277290103941140843)
  ·
    refine ⟨38081254915935155911711265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25387503277290103941140843 38081254915935155911711265)
    ·
      refine ⟨28560941186951366933783449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38081254915935155911711265 28560941186951366933783449)
      ·
        refine ⟨21420705890213525200337587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28560941186951366933783449 21420705890213525200337587)
        ·
          refine ⟨32131058835320287800506381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21420705890213525200337587 32131058835320287800506381)
          ·
            refine ⟨12049147063245107925189893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32131058835320287800506381 12049147063245107925189893)
            ·
              refine ⟨2259215074358457735973105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12049147063245107925189893 2259215074358457735973105)
              ·
                refine ⟨1694411305768843301979829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2259215074358457735973105 1694411305768843301979829)
                ·
                  refine ⟨158851059915829059560609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1694411305768843301979829 158851059915829059560609)
                  ·
                    rfl

theorem cell21_696063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_696063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696063 prefixEnd_696063 := by exact prefixLift 696063
  have htrace : WordTrace (prefixWord ++ tailWord_696063) baseStart_696063 baseEnd_696063 := by
    simpa [prefixWord, tailWord_696063, baseEnd_696063] using wordTrace_append hprefix tailTrace_696063
  have hstable : (prefixWord ++ tailWord_696063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696063).length < 2 ^ (prefixWord ++ tailWord_696063).sum := by decide
  have hdescent : baseEnd_696063 < baseStart_696063 := by decide
  rcases family_descends (prefixWord ++ tailWord_696063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696108 : List Nat := [2, 2, 1, 1, 1, 5, 1, 8]
def baseStart_696108 : Nat := 118140960795 + 696108 * 2 ^ 59
def prefixEnd_696108 : Nat := 4983230072969 + 3 ^ 40 * 696108 * 2
def baseEnd_696108 : Nat := 52953776509639660436839

theorem tailTrace_696108 : CollatzResearch.WordTrace tailWord_696108 prefixEnd_696108 52953776509639660436839 := by
  unfold tailWord_696108
  simp only [CollatzResearch.WordTrace]
  refine ⟨12694572281063538313264489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16926096374751384417685985 12694572281063538313264489)
  ·
    refine ⟨9520929210797653734948367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12694572281063538313264489 9520929210797653734948367)
    ·
      refine ⟨14281393816196480602422551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9520929210797653734948367 14281393816196480602422551)
      ·
        refine ⟨21422090724294720903633827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14281393816196480602422551 21422090724294720903633827)
        ·
          refine ⟨32133136086442081355450741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21422090724294720903633827 32133136086442081355450741)
          ·
            refine ⟨3012481508103945127073507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32133136086442081355450741 3012481508103945127073507)
            ·
              refine ⟨4518722262155917690610261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012481508103945127073507 4518722262155917690610261)
              ·
                refine ⟨52953776509639660436839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4518722262155917690610261 52953776509639660436839)
                ·
                  rfl

theorem cell21_696108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_696108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696108 prefixEnd_696108 := by exact prefixLift 696108
  have htrace : WordTrace (prefixWord ++ tailWord_696108) baseStart_696108 baseEnd_696108 := by
    simpa [prefixWord, tailWord_696108, baseEnd_696108] using wordTrace_append hprefix tailTrace_696108
  have hstable : (prefixWord ++ tailWord_696108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696108).length < 2 ^ (prefixWord ++ tailWord_696108).sum := by decide
  have hdescent : baseEnd_696108 < baseStart_696108 := by decide
  rcases family_descends (prefixWord ++ tailWord_696108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696125 : List Nat := [1, 4, 1, 4, 1, 1, 2, 7]
def baseStart_696125 : Nat := 118140960795 + 696125 * 2 ^ 59
def prefixEnd_696125 : Nat := 4983230072969 + 3 ^ 40 * 696125 * 2
def baseEnd_696125 : Nat := 52955069720176909842383

theorem tailTrace_696125 : CollatzResearch.WordTrace tailWord_696125 prefixEnd_696125 52955069720176909842383 := by
  unfold tailWord_696125
  simp only [CollatzResearch.WordTrace]
  refine ⟨25389764603065488529897829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16926509735376992353265219 25389764603065488529897829)
  ·
    refine ⟨4760580863074779099355843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25389764603065488529897829 4760580863074779099355843)
    ·
      refine ⟨7140871294612168649033765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4760580863074779099355843 7140871294612168649033765)
      ·
        refine ⟨1338913367739781621693831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7140871294612168649033765 1338913367739781621693831)
        ·
          refine ⟨2008370051609672432540747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1338913367739781621693831 2008370051609672432540747)
          ·
            refine ⟨3012555077414508648811121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008370051609672432540747 3012555077414508648811121)
            ·
              refine ⟨2259416308060881486608341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3012555077414508648811121 2259416308060881486608341)
              ·
                refine ⟨52955069720176909842383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2259416308060881486608341 52955069720176909842383)
                ·
                  rfl

theorem cell21_696125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 7].length) (baseStart_696125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696125 prefixEnd_696125 := by exact prefixLift 696125
  have htrace : WordTrace (prefixWord ++ tailWord_696125) baseStart_696125 baseEnd_696125 := by
    simpa [prefixWord, tailWord_696125, baseEnd_696125] using wordTrace_append hprefix tailTrace_696125
  have hstable : (prefixWord ++ tailWord_696125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696125).length < 2 ^ (prefixWord ++ tailWord_696125).sum := by decide
  have hdescent : baseEnd_696125 < baseStart_696125 := by decide
  rcases family_descends (prefixWord ++ tailWord_696125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696190 : List Nat := [4, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_696190 : Nat := 118140960795 + 696190 * 2 ^ 59
def prefixEnd_696190 : Nat := 4983230072969 + 3 ^ 40 * 696190 * 2
def baseEnd_696190 : Nat := 158880043046105060943683

theorem tailTrace_696190 : CollatzResearch.WordTrace tailWord_696190 prefixEnd_696190 158880043046105060943683 := by
  unfold tailWord_696190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3174016918478750578876753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16928090231886669754009349 3174016918478750578876753)
  ·
    refine ⟨2380512688859062934157565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3174016918478750578876753 2380512688859062934157565)
    ·
      refine ⟨892692258322148600309087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2380512688859062934157565 892692258322148600309087)
      ·
        refine ⟨1339038387483222900463631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892692258322148600309087 1339038387483222900463631)
        ·
          refine ⟨2008557581224834350695447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339038387483222900463631 2008557581224834350695447)
          ·
            refine ⟨3012836371837251526043171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008557581224834350695447 3012836371837251526043171)
            ·
              refine ⟨4519254557755877289064757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012836371837251526043171 4519254557755877289064757)
              ·
                refine ⟨423680114789613495849821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4519254557755877289064757 423680114789613495849821)
                ·
                  refine ⟨158880043046105060943683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423680114789613495849821 158880043046105060943683)
                  ·
                    rfl

theorem cell21_696190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_696190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696190 prefixEnd_696190 := by exact prefixLift 696190
  have htrace : WordTrace (prefixWord ++ tailWord_696190) baseStart_696190 baseEnd_696190 := by
    simpa [prefixWord, tailWord_696190, baseEnd_696190] using wordTrace_append hprefix tailTrace_696190
  have hstable : (prefixWord ++ tailWord_696190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696190).length < 2 ^ (prefixWord ++ tailWord_696190).sum := by decide
  have hdescent : baseEnd_696190 < baseStart_696190 := by decide
  rcases family_descends (prefixWord ++ tailWord_696190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696215 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 5]
def baseStart_696215 : Nat := 118140960795 + 696215 * 2 ^ 59
def prefixEnd_696215 : Nat := 4983230072969 + 3 ^ 40 * 696215 * 2
def baseEnd_696215 : Nat := 158885748386710573026965

theorem tailTrace_696215 : CollatzResearch.WordTrace tailWord_696215 prefixEnd_696215 158885748386710573026965 := by
  unfold tailWord_696215
  simp only [CollatzResearch.WordTrace]
  refine ⟨25393047172739433900674099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16928698115159622600449399 25393047172739433900674099)
  ·
    refine ⟨38089570759109150851011149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25393047172739433900674099 38089570759109150851011149)
    ·
      refine ⟨14283589034665931569129181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38089570759109150851011149 14283589034665931569129181)
      ·
        refine ⟨5356345887999724338423443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14283589034665931569129181 5356345887999724338423443)
        ·
          refine ⟨8034518831999586507635165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5356345887999724338423443 8034518831999586507635165)
          ·
            refine ⟨3012944561999844940363187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8034518831999586507635165 3012944561999844940363187)
            ·
              refine ⟨4519416842999767410544781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012944561999844940363187 4519416842999767410544781)
              ·
                refine ⟨1694781316124912778954293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4519416842999767410544781 1694781316124912778954293)
                ·
                  refine ⟨158885748386710573026965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1694781316124912778954293 158885748386710573026965)
                  ·
                    rfl

theorem cell21_696215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_696215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696215 prefixEnd_696215 := by exact prefixLift 696215
  have htrace : WordTrace (prefixWord ++ tailWord_696215) baseStart_696215 baseEnd_696215 := by
    simpa [prefixWord, tailWord_696215, baseEnd_696215] using wordTrace_append hprefix tailTrace_696215
  have hstable : (prefixWord ++ tailWord_696215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696215).length < 2 ^ (prefixWord ++ tailWord_696215).sum := by decide
  have hdescent : baseEnd_696215 < baseStart_696215 := by decide
  rcases family_descends (prefixWord ++ tailWord_696215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696277 : List Nat := [1, 3, 2, 3, 2, 2, 2, 6]
def baseStart_696277 : Nat := 118140960795 + 696277 * 2 ^ 59
def prefixEnd_696277 : Nat := 4983230072969 + 3 ^ 40 * 696277 * 2
def baseEnd_696277 : Nat := 52966632543804080997835

theorem tailTrace_696277 : CollatzResearch.WordTrace tailWord_696277 prefixEnd_696277 52966632543804080997835 := by
  unfold tailWord_696277
  simp only [CollatzResearch.WordTrace]
  refine ⟨25395308498514818489431085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16930205665676545659620723 25395308498514818489431085)
  ·
    refine ⟨9523240686943056933536657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25395308498514818489431085 9523240686943056933536657)
    ·
      refine ⟨7142430515207292700152493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9523240686943056933536657 7142430515207292700152493)
      ·
        refine ⟨2678411443202734762557185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7142430515207292700152493 2678411443202734762557185)
        ·
          refine ⟨2008808582402051071917889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2678411443202734762557185 2008808582402051071917889)
          ·
            refine ⟨1506606436801538303938417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2008808582402051071917889 1506606436801538303938417)
            ·
              refine ⟨1129954827601153727953813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1506606436801538303938417 1129954827601153727953813)
              ·
                refine ⟨52966632543804080997835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1129954827601153727953813 52966632543804080997835)
                ·
                  rfl

theorem cell21_696277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 6].length) (baseStart_696277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696277 prefixEnd_696277 := by exact prefixLift 696277
  have htrace : WordTrace (prefixWord ++ tailWord_696277) baseStart_696277 baseEnd_696277 := by
    simpa [prefixWord, tailWord_696277, baseEnd_696277] using wordTrace_append hprefix tailTrace_696277
  have hstable : (prefixWord ++ tailWord_696277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696277).length < 2 ^ (prefixWord ++ tailWord_696277).sum := by decide
  have hdescent : baseEnd_696277 < baseStart_696277 := by decide
  rcases family_descends (prefixWord ++ tailWord_696277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696325 : List Nat := [1, 3, 1, 1, 2, 4, 4, 2, 3]
def baseStart_696325 : Nat := 118140960795 + 696325 * 2 ^ 59
def prefixEnd_696325 : Nat := 4983230072969 + 3 ^ 40 * 696325 * 2
def baseEnd_696325 : Nat := 158910851885374826193407

theorem tailTrace_696325 : CollatzResearch.WordTrace tailWord_696325 prefixEnd_696325 158910851885374826193407 := by
  unfold tailWord_696325
  simp only [CollatzResearch.WordTrace]
  refine ⟨25397059202340922687178429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16931372801560615124785619 25397059202340922687178429)
  ·
    refine ⟨9523897200877846007691911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25397059202340922687178429 9523897200877846007691911)
    ·
      refine ⟨14285845801316769011537867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9523897200877846007691911 14285845801316769011537867)
      ·
        refine ⟨21428768701975153517306801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14285845801316769011537867 21428768701975153517306801)
        ·
          refine ⟨16071576526481365137980101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21428768701975153517306801 16071576526481365137980101)
          ·
            refine ⟨3013420598715255963371269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16071576526481365137980101 3013420598715255963371269)
            ·
              refine ⟨565016362259110493132113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3013420598715255963371269 565016362259110493132113)
              ·
                refine ⟨423762271694332869849085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565016362259110493132113 423762271694332869849085)
                ·
                  refine ⟨158910851885374826193407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423762271694332869849085 158910851885374826193407)
                  ·
                    rfl

theorem cell21_696325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_696325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696325 prefixEnd_696325 := by exact prefixLift 696325
  have htrace : WordTrace (prefixWord ++ tailWord_696325) baseStart_696325 baseEnd_696325 := by
    simpa [prefixWord, tailWord_696325, baseEnd_696325] using wordTrace_append hprefix tailTrace_696325
  have hstable : (prefixWord ++ tailWord_696325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696325).length < 2 ^ (prefixWord ++ tailWord_696325).sum := by decide
  have hdescent : baseEnd_696325 < baseStart_696325 := by decide
  rcases family_descends (prefixWord ++ tailWord_696325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696384 : List Nat := [2, 1, 1, 2, 2, 4, 2, 4, 3]
def baseStart_696384 : Nat := 118140960795 + 696384 * 2 ^ 59
def prefixEnd_696384 : Nat := 4983230072969 + 3 ^ 40 * 696384 * 2
def baseEnd_696384 : Nat := 158924316489203834709953

theorem tailTrace_696384 : CollatzResearch.WordTrace tailWord_696384 prefixEnd_696384 158924316489203834709953 := by
  unfold tailWord_696384
  simp only [CollatzResearch.WordTrace]
  refine ⟨12699605554563587881788103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16932807406084783842384137 12699605554563587881788103)
  ·
    refine ⟨19049408331845381822682155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12699605554563587881788103 19049408331845381822682155)
    ·
      refine ⟨28574112497768072734023233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19049408331845381822682155 28574112497768072734023233)
      ·
        refine ⟨21430584373326054550517425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28574112497768072734023233 21430584373326054550517425)
        ·
          refine ⟨16072938279994540912888069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21430584373326054550517425 16072938279994540912888069)
          ·
            refine ⟨3013675927498976421166513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16072938279994540912888069 3013675927498976421166513)
            ·
              refine ⟨2260256945624232315874885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3013675927498976421166513 2260256945624232315874885)
              ·
                refine ⟨423798177304543559226541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2260256945624232315874885 423798177304543559226541)
                ·
                  refine ⟨158924316489203834709953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423798177304543559226541 158924316489203834709953)
                  ·
                    rfl

theorem cell21_696384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 3].length) (baseStart_696384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696384 prefixEnd_696384 := by exact prefixLift 696384
  have htrace : WordTrace (prefixWord ++ tailWord_696384) baseStart_696384 baseEnd_696384 := by
    simpa [prefixWord, tailWord_696384, baseEnd_696384] using wordTrace_append hprefix tailTrace_696384
  have hstable : (prefixWord ++ tailWord_696384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696384).length < 2 ^ (prefixWord ++ tailWord_696384).sum := by decide
  have hdescent : baseEnd_696384 < baseStart_696384 := by decide
  rcases family_descends (prefixWord ++ tailWord_696384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696449 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 4]
def baseStart_696449 : Nat := 118140960795 + 696449 * 2 ^ 59
def prefixEnd_696449 : Nat := 4983230072969 + 3 ^ 40 * 696449 * 2
def baseEnd_696449 : Nat := 158939150374778166126487

theorem tailTrace_696449 : CollatzResearch.WordTrace tailWord_696449 prefixEnd_696449 158939150374778166126487 := by
  unfold tailWord_696449
  simp only [CollatzResearch.WordTrace]
  refine ⟨25401581853891691864692401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16934387902594461243128267 25401581853891691864692401)
  ·
    refine ⟨19051186390418768898519301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25401581853891691864692401 19051186390418768898519301)
    ·
      refine ⟨3572097448203519168472369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19051186390418768898519301 3572097448203519168472369)
      ·
        refine ⟨2679073086152639376354277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3572097448203519168472369 2679073086152639376354277)
        ·
          refine ⟨502326203653619883066427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2679073086152639376354277 502326203653619883066427)
          ·
            refine ⟨753489305480429824599641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502326203653619883066427 753489305480429824599641)
            ·
              refine ⟨565116979110322368449731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753489305480429824599641 565116979110322368449731)
              ·
                refine ⟨847675468665483552674597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565116979110322368449731 847675468665483552674597)
                ·
                  refine ⟨158939150374778166126487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 847675468665483552674597 158939150374778166126487)
                  ·
                    rfl

theorem cell21_696449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 4].length) (baseStart_696449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696449 prefixEnd_696449 := by exact prefixLift 696449
  have htrace : WordTrace (prefixWord ++ tailWord_696449) baseStart_696449 baseEnd_696449 := by
    simpa [prefixWord, tailWord_696449, baseEnd_696449] using wordTrace_append hprefix tailTrace_696449
  have hstable : (prefixWord ++ tailWord_696449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696449).length < 2 ^ (prefixWord ++ tailWord_696449).sum := by decide
  have hdescent : baseEnd_696449 < baseStart_696449 := by decide
  rcases family_descends (prefixWord ++ tailWord_696449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696536 : List Nat := [2, 1, 2, 2, 4, 1, 1, 5, 3]
def baseStart_696536 : Nat := 118140960795 + 696536 * 2 ^ 59
def prefixEnd_696536 : Nat := 4983230072969 + 3 ^ 40 * 696536 * 2
def baseEnd_696536 : Nat := 158959004960085348176309

theorem tailTrace_696536 : CollatzResearch.WordTrace tailWord_696536 prefixEnd_696536 158959004960085348176309 := by
  unfold tailWord_696536
  simp only [CollatzResearch.WordTrace]
  refine ⟨12702377502288252861554731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16936503336384337148739641 12702377502288252861554731)
  ·
    refine ⟨19053566253432379292332097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12702377502288252861554731 19053566253432379292332097)
    ·
      refine ⟨14290174690074284469249073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19053566253432379292332097 14290174690074284469249073)
      ·
        refine ⟨10717631017555713351936805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14290174690074284469249073 10717631017555713351936805)
        ·
          refine ⟨2009555815791696253488151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10717631017555713351936805 2009555815791696253488151)
          ·
            refine ⟨3014333723687544380232227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009555815791696253488151 3014333723687544380232227)
            ·
              refine ⟨4521500585531316570348341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3014333723687544380232227 4521500585531316570348341)
              ·
                refine ⟨423890679893560928470157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4521500585531316570348341 423890679893560928470157)
                ·
                  refine ⟨158959004960085348176309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423890679893560928470157 158959004960085348176309)
                  ·
                    rfl

theorem cell21_696536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 3].length) (baseStart_696536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696536 prefixEnd_696536 := by exact prefixLift 696536
  have htrace : WordTrace (prefixWord ++ tailWord_696536) baseStart_696536 baseEnd_696536 := by
    simpa [prefixWord, tailWord_696536, baseEnd_696536] using wordTrace_append hprefix tailTrace_696536
  have hstable : (prefixWord ++ tailWord_696536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696536).length < 2 ^ (prefixWord ++ tailWord_696536).sum := by decide
  have hdescent : baseEnd_696536 < baseStart_696536 := by decide
  rcases family_descends (prefixWord ++ tailWord_696536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696609 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 6]
def baseStart_696609 : Nat := 118140960795 + 696609 * 2 ^ 59
def prefixEnd_696609 : Nat := 4983230072969 + 3 ^ 40 * 696609 * 2
def baseEnd_696609 : Nat := 158975664554653443459493

theorem tailTrace_696609 : CollatzResearch.WordTrace tailWord_696609 prefixEnd_696609 158975664554653443459493 := by
  unfold tailWord_696609
  simp only [CollatzResearch.WordTrace]
  refine ⟨25407417533312039190516881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16938278355541359460344587 25407417533312039190516881)
  ·
    refine ⟨19055563149984029392887661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25407417533312039190516881 19055563149984029392887661)
    ·
      refine ⟨7145836181244011022332873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19055563149984029392887661 7145836181244011022332873)
      ·
        refine ⟨5359377135933008266749655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7145836181244011022332873 5359377135933008266749655)
        ·
          refine ⟨8039065703899512400124483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359377135933008266749655 8039065703899512400124483)
          ·
            refine ⟨12058598555849268600186725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8039065703899512400124483 12058598555849268600186725)
            ·
              refine ⟨2260987229221737862535011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12058598555849268600186725 2260987229221737862535011)
              ·
                refine ⟨3391480843832606793802517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260987229221737862535011 3391480843832606793802517)
                ·
                  refine ⟨158975664554653443459493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3391480843832606793802517 158975664554653443459493)
                  ·
                    rfl

theorem cell21_696609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_696609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696609 prefixEnd_696609 := by exact prefixLift 696609
  have htrace : WordTrace (prefixWord ++ tailWord_696609) baseStart_696609 baseEnd_696609 := by
    simpa [prefixWord, tailWord_696609, baseEnd_696609] using wordTrace_append hprefix tailTrace_696609
  have hstable : (prefixWord ++ tailWord_696609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696609).length < 2 ^ (prefixWord ++ tailWord_696609).sum := by decide
  have hdescent : baseEnd_696609 < baseStart_696609 := by decide
  rcases family_descends (prefixWord ++ tailWord_696609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696612 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 5]
def baseStart_696612 : Nat := 118140960795 + 696612 * 2 ^ 59
def prefixEnd_696612 : Nat := 4983230072969 + 3 ^ 40 * 696612 * 2
def baseEnd_696612 : Nat := 158976349195526104909487

theorem tailTrace_696612 : CollatzResearch.WordTrace tailWord_696612 prefixEnd_696612 158976349195526104909487 := by
  unfold tailWord_696612
  simp only [CollatzResearch.WordTrace]
  refine ⟨12703763476150585351438045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16938351301534113801917393 12703763476150585351438045)
  ·
    refine ⟨4763911303556469506789267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12703763476150585351438045 4763911303556469506789267)
    ·
      refine ⟨7145866955334704260183901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4763911303556469506789267 7145866955334704260183901)
      ·
        refine ⟨2679700108250514097568963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7145866955334704260183901 2679700108250514097568963)
        ·
          refine ⟨4019550162375771146353445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2679700108250514097568963 4019550162375771146353445)
          ·
            refine ⟨753665655445457089941271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4019550162375771146353445 753665655445457089941271)
            ·
              refine ⟨1130498483168185634911907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753665655445457089941271 1130498483168185634911907)
              ·
                refine ⟨1695747724752278452367861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130498483168185634911907 1695747724752278452367861)
                ·
                  refine ⟨158976349195526104909487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1695747724752278452367861 158976349195526104909487)
                  ·
                    rfl

theorem cell21_696612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_696612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696612 prefixEnd_696612 := by exact prefixLift 696612
  have htrace : WordTrace (prefixWord ++ tailWord_696612) baseStart_696612 baseEnd_696612 := by
    simpa [prefixWord, tailWord_696612, baseEnd_696612] using wordTrace_append hprefix tailTrace_696612
  have hstable : (prefixWord ++ tailWord_696612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696612).length < 2 ^ (prefixWord ++ tailWord_696612).sum := by decide
  have hdescent : baseEnd_696612 < baseStart_696612 := by decide
  rcases family_descends (prefixWord ++ tailWord_696612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696615 : List Nat := [1, 1, 8, 1, 1, 1, 2, 6]
def baseStart_696615 : Nat := 118140960795 + 696615 * 2 ^ 59
def prefixEnd_696615 : Nat := 4983230072969 + 3 ^ 40 * 696615 * 2
def baseEnd_696615 : Nat := 52992344612132922119827

theorem tailTrace_696615 : CollatzResearch.WordTrace tailWord_696615 prefixEnd_696615 52992344612132922119827 := by
  unfold tailWord_696615
  simp only [CollatzResearch.WordTrace]
  refine ⟨25407636371290302215235299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16938424247526868143490199 25407636371290302215235299)
  ·
    refine ⟨38111454556935453322852949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25407636371290302215235299 38111454556935453322852949)
    ·
      refine ⟨446618608089087343627183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 38111454556935453322852949 446618608089087343627183)
      ·
        refine ⟨669927912133631015440775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446618608089087343627183 669927912133631015440775)
        ·
          refine ⟨1004891868200446523161163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669927912133631015440775 1004891868200446523161163)
          ·
            refine ⟨1507337802300669784741745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004891868200446523161163 1507337802300669784741745)
            ·
              refine ⟨1130503351725502338556309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1507337802300669784741745 1130503351725502338556309)
              ·
                refine ⟨52992344612132922119827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1130503351725502338556309 52992344612132922119827)
                ·
                  rfl

theorem cell21_696615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 6].length) (baseStart_696615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696615 prefixEnd_696615 := by exact prefixLift 696615
  have htrace : WordTrace (prefixWord ++ tailWord_696615) baseStart_696615 baseEnd_696615 := by
    simpa [prefixWord, tailWord_696615, baseEnd_696615] using wordTrace_append hprefix tailTrace_696615
  have hstable : (prefixWord ++ tailWord_696615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696615).length < 2 ^ (prefixWord ++ tailWord_696615).sum := by decide
  have hdescent : baseEnd_696615 < baseStart_696615 := by decide
  rcases family_descends (prefixWord ++ tailWord_696615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696623 : List Nat := [1, 1, 2, 1, 2, 1, 5, 8]
def baseStart_696623 : Nat := 118140960795 + 696623 * 2 ^ 59
def prefixEnd_696623 : Nat := 4983230072969 + 3 ^ 40 * 696623 * 2
def baseEnd_696623 : Nat := 52992953181797510075377

theorem tailTrace_696623 : CollatzResearch.WordTrace tailWord_696623 prefixEnd_696623 52992953181797510075377 := by
  unfold tailWord_696623
  simp only [CollatzResearch.WordTrace]
  refine ⟨25407928155261319581526523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16938618770174213054351015 25407928155261319581526523)
  ·
    refine ⟨38111892232891979372289785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25407928155261319581526523 38111892232891979372289785)
    ·
      refine ⟨28583919174668984529217339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38111892232891979372289785 28583919174668984529217339)
      ·
        refine ⟨42875878762003476793826009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28583919174668984529217339 42875878762003476793826009)
        ·
          refine ⟨32156909071502607595369507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42875878762003476793826009 32156909071502607595369507)
          ·
            refine ⟨48235363607253911393054261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32156909071502607595369507 48235363607253911393054261)
            ·
              refine ⟨4522065338180054193098837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48235363607253911393054261 4522065338180054193098837)
              ·
                refine ⟨52992953181797510075377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4522065338180054193098837 52992953181797510075377)
                ·
                  rfl

theorem cell21_696623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 8].length) (baseStart_696623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696623 prefixEnd_696623 := by exact prefixLift 696623
  have htrace : WordTrace (prefixWord ++ tailWord_696623) baseStart_696623 baseEnd_696623 := by
    simpa [prefixWord, tailWord_696623, baseEnd_696623] using wordTrace_append hprefix tailTrace_696623
  have hstable : (prefixWord ++ tailWord_696623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696623).length < 2 ^ (prefixWord ++ tailWord_696623).sum := by decide
  have hdescent : baseEnd_696623 < baseStart_696623 := by decide
  rcases family_descends (prefixWord ++ tailWord_696623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696654 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_696654 : Nat := 118140960795 + 696654 * 2 ^ 59
def prefixEnd_696654 : Nat := 4983230072969 + 3 ^ 40 * 696654 * 2
def baseEnd_696654 : Nat := 158985934167743365209401

theorem tailTrace_696654 : CollatzResearch.WordTrace tailWord_696654 prefixEnd_696654 158985934167743365209401 := by
  unfold tailWord_696654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3176132352268626484488127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16939372545432674583936677 3176132352268626484488127)
  ·
    refine ⟨4764198528402939726732191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3176132352268626484488127 4764198528402939726732191)
    ·
      refine ⟨7146297792604409590098287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4764198528402939726732191 7146297792604409590098287)
      ·
        refine ⟨10719446688906614385147431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7146297792604409590098287 10719446688906614385147431)
        ·
          refine ⟨16079170033359921577721147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10719446688906614385147431 16079170033359921577721147)
          ·
            refine ⟨24118755050039882366581721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16079170033359921577721147 24118755050039882366581721)
            ·
              refine ⟨18089066287529911774936291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24118755050039882366581721 18089066287529911774936291)
              ·
                refine ⟨27133599431294867662404437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18089066287529911774936291 27133599431294867662404437)
                ·
                  refine ⟨158985934167743365209401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27133599431294867662404437 158985934167743365209401)
                  ·
                    rfl

theorem cell21_696654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_696654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696654 prefixEnd_696654 := by exact prefixLift 696654
  have htrace : WordTrace (prefixWord ++ tailWord_696654) baseStart_696654 baseEnd_696654 := by
    simpa [prefixWord, tailWord_696654, baseEnd_696654] using wordTrace_append hprefix tailTrace_696654
  have hstable : (prefixWord ++ tailWord_696654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696654).length < 2 ^ (prefixWord ++ tailWord_696654).sum := by decide
  have hdescent : baseEnd_696654 < baseStart_696654 := by decide
  rcases family_descends (prefixWord ++ tailWord_696654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696705 : List Nat := [1, 2, 4, 3, 1, 2, 2, 3, 3]
def baseStart_696705 : Nat := 118140960795 + 696705 * 2 ^ 59
def prefixEnd_696705 : Nat := 4983230072969 + 3 ^ 40 * 696705 * 2
def baseEnd_696705 : Nat := 158997573062578609859297

theorem tailTrace_696705 : CollatzResearch.WordTrace tailWord_696705 prefixEnd_696705 158997573062578609859297 := by
  unfold tailWord_696705
  simp only [CollatzResearch.WordTrace]
  refine ⟨25410918940964247586011569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16940612627309498390674379 25410918940964247586011569)
  ·
    refine ⟨19058189205723185689508677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25410918940964247586011569 19058189205723185689508677)
    ·
      refine ⟨3573410476073097316782877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19058189205723185689508677 3573410476073097316782877)
      ·
        refine ⟨1340028928527411493793579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3573410476073097316782877 1340028928527411493793579)
        ·
          refine ⟨2010043392791117240690369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340028928527411493793579 2010043392791117240690369)
          ·
            refine ⟨1507532544593337930517777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2010043392791117240690369 1507532544593337930517777)
            ·
              refine ⟨1130649408445003447888333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1507532544593337930517777 1130649408445003447888333)
              ·
                refine ⟨423993528166876292958125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1130649408445003447888333 423993528166876292958125)
                ·
                  refine ⟨158997573062578609859297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423993528166876292958125 158997573062578609859297)
                  ·
                    rfl

theorem cell21_696705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 3].length) (baseStart_696705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696705 prefixEnd_696705 := by exact prefixLift 696705
  have htrace : WordTrace (prefixWord ++ tailWord_696705) baseStart_696705 baseEnd_696705 := by
    simpa [prefixWord, tailWord_696705, baseEnd_696705] using wordTrace_append hprefix tailTrace_696705
  have hstable : (prefixWord ++ tailWord_696705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696705).length < 2 ^ (prefixWord ++ tailWord_696705).sum := by decide
  have hdescent : baseEnd_696705 < baseStart_696705 := by decide
  rcases family_descends (prefixWord ++ tailWord_696705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696756 : List Nat := [2, 5, 2, 2, 2, 1, 1, 3, 3]
def baseStart_696756 : Nat := 118140960795 + 696756 * 2 ^ 59
def prefixEnd_696756 : Nat := 4983230072969 + 3 ^ 40 * 696756 * 2
def baseEnd_696756 : Nat := 159009211957413854509193

theorem tailTrace_696756 : CollatzResearch.WordTrace tailWord_696756 prefixEnd_696756 159009211957413854509193 := by
  unfold tailWord_696756
  simp only [CollatzResearch.WordTrace]
  refine ⟨12706389531889741648059061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16941852709186322197412081 12706389531889741648059061)
  ·
    refine ⟨1191224018614663279505537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12706389531889741648059061 1191224018614663279505537)
    ·
      refine ⟨893418013960997459629153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1191224018614663279505537 893418013960997459629153)
      ·
        refine ⟨670063510470748094721865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 893418013960997459629153 670063510470748094721865)
        ·
          refine ⟨502547632853061071041399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 670063510470748094721865 502547632853061071041399)
          ·
            refine ⟨753821449279591606562099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502547632853061071041399 753821449279591606562099)
            ·
              refine ⟨1130732173919387409843149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753821449279591606562099 1130732173919387409843149)
              ·
                refine ⟨424024565219770278691181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1130732173919387409843149 424024565219770278691181)
                ·
                  refine ⟨159009211957413854509193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424024565219770278691181 159009211957413854509193)
                  ·
                    rfl

theorem cell21_696756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_696756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696756 prefixEnd_696756 := by exact prefixLift 696756
  have htrace : WordTrace (prefixWord ++ tailWord_696756) baseStart_696756 baseEnd_696756 := by
    simpa [prefixWord, tailWord_696756, baseEnd_696756] using wordTrace_append hprefix tailTrace_696756
  have hstable : (prefixWord ++ tailWord_696756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696756).length < 2 ^ (prefixWord ++ tailWord_696756).sum := by decide
  have hdescent : baseEnd_696756 < baseStart_696756 := by decide
  rcases family_descends (prefixWord ++ tailWord_696756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696761 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 6]
def baseStart_696761 : Nat := 118140960795 + 696761 * 2 ^ 59
def prefixEnd_696761 : Nat := 4983230072969 + 3 ^ 40 * 696761 * 2
def baseEnd_696761 : Nat := 159010353025534956925849

theorem tailTrace_696761 : CollatzResearch.WordTrace tailWord_696761 prefixEnd_696761 159010353025534956925849 := by
  unfold tailWord_696761
  simp only [CollatzResearch.WordTrace]
  refine ⟨25412961428761369150050137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16941974285840912766700091 25412961428761369150050137)
  ·
    refine ⟨19059721071571026862537603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25412961428761369150050137 19059721071571026862537603)
    ·
      refine ⟨28589581607356540293806405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19059721071571026862537603 28589581607356540293806405)
      ·
        refine ⟨5360546551379351305088701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28589581607356540293806405 5360546551379351305088701)
        ·
          refine ⟨2010204956767256739408263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5360546551379351305088701 2010204956767256739408263)
          ·
            refine ⟨3015307435150885109112395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010204956767256739408263 3015307435150885109112395)
            ·
              refine ⟨4522961152726327663668593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015307435150885109112395 4522961152726327663668593)
              ·
                refine ⟨3392220864544745747751445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4522961152726327663668593 3392220864544745747751445)
                ·
                  refine ⟨159010353025534956925849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3392220864544745747751445 159010353025534956925849)
                  ·
                    rfl

theorem cell21_696761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_696761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696761 prefixEnd_696761 := by exact prefixLift 696761
  have htrace : WordTrace (prefixWord ++ tailWord_696761) baseStart_696761 baseEnd_696761 := by
    simpa [prefixWord, tailWord_696761, baseEnd_696761] using wordTrace_append hprefix tailTrace_696761
  have hstable : (prefixWord ++ tailWord_696761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696761).length < 2 ^ (prefixWord ++ tailWord_696761).sum := by decide
  have hdescent : baseEnd_696761 < baseStart_696761 := by decide
  rcases family_descends (prefixWord ++ tailWord_696761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696775 : List Nat := [1, 1, 4, 1, 1, 4, 9]
def baseStart_696775 : Nat := 118140960795 + 696775 * 2 ^ 59
def prefixEnd_696775 : Nat := 4983230072969 + 3 ^ 40 * 696775 * 2
def baseEnd_696775 : Nat := 17668172001808227076943

theorem tailTrace_696775 : CollatzResearch.WordTrace tailWord_696775 prefixEnd_696775 17668172001808227076943 := by
  unfold tailWord_696775
  simp only [CollatzResearch.WordTrace]
  refine ⟨25413472050710649541059779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16942314700473766360706519 25413472050710649541059779)
  ·
    refine ⟨38120208076065974311589669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25413472050710649541059779 38120208076065974311589669)
    ·
      refine ⟨7147539014262370183423063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38120208076065974311589669 7147539014262370183423063)
      ·
        refine ⟨10721308521393555275134595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7147539014262370183423063 10721308521393555275134595)
        ·
          refine ⟨16081962782090332912701893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10721308521393555275134595 16081962782090332912701893)
          ·
            refine ⟨3015368021641937421131605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16081962782090332912701893 3015368021641937421131605)
            ·
              refine ⟨17668172001808227076943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3015368021641937421131605 17668172001808227076943)
              ·
                rfl

theorem cell21_696775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 9].length) (baseStart_696775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696775 prefixEnd_696775 := by exact prefixLift 696775
  have htrace : WordTrace (prefixWord ++ tailWord_696775) baseStart_696775 baseEnd_696775 := by
    simpa [prefixWord, tailWord_696775, baseEnd_696775] using wordTrace_append hprefix tailTrace_696775
  have hstable : (prefixWord ++ tailWord_696775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696775).length < 2 ^ (prefixWord ++ tailWord_696775).sum := by decide
  have hdescent : baseEnd_696775 < baseStart_696775 := by decide
  rcases family_descends (prefixWord ++ tailWord_696775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696837 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 4]
def baseStart_696837 : Nat := 118140960795 + 696837 * 2 ^ 59
def prefixEnd_696837 : Nat := 4983230072969 + 3 ^ 40 * 696837 * 2
def baseEnd_696837 : Nat := 159027697260975713659027

theorem tailTrace_696837 : CollatzResearch.WordTrace tailWord_696837 prefixEnd_696837 159027697260975713659027 := by
  unfold tailWord_696837
  simp only [CollatzResearch.WordTrace]
  refine ⟨25415733376486034129816765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16943822250990689419877843 25415733376486034129816765)
  ·
    refine ⟨9530900016182262798681287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25415733376486034129816765 9530900016182262798681287)
    ·
      refine ⟨14296350024273394198021931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9530900016182262798681287 14296350024273394198021931)
      ·
        refine ⟨21444525036410091297032897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14296350024273394198021931 21444525036410091297032897)
        ·
          refine ⟨16083393777307568472774673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21444525036410091297032897 16083393777307568472774673)
          ·
            refine ⟨12062545332980676354581005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16083393777307568472774673 12062545332980676354581005)
            ·
              refine ⟨4523454499867753632967877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12062545332980676354581005 4523454499867753632967877)
              ·
                refine ⟨848147718725203806181477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4523454499867753632967877 848147718725203806181477)
                ·
                  refine ⟨159027697260975713659027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 848147718725203806181477 159027697260975713659027)
                  ·
                    rfl

theorem cell21_696837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_696837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696837 prefixEnd_696837 := by exact prefixLift 696837
  have htrace : WordTrace (prefixWord ++ tailWord_696837) baseStart_696837 baseEnd_696837 := by
    simpa [prefixWord, tailWord_696837, baseEnd_696837] using wordTrace_append hprefix tailTrace_696837
  have hstable : (prefixWord ++ tailWord_696837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696837).length < 2 ^ (prefixWord ++ tailWord_696837).sum := by decide
  have hdescent : baseEnd_696837 < baseStart_696837 := by decide
  rcases family_descends (prefixWord ++ tailWord_696837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696933 : List Nat := [1, 3, 1, 3, 4, 2, 1, 3, 3]
def baseStart_696933 : Nat := 118140960795 + 696933 * 2 ^ 59
def prefixEnd_696933 : Nat := 4983230072969 + 3 ^ 40 * 696933 * 2
def baseEnd_696933 : Nat := 159049605768900880058831

theorem tailTrace_696933 : CollatzResearch.WordTrace tailWord_696933 prefixEnd_696933 159049605768900880058831 := by
  unfold tailWord_696933
  simp only [CollatzResearch.WordTrace]
  refine ⟨25419234784138242525311453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16946156522758828350207635 25419234784138242525311453)
  ·
    refine ⟨9532213044051840946991795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25419234784138242525311453 9532213044051840946991795)
    ·
      refine ⟨14298319566077761420487693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9532213044051840946991795 14298319566077761420487693)
      ·
        refine ⟨5361869837279160532682885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14298319566077761420487693 5361869837279160532682885)
        ·
          refine ⟨1005350594489842599878041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5361869837279160532682885 1005350594489842599878041)
          ·
            refine ⟨754012945867381949908531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005350594489842599878041 754012945867381949908531)
            ·
              refine ⟨1131019418801072924862797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754012945867381949908531 1131019418801072924862797)
              ·
                refine ⟨424132282050402346823549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1131019418801072924862797 424132282050402346823549)
                ·
                  refine ⟨159049605768900880058831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424132282050402346823549 159049605768900880058831)
                  ·
                    rfl

theorem cell21_696933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_696933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696933 prefixEnd_696933 := by exact prefixLift 696933
  have htrace : WordTrace (prefixWord ++ tailWord_696933) baseStart_696933 baseEnd_696933 := by
    simpa [prefixWord, tailWord_696933, baseEnd_696933] using wordTrace_append hprefix tailTrace_696933
  have hstable : (prefixWord ++ tailWord_696933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696933).length < 2 ^ (prefixWord ++ tailWord_696933).sum := by decide
  have hdescent : baseEnd_696933 < baseStart_696933 := by decide
  rcases family_descends (prefixWord ++ tailWord_696933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696944 : List Nat := [2, 1, 1, 1, 7, 2, 7]
def baseStart_696944 : Nat := 118140960795 + 696944 * 2 ^ 59
def prefixEnd_696944 : Nat := 4983230072969 + 3 ^ 40 * 696944 * 2
def baseEnd_696944 : Nat := 17672457346529700597275

theorem tailTrace_696944 : CollatzResearch.WordTrace tailWord_696944 prefixEnd_696944 17672457346529700597275 := by
  unfold tailWord_696944
  simp only [CollatzResearch.WordTrace]
  refine ⟨12709817993549195701980943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16946423991398927602641257 12709817993549195701980943)
  ·
    refine ⟨19064726990323793552971415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12709817993549195701980943 19064726990323793552971415)
    ·
      refine ⟨28597090485485690329457123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19064726990323793552971415 28597090485485690329457123)
      ·
        refine ⟨42895635728228535494185685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28597090485485690329457123 42895635728228535494185685)
        ·
          refine ⟨1005366462380356300644977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 42895635728228535494185685 1005366462380356300644977)
          ·
            refine ⟨754024846785267225483733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005366462380356300644977 754024846785267225483733)
            ·
              refine ⟨17672457346529700597275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 754024846785267225483733 17672457346529700597275)
              ·
                rfl

theorem cell21_696944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 7].length) (baseStart_696944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696944 prefixEnd_696944 := by exact prefixLift 696944
  have htrace : WordTrace (prefixWord ++ tailWord_696944) baseStart_696944 baseEnd_696944 := by
    simpa [prefixWord, tailWord_696944, baseEnd_696944] using wordTrace_append hprefix tailTrace_696944
  have hstable : (prefixWord ++ tailWord_696944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696944).length < 2 ^ (prefixWord ++ tailWord_696944).sum := by decide
  have hdescent : baseEnd_696944 < baseStart_696944 := by decide
  rcases family_descends (prefixWord ++ tailWord_696944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696950 : List Nat := [5, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_696950 : Nat := 118140960795 + 696950 * 2 ^ 59
def prefixEnd_696950 : Nat := 4983230072969 + 3 ^ 40 * 696950 * 2
def baseEnd_696950 : Nat := 159053485400512628275463

theorem tailTrace_696950 : CollatzResearch.WordTrace tailWord_696950 prefixEnd_696950 159053485400512628275463 := by
  unfold tailWord_696950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588740926567290901792519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16946569883384436285786869 1588740926567290901792519)
  ·
    refine ⟨2383111389850936352688779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1588740926567290901792519 2383111389850936352688779)
    ·
      refine ⟨3574667084776404529033169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2383111389850936352688779 3574667084776404529033169)
      ·
        refine ⟨2681000313582303396774877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3574667084776404529033169 2681000313582303396774877)
        ·
          refine ⟨1005375117593363773790579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2681000313582303396774877 1005375117593363773790579)
          ·
            refine ⟨1508062676390045660685869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005375117593363773790579 1508062676390045660685869)
            ·
              refine ⟨565523503646267122757201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1508062676390045660685869 565523503646267122757201)
              ·
                refine ⟨424142627734700342067901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565523503646267122757201 424142627734700342067901)
                ·
                  refine ⟨159053485400512628275463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424142627734700342067901 159053485400512628275463)
                  ·
                    rfl

theorem cell21_696950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_696950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696950 prefixEnd_696950 := by exact prefixLift 696950
  have htrace : WordTrace (prefixWord ++ tailWord_696950) baseStart_696950 baseEnd_696950 := by
    simpa [prefixWord, tailWord_696950, baseEnd_696950] using wordTrace_append hprefix tailTrace_696950
  have hstable : (prefixWord ++ tailWord_696950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696950).length < 2 ^ (prefixWord ++ tailWord_696950).sum := by decide
  have hdescent : baseEnd_696950 < baseStart_696950 := by decide
  rcases family_descends (prefixWord ++ tailWord_696950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696972 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_696972 : Nat := 118140960795 + 696972 * 2 ^ 59
def prefixEnd_696972 : Nat := 4983230072969 + 3 ^ 40 * 696972 * 2
def baseEnd_696972 : Nat := 159058506100245478908751

theorem tailTrace_696972 : CollatzResearch.WordTrace tailWord_696972 prefixEnd_696972 159058506100245478908751 := by
  unfold tailWord_696972
  simp only [CollatzResearch.WordTrace]
  refine ⟨12710328615498476092990585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16947104820664634790654113 12710328615498476092990585)
  ·
    refine ⟨9532746461623857069742939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12710328615498476092990585 9532746461623857069742939)
    ·
      refine ⟨14299119692435785604614409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9532746461623857069742939 14299119692435785604614409)
      ·
        refine ⟨10724339769326839203460807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14299119692435785604614409 10724339769326839203460807)
        ·
          refine ⟨16086509653990258805191211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10724339769326839203460807 16086509653990258805191211)
          ·
            refine ⟨24129764480985388207786817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16086509653990258805191211 24129764480985388207786817)
            ·
              refine ⟨18097323360739041155840113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24129764480985388207786817 18097323360739041155840113)
              ·
                refine ⟨13572992520554280866880085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18097323360739041155840113 13572992520554280866880085)
                ·
                  refine ⟨159058506100245478908751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13572992520554280866880085 159058506100245478908751)
                  ·
                    rfl

theorem cell21_696972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_696972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_696972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_696972 prefixEnd_696972 := by exact prefixLift 696972
  have htrace : WordTrace (prefixWord ++ tailWord_696972) baseStart_696972 baseEnd_696972 := by
    simpa [prefixWord, tailWord_696972, baseEnd_696972] using wordTrace_append hprefix tailTrace_696972
  have hstable : (prefixWord ++ tailWord_696972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696972).length < 2 ^ (prefixWord ++ tailWord_696972).sum := by decide
  have hdescent : baseEnd_696972 < baseStart_696972 := by decide
  rcases family_descends (prefixWord ++ tailWord_696972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697009 : List Nat := [1, 2, 2, 6, 1, 1, 1, 4, 3]
def baseStart_697009 : Nat := 118140960795 + 697009 * 2 ^ 59
def prefixEnd_697009 : Nat := 4983230072969 + 3 ^ 40 * 697009 * 2
def baseEnd_697009 : Nat := 159066950004341636792009

theorem tailTrace_697009 : CollatzResearch.WordTrace tailWord_697009 prefixEnd_697009 159066950004341636792009 := by
  unfold tailWord_697009
  simp only [CollatzResearch.WordTrace]
  refine ⟨25422006731862907505078081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16948004487908605003385387 25422006731862907505078081)
  ·
    refine ⟨19066505048897180628808561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25422006731862907505078081 19066505048897180628808561)
    ·
      refine ⟨14299878786672885471606421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19066505048897180628808561 14299878786672885471606421)
      ·
        refine ⟨670306818125291506481551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14299878786672885471606421 670306818125291506481551)
        ·
          refine ⟨1005460227187937259722327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670306818125291506481551 1005460227187937259722327)
          ·
            refine ⟨1508190340781905889583491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005460227187937259722327 1508190340781905889583491)
            ·
              refine ⟨2262285511172858834375237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508190340781905889583491 2262285511172858834375237)
              ·
                refine ⟨424178533344911031445357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2262285511172858834375237 424178533344911031445357)
                ·
                  refine ⟨159066950004341636792009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424178533344911031445357 159066950004341636792009)
                  ·
                    rfl

theorem cell21_697009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 3].length) (baseStart_697009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697009 prefixEnd_697009 := by exact prefixLift 697009
  have htrace : WordTrace (prefixWord ++ tailWord_697009) baseStart_697009 baseEnd_697009 := by
    simpa [prefixWord, tailWord_697009, baseEnd_697009] using wordTrace_append hprefix tailTrace_697009
  have hstable : (prefixWord ++ tailWord_697009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697009).length < 2 ^ (prefixWord ++ tailWord_697009).sum := by decide
  have hdescent : baseEnd_697009 < baseStart_697009 := by decide
  rcases family_descends (prefixWord ++ tailWord_697009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697034 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_697034 : Nat := 118140960795 + 697034 * 2 ^ 59
def prefixEnd_697034 : Nat := 4983230072969 + 3 ^ 40 * 697034 * 2
def baseEnd_697034 : Nat := 159072655344947148875291

theorem tailTrace_697034 : CollatzResearch.WordTrace tailWord_697034 prefixEnd_697034 159072655344947148875291 := by
  unfold tailWord_697034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355729639193084193684539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16948612371181557849825437 6355729639193084193684539)
  ·
    refine ⟨9533594458789626290526809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6355729639193084193684539 9533594458789626290526809)
    ·
      refine ⟨7150195844092219717895107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9533594458789626290526809 7150195844092219717895107)
      ·
        refine ⟨10725293766138329576842661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7150195844092219717895107 10725293766138329576842661)
        ·
          refine ⟨2010992581150936795657999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10725293766138329576842661 2010992581150936795657999)
          ·
            refine ⟨3016488871726405193486999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010992581150936795657999 3016488871726405193486999)
            ·
              refine ⟨4524733307589607790230499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016488871726405193486999 4524733307589607790230499)
              ·
                refine ⟨6787099961384411685345749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524733307589607790230499 6787099961384411685345749)
                ·
                  refine ⟨159072655344947148875291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6787099961384411685345749 159072655344947148875291)
                  ·
                    rfl

theorem cell21_697034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_697034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697034 prefixEnd_697034 := by exact prefixLift 697034
  have htrace : WordTrace (prefixWord ++ tailWord_697034) baseStart_697034 baseEnd_697034 := by
    simpa [prefixWord, tailWord_697034, baseEnd_697034] using wordTrace_append hprefix tailTrace_697034
  have hstable : (prefixWord ++ tailWord_697034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697034).length < 2 ^ (prefixWord ++ tailWord_697034).sum := by decide
  have hdescent : baseEnd_697034 < baseStart_697034 := by decide
  rcases family_descends (prefixWord ++ tailWord_697034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697065 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 4]
def baseStart_697065 : Nat := 118140960795 + 697065 * 2 ^ 59
def prefixEnd_697065 : Nat := 4983230072969 + 3 ^ 40 * 697065 * 2
def baseEnd_697065 : Nat := 159079729967297983858561

theorem tailTrace_697065 : CollatzResearch.WordTrace tailWord_697065 prefixEnd_697065 159079729967297983858561 := by
  unfold tailWord_697065
  simp only [CollatzResearch.WordTrace]
  refine ⟨25424049219660029069116649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16949366146440019379411099 25424049219660029069116649)
  ·
    refine ⟨19068036914745021801837487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25424049219660029069116649 19068036914745021801837487)
    ·
      refine ⟨28602055372117532702756231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19068036914745021801837487 28602055372117532702756231)
      ·
        refine ⟨42903083058176299054134347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28602055372117532702756231 42903083058176299054134347)
        ·
          refine ⟨64354624587264448581201521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42903083058176299054134347 64354624587264448581201521)
          ·
            refine ⟨48265968440448336435901141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64354624587264448581201521 48265968440448336435901141)
            ·
              refine ⟨1131233635323007885216433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48265968440448336435901141 1131233635323007885216433)
              ·
                refine ⟨848425226492255913912325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131233635323007885216433 848425226492255913912325)
                ·
                  refine ⟨159079729967297983858561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 848425226492255913912325 159079729967297983858561)
                  ·
                    rfl

theorem cell21_697065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_697065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697065 prefixEnd_697065 := by exact prefixLift 697065
  have htrace : WordTrace (prefixWord ++ tailWord_697065) baseStart_697065 baseEnd_697065 := by
    simpa [prefixWord, tailWord_697065, baseEnd_697065] using wordTrace_append hprefix tailTrace_697065
  have hstable : (prefixWord ++ tailWord_697065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697065).length < 2 ^ (prefixWord ++ tailWord_697065).sum := by decide
  have hdescent : baseEnd_697065 < baseStart_697065 := by decide
  rcases family_descends (prefixWord ++ tailWord_697065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697096 : List Nat := [2, 1, 3, 2, 2, 2, 4, 5]
def baseStart_697096 : Nat := 118140960795 + 697096 * 2 ^ 59
def prefixEnd_697096 : Nat := 4983230072969 + 3 ^ 40 * 697096 * 2
def baseEnd_697096 : Nat := 53028934863216272947277

theorem tailTrace_697096 : CollatzResearch.WordTrace tailWord_697096 prefixEnd_697096 53028934863216272947277 := by
  unfold tailWord_697096
  simp only [CollatzResearch.WordTrace]
  refine ⟨12712589941273860681747571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16950119921698480908996761 12712589941273860681747571)
  ·
    refine ⟨19068884911910791022621357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12712589941273860681747571 19068884911910791022621357)
    ·
      refine ⟨7150831841966546633483009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19068884911910791022621357 7150831841966546633483009)
      ·
        refine ⟨5363123881474909975112257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7150831841966546633483009 5363123881474909975112257)
        ·
          refine ⟨4022342911106182481334193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5363123881474909975112257 4022342911106182481334193)
          ·
            refine ⟨3016757183329636861000645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4022342911106182481334193 3016757183329636861000645)
            ·
              refine ⟨565641971874306911437621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3016757183329636861000645 565641971874306911437621)
              ·
                refine ⟨53028934863216272947277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 565641971874306911437621 53028934863216272947277)
                ·
                  rfl

theorem cell21_697096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_697096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697096 prefixEnd_697096 := by exact prefixLift 697096
  have htrace : WordTrace (prefixWord ++ tailWord_697096) baseStart_697096 baseEnd_697096 := by
    simpa [prefixWord, tailWord_697096, baseEnd_697096] using wordTrace_append hprefix tailTrace_697096
  have hstable : (prefixWord ++ tailWord_697096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697096).length < 2 ^ (prefixWord ++ tailWord_697096).sum := by decide
  have hdescent : baseEnd_697096 < baseStart_697096 := by decide
  rcases family_descends (prefixWord ++ tailWord_697096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697133 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 4]
def baseStart_697133 : Nat := 118140960795 + 697133 * 2 ^ 59
def prefixEnd_697133 : Nat := 4983230072969 + 3 ^ 40 * 697133 * 2
def baseEnd_697133 : Nat := 159095248493744976725089

theorem tailTrace_697133 : CollatzResearch.WordTrace tailWord_697133 prefixEnd_697133 159095248493744976725089 := by
  unfold tailWord_697133
  simp only [CollatzResearch.WordTrace]
  refine ⟨25426529383413676682592053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16951019588942451121728035 25426529383413676682592053)
  ·
    refine ⟨2383737129695032188993005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25426529383413676682592053 2383737129695032188993005)
    ·
      refine ⟨893901423635637070872377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2383737129695032188993005 893901423635637070872377)
      ·
        refine ⟨670426067726727803154283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 893901423635637070872377 670426067726727803154283)
        ·
          refine ⟨1005639101590091704731425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670426067726727803154283 1005639101590091704731425)
          ·
            refine ⟨754229326192568778548569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005639101590091704731425 754229326192568778548569)
            ·
              refine ⟨565671994644426583911427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754229326192568778548569 565671994644426583911427)
              ·
                refine ⟨848507991966639875867141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565671994644426583911427 848507991966639875867141)
                ·
                  refine ⟨159095248493744976725089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 848507991966639875867141 159095248493744976725089)
                  ·
                    rfl

theorem cell21_697133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_697133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697133 prefixEnd_697133 := by exact prefixLift 697133
  have htrace : WordTrace (prefixWord ++ tailWord_697133) baseStart_697133 baseEnd_697133 := by
    simpa [prefixWord, tailWord_697133, baseEnd_697133] using wordTrace_append hprefix tailTrace_697133
  have hstable : (prefixWord ++ tailWord_697133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697133).length < 2 ^ (prefixWord ++ tailWord_697133).sum := by decide
  have hdescent : baseEnd_697133 < baseStart_697133 := by decide
  rcases family_descends (prefixWord ++ tailWord_697133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697172 : List Nat := [2, 4, 1, 1, 5, 8]
def baseStart_697172 : Nat := 118140960795 + 697172 * 2 ^ 59
def prefixEnd_697172 : Nat := 4983230072969 + 3 ^ 40 * 697172 * 2
def baseEnd_697172 : Nat := 5892746252781095391667

theorem tailTrace_697172 : CollatzResearch.WordTrace tailWord_697172 prefixEnd_697172 5892746252781095391667 := by
  unfold tailWord_697172
  simp only [CollatzResearch.WordTrace]
  refine ⟨12713975915136193171630885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16951967886848257562174513 12713975915136193171630885)
  ·
    refine ⟨2383870484088036219680791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12713975915136193171630885 2383870484088036219680791)
    ·
      refine ⟨3575805726132054329521187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2383870484088036219680791 3575805726132054329521187)
      ·
        refine ⟨5363708589198081494281781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575805726132054329521187 5363708589198081494281781)
        ·
          refine ⟨502847680237320140088917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5363708589198081494281781 502847680237320140088917)
          ·
            refine ⟨5892746252781095391667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 502847680237320140088917 5892746252781095391667)
            ·
              rfl

theorem cell21_697172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 8].length) (baseStart_697172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697172 prefixEnd_697172 := by exact prefixLift 697172
  have htrace : WordTrace (prefixWord ++ tailWord_697172) baseStart_697172 baseEnd_697172 := by
    simpa [prefixWord, tailWord_697172, baseEnd_697172] using wordTrace_append hprefix tailTrace_697172
  have hstable : (prefixWord ++ tailWord_697172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697172).length < 2 ^ (prefixWord ++ tailWord_697172).sum := by decide
  have hdescent : baseEnd_697172 < baseStart_697172 := by decide
  rcases family_descends (prefixWord ++ tailWord_697172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697234 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_697234 : Nat := 118140960795 + 697234 * 2 ^ 59
def prefixEnd_697234 : Nat := 4983230072969 + 3 ^ 40 * 697234 * 2
def baseEnd_697234 : Nat := 159118298069791245541549

theorem tailTrace_697234 : CollatzResearch.WordTrace tailWord_697234 prefixEnd_697234 159118298069791245541549 := by
  unfold tailWord_697234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6357553289011942733004689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16953475437365180621345837 6357553289011942733004689)
  ·
    refine ⟨4768164966758957049753517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6357553289011942733004689 4768164966758957049753517)
    ·
      refine ⟨1788061862534608893657569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4768164966758957049753517 1788061862534608893657569)
      ·
        refine ⟨1341046396900956670243177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1788061862534608893657569 1341046396900956670243177)
        ·
          refine ⟨1005784797675717502682383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1341046396900956670243177 1005784797675717502682383)
          ·
            refine ⟨1508677196513576254023575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005784797675717502682383 1508677196513576254023575)
            ·
              refine ⟨2263015794770364381035363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508677196513576254023575 2263015794770364381035363)
              ·
                refine ⟨3394523692155546571553045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263015794770364381035363 3394523692155546571553045)
                ·
                  refine ⟨159118298069791245541549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3394523692155546571553045 159118298069791245541549)
                  ·
                    rfl

theorem cell21_697234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_697234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697234 prefixEnd_697234 := by exact prefixLift 697234
  have htrace : WordTrace (prefixWord ++ tailWord_697234) baseStart_697234 baseEnd_697234 := by
    simpa [prefixWord, tailWord_697234, baseEnd_697234] using wordTrace_append hprefix tailTrace_697234
  have hstable : (prefixWord ++ tailWord_697234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697234).length < 2 ^ (prefixWord ++ tailWord_697234).sum := by decide
  have hdescent : baseEnd_697234 < baseStart_697234 := by decide
  rcases family_descends (prefixWord ++ tailWord_697234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697265 : List Nat := [1, 2, 2, 4, 3, 2, 2, 5]
def baseStart_697265 : Nat := 118140960795 + 697265 * 2 ^ 59
def prefixEnd_697265 : Nat := 4983230072969 + 3 ^ 40 * 697265 * 2
def baseEnd_697265 : Nat := 53041790897380693508273

theorem tailTrace_697265 : CollatzResearch.WordTrace tailWord_697265 prefixEnd_697265 53041790897380693508273 := by
  unfold tailWord_697265
  simp only [CollatzResearch.WordTrace]
  refine ⟨25431343818935463226397249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16954229212623642150931499 25431343818935463226397249)
  ·
    refine ⟨19073507864201597419797937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25431343818935463226397249 19073507864201597419797937)
    ·
      refine ⟨14305130898151198064848453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19073507864201597419797937 14305130898151198064848453)
      ·
        refine ⟨2682212043403349637159085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14305130898151198064848453 2682212043403349637159085)
        ·
          refine ⟨1005829516276256113934657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2682212043403349637159085 1005829516276256113934657)
          ·
            refine ⟨754372137207192085450993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005829516276256113934657 754372137207192085450993)
            ·
              refine ⟨565779102905394064088245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754372137207192085450993 565779102905394064088245)
              ·
                refine ⟨53041790897380693508273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 565779102905394064088245 53041790897380693508273)
                ·
                  rfl

theorem cell21_697265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 5].length) (baseStart_697265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697265 prefixEnd_697265 := by exact prefixLift 697265
  have htrace : WordTrace (prefixWord ++ tailWord_697265) baseStart_697265 baseEnd_697265 := by
    simpa [prefixWord, tailWord_697265, baseEnd_697265] using wordTrace_append hprefix tailTrace_697265
  have hstable : (prefixWord ++ tailWord_697265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697265).length < 2 ^ (prefixWord ++ tailWord_697265).sum := by decide
  have hdescent : baseEnd_697265 < baseStart_697265 := by decide
  rcases family_descends (prefixWord ++ tailWord_697265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697355 : List Nat := [1, 1, 1, 1, 6, 3, 1, 4, 3]
def baseStart_697355 : Nat := 118140960795 + 697355 * 2 ^ 59
def prefixEnd_697355 : Nat := 4983230072969 + 3 ^ 40 * 697355 * 2
def baseEnd_697355 : Nat := 159145911918321924024635

theorem tailTrace_697355 : CollatzResearch.WordTrace tailWord_697355 prefixEnd_697355 159145911918321924024635 := by
  unfold tailWord_697355
  simp only [CollatzResearch.WordTrace]
  refine ⟨25434626388609408597173519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16956417592406272398115679 25434626388609408597173519)
  ·
    refine ⟨38151939582914112895760279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25434626388609408597173519 38151939582914112895760279)
    ·
      refine ⟨57227909374371169343640419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38151939582914112895760279 57227909374371169343640419)
      ·
        refine ⟨85841864061556754015460629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57227909374371169343640419 85841864061556754015460629)
        ·
          refine ⟨4023837377885472844474717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85841864061556754015460629 4023837377885472844474717)
          ·
            refine ⟨1508939016707052316678019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4023837377885472844474717 1508939016707052316678019)
            ·
              refine ⟨2263408525060578475017029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508939016707052316678019 2263408525060578475017029)
              ·
                refine ⟨424389098448858464065693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2263408525060578475017029 424389098448858464065693)
                ·
                  refine ⟨159145911918321924024635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424389098448858464065693 159145911918321924024635)
                  ·
                    rfl

theorem cell21_697355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 3].length) (baseStart_697355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697355 prefixEnd_697355 := by exact prefixLift 697355
  have htrace : WordTrace (prefixWord ++ tailWord_697355) baseStart_697355 baseEnd_697355 := by
    simpa [prefixWord, tailWord_697355, baseEnd_697355] using wordTrace_append hprefix tailTrace_697355
  have hstable : (prefixWord ++ tailWord_697355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697355).length < 2 ^ (prefixWord ++ tailWord_697355).sum := by decide
  have hdescent : baseEnd_697355 < baseStart_697355 := by decide
  rcases family_descends (prefixWord ++ tailWord_697355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697397 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 9]
def baseStart_697397 : Nat := 118140960795 + 697397 * 2 ^ 59
def prefixEnd_697397 : Nat := 4983230072969 + 3 ^ 40 * 697397 * 2
def baseEnd_697397 : Nat := 159155496890539184324549

theorem tailTrace_697397 : CollatzResearch.WordTrace tailWord_697397 prefixEnd_697397 159155496890539184324549 := by
  unfold tailWord_697397
  simp only [CollatzResearch.WordTrace]
  refine ⟨25436158254457249770202445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16957438836304833180134963 25436158254457249770202445)
  ·
    refine ⟨9538559345421468663825917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25436158254457249770202445 9538559345421468663825917)
    ·
      refine ⟨3576959754533050748934719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9538559345421468663825917 3576959754533050748934719)
      ·
        refine ⟨5365439631799576123402079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3576959754533050748934719 5365439631799576123402079)
        ·
          refine ⟨8048159447699364185103119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365439631799576123402079 8048159447699364185103119)
          ·
            refine ⟨12072239171549046277654679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8048159447699364185103119 12072239171549046277654679)
            ·
              refine ⟨18108358757323569416482019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12072239171549046277654679 18108358757323569416482019)
              ·
                refine ⟨27162538135985354124723029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18108358757323569416482019 27162538135985354124723029)
                ·
                  refine ⟨159155496890539184324549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27162538135985354124723029 159155496890539184324549)
                  ·
                    rfl

theorem cell21_697397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_697397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697397 prefixEnd_697397 := by exact prefixLift 697397
  have htrace : WordTrace (prefixWord ++ tailWord_697397) baseStart_697397 baseEnd_697397 := by
    simpa [prefixWord, tailWord_697397, baseEnd_697397] using wordTrace_append hprefix tailTrace_697397
  have hstable : (prefixWord ++ tailWord_697397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697397).length < 2 ^ (prefixWord ++ tailWord_697397).sum := by decide
  have hdescent : baseEnd_697397 < baseStart_697397 := by decide
  rcases family_descends (prefixWord ++ tailWord_697397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697521 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 4]
def baseStart_697521 : Nat := 118140960795 + 697521 * 2 ^ 59
def prefixEnd_697521 : Nat := 4983230072969 + 3 ^ 40 * 697521 * 2
def baseEnd_697521 : Nat := 159183795379942524257629

theorem tailTrace_697521 : CollatzResearch.WordTrace tailWord_697521 prefixEnd_697521 159183795379942524257629 := by
  unfold tailWord_697521
  simp only [CollatzResearch.WordTrace]
  refine ⟨25440680906008018947716417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16960453937338679298477611 25440680906008018947716417)
  ·
    refine ⟨19080510679506014210787313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25440680906008018947716417 19080510679506014210787313)
    ·
      refine ⟨14310383009629510658090485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19080510679506014210787313 14310383009629510658090485)
      ·
        refine ⟨1341598407152766624195983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14310383009629510658090485 1341598407152766624195983)
        ·
          refine ⟨2012397610729149936293975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1341598407152766624195983 2012397610729149936293975)
          ·
            refine ⟨3018596416093724904440963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012397610729149936293975 3018596416093724904440963)
            ·
              refine ⟨4527894624140587356661445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018596416093724904440963 4527894624140587356661445)
              ·
                refine ⟨848980242026360129374021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4527894624140587356661445 848980242026360129374021)
                ·
                  refine ⟨159183795379942524257629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 848980242026360129374021 159183795379942524257629)
                  ·
                    rfl

theorem cell21_697521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_697521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697521 prefixEnd_697521 := by exact prefixLift 697521
  have htrace : WordTrace (prefixWord ++ tailWord_697521) baseStart_697521 baseEnd_697521 := by
    simpa [prefixWord, tailWord_697521, baseEnd_697521] using wordTrace_append hprefix tailTrace_697521
  have hstable : (prefixWord ++ tailWord_697521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697521).length < 2 ^ (prefixWord ++ tailWord_697521).sum := by decide
  have hdescent : baseEnd_697521 < baseStart_697521 := by decide
  rcases family_descends (prefixWord ++ tailWord_697521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697580 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 6]
def baseStart_697580 : Nat := 118140960795 + 697580 * 2 ^ 59
def prefixEnd_697580 : Nat := 4983230072969 + 3 ^ 40 * 697580 * 2
def baseEnd_697580 : Nat := 159197259983771532774175

theorem tailTrace_697580 : CollatzResearch.WordTrace tailWord_697580 prefixEnd_697580 159197259983771532774175 := by
  unfold tailWord_697580
  simp only [CollatzResearch.WordTrace]
  refine ⟨12721416406397136012057097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16961888541862848016076129 12721416406397136012057097)
  ·
    refine ⟨9541062304797852009042823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12721416406397136012057097 9541062304797852009042823)
    ·
      refine ⟨14311593457196778013564235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9541062304797852009042823 14311593457196778013564235)
      ·
        refine ⟨21467390185795167020346353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14311593457196778013564235 21467390185795167020346353)
        ·
          refine ⟨16100542639346375265259765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21467390185795167020346353 16100542639346375265259765)
          ·
            refine ⟨1509425872438722681118103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16100542639346375265259765 1509425872438722681118103)
            ·
              refine ⟨2264138808658084021677155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1509425872438722681118103 2264138808658084021677155)
              ·
                refine ⟨3396208212987126032515733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2264138808658084021677155 3396208212987126032515733)
                ·
                  refine ⟨159197259983771532774175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3396208212987126032515733 159197259983771532774175)
                  ·
                    rfl

theorem cell21_697580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_697580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697580 prefixEnd_697580 := by exact prefixLift 697580
  have htrace : WordTrace (prefixWord ++ tailWord_697580) baseStart_697580 baseEnd_697580 := by
    simpa [prefixWord, tailWord_697580, baseEnd_697580] using wordTrace_append hprefix tailTrace_697580
  have hstable : (prefixWord ++ tailWord_697580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697580).length < 2 ^ (prefixWord ++ tailWord_697580).sum := by decide
  have hdescent : baseEnd_697580 < baseStart_697580 := by decide
  rcases family_descends (prefixWord ++ tailWord_697580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697594 : List Nat := [3, 1, 1, 1, 1, 4, 2, 8]
def baseStart_697594 : Nat := 118140960795 + 697594 * 2 ^ 59
def prefixEnd_697594 : Nat := 4983230072969 + 3 ^ 40 * 697594 * 2
def baseEnd_697594 : Nat := 53066818324836873180271

theorem tailTrace_697594 : CollatzResearch.WordTrace tailWord_697594 prefixEnd_697594 53066818324836873180271 := by
  unfold tailWord_697594
  simp only [CollatzResearch.WordTrace]
  refine ⟨6360835858685888103780959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16962228956495701610082557 6360835858685888103780959)
  ·
    refine ⟨9541253788028832155671439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6360835858685888103780959 9541253788028832155671439)
    ·
      refine ⟨14311880682043248233507159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9541253788028832155671439 14311880682043248233507159)
      ·
        refine ⟨21467821023064872350260739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14311880682043248233507159 21467821023064872350260739)
        ·
          refine ⟨32201731534597308525391109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21467821023064872350260739 32201731534597308525391109)
          ·
            refine ⟨6037824662736995348510833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32201731534597308525391109 6037824662736995348510833)
            ·
              refine ⟨4528368497052746511383125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6037824662736995348510833 4528368497052746511383125)
              ·
                refine ⟨53066818324836873180271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4528368497052746511383125 53066818324836873180271)
                ·
                  rfl

theorem cell21_697594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_697594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697594 prefixEnd_697594 := by exact prefixLift 697594
  have htrace : WordTrace (prefixWord ++ tailWord_697594) baseStart_697594 baseEnd_697594 := by
    simpa [prefixWord, tailWord_697594, baseEnd_697594] using wordTrace_append hprefix tailTrace_697594
  have hstable : (prefixWord ++ tailWord_697594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697594).length < 2 ^ (prefixWord ++ tailWord_697594).sum := by decide
  have hdescent : baseEnd_697594 < baseStart_697594 := by decide
  rcases family_descends (prefixWord ++ tailWord_697594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697611 : List Nat := [1, 1, 1, 1, 5, 3, 4, 5]
def baseStart_697611 : Nat := 118140960795 + 697611 * 2 ^ 59
def prefixEnd_697611 : Nat := 4983230072969 + 3 ^ 40 * 697611 * 2
def baseEnd_697611 : Nat := 53068111535374122585815

theorem tailTrace_697611 : CollatzResearch.WordTrace tailWord_697611 prefixEnd_697611 53068111535374122585815 := by
  unfold tailWord_697611
  simp only [CollatzResearch.WordTrace]
  refine ⟨25443963475681964318492687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16962642317121309545661791 25443963475681964318492687)
  ·
    refine ⟨38165945213522946477739031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25443963475681964318492687 38165945213522946477739031)
    ·
      refine ⟨57248917820284419716608547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38165945213522946477739031 57248917820284419716608547)
      ·
        refine ⟨85873376730426629574912821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57248917820284419716608547 85873376730426629574912821)
        ·
          refine ⟨8050629068477496522648077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85873376730426629574912821 8050629068477496522648077)
          ·
            refine ⟨3018985900679061195993029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8050629068477496522648077 3018985900679061195993029)
            ·
              refine ⟨566059856377323974248693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3018985900679061195993029 566059856377323974248693)
              ·
                refine ⟨53068111535374122585815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 566059856377323974248693 53068111535374122585815)
                ·
                  rfl

theorem cell21_697611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 5].length) (baseStart_697611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697611 prefixEnd_697611 := by exact prefixLift 697611
  have htrace : WordTrace (prefixWord ++ tailWord_697611) baseStart_697611 baseEnd_697611 := by
    simpa [prefixWord, tailWord_697611, baseEnd_697611] using wordTrace_append hprefix tailTrace_697611
  have hstable : (prefixWord ++ tailWord_697611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697611).length < 2 ^ (prefixWord ++ tailWord_697611).sum := by decide
  have hdescent : baseEnd_697611 < baseStart_697611 := by decide
  rcases family_descends (prefixWord ++ tailWord_697611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697701 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 5]
def baseStart_697701 : Nat := 118140960795 + 697701 * 2 ^ 59
def prefixEnd_697701 : Nat := 4983230072969 + 3 ^ 40 * 697701 * 2
def baseEnd_697701 : Nat := 159224873832302211257261

theorem tailTrace_697701 : CollatzResearch.WordTrace tailWord_697701 prefixEnd_697701 159224873832302211257261 := by
  unfold tailWord_697701
  simp only [CollatzResearch.WordTrace]
  refine ⟨25447246045355909689268957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16964830696903939792845971 25447246045355909689268957)
  ·
    refine ⟨9542717267008466133475859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25447246045355909689268957 9542717267008466133475859)
    ·
      refine ⟨14314075900512699200213789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9542717267008466133475859 14314075900512699200213789)
      ·
        refine ⟨5367778462692262200080171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14314075900512699200213789 5367778462692262200080171)
        ·
          refine ⟨8051667694038393300120257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5367778462692262200080171 8051667694038393300120257)
          ·
            refine ⟨6038750770528794975090193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8051667694038393300120257 6038750770528794975090193)
            ·
              refine ⟨4529063077896596231317645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6038750770528794975090193 4529063077896596231317645)
              ·
                refine ⟨1698398654211223586744117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4529063077896596231317645 1698398654211223586744117)
                ·
                  refine ⟨159224873832302211257261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1698398654211223586744117 159224873832302211257261)
                  ·
                    rfl

theorem cell21_697701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_697701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697701 prefixEnd_697701 := by exact prefixLift 697701
  have htrace : WordTrace (prefixWord ++ tailWord_697701) baseStart_697701 baseEnd_697701 := by
    simpa [prefixWord, tailWord_697701, baseEnd_697701] using wordTrace_append hprefix tailTrace_697701
  have hstable : (prefixWord ++ tailWord_697701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697701).length < 2 ^ (prefixWord ++ tailWord_697701).sum := by decide
  have hdescent : baseEnd_697701 < baseStart_697701 := by decide
  rcases family_descends (prefixWord ++ tailWord_697701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697704 : List Nat := [2, 1, 4, 2, 3, 2, 1, 6]
def baseStart_697704 : Nat := 118140960795 + 697704 * 2 ^ 59
def prefixEnd_697704 : Nat := 4983230072969 + 3 ^ 40 * 697704 * 2
def baseEnd_697704 : Nat := 53075186157724957569085

theorem tailTrace_697704 : CollatzResearch.WordTrace tailWord_697704 prefixEnd_697704 53075186157724957569085 := by
  unfold tailWord_697704
  simp only [CollatzResearch.WordTrace]
  refine ⟨12723677732172520600814083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16964903642896694134418777 12723677732172520600814083)
  ·
    refine ⟨19085516598258780901221125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12723677732172520600814083 19085516598258780901221125)
    ·
      refine ⟨3578534362173521418978961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19085516598258780901221125 3578534362173521418978961)
      ·
        refine ⟨2683900771630141064234221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3578534362173521418978961 2683900771630141064234221)
        ·
          refine ⟨1006462789361302899087833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2683900771630141064234221 1006462789361302899087833)
          ·
            refine ⟨754847092020977174315875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1006462789361302899087833 754847092020977174315875)
            ·
              refine ⟨1132270638031465761473813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754847092020977174315875 1132270638031465761473813)
              ·
                refine ⟨53075186157724957569085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1132270638031465761473813 53075186157724957569085)
                ·
                  rfl

theorem cell21_697704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_697704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697704 prefixEnd_697704 := by exact prefixLift 697704
  have htrace : WordTrace (prefixWord ++ tailWord_697704) baseStart_697704 baseEnd_697704 := by
    simpa [prefixWord, tailWord_697704, baseEnd_697704] using wordTrace_append hprefix tailTrace_697704
  have hstable : (prefixWord ++ tailWord_697704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697704).length < 2 ^ (prefixWord ++ tailWord_697704).sum := by decide
  have hdescent : baseEnd_697704 < baseStart_697704 := by decide
  rcases family_descends (prefixWord ++ tailWord_697704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697735 : List Nat := [1, 1, 4, 2, 2, 3, 2, 3, 3]
def baseStart_697735 : Nat := 118140960795 + 697735 * 2 ^ 59
def prefixEnd_697735 : Nat := 4983230072969 + 3 ^ 40 * 697735 * 2
def baseEnd_697735 : Nat := 159232633095525707690525

theorem tailTrace_697735 : CollatzResearch.WordTrace tailWord_697735 prefixEnd_697735 159232633095525707690525 := by
  unfold tailWord_697735
  simp only [CollatzResearch.WordTrace]
  refine ⟨25448486127232733496006659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16965657418155155664004439 25448486127232733496006659)
  ·
    refine ⟨38172729190849100244009989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25448486127232733496006659 38172729190849100244009989)
    ·
      refine ⟨7157386723284206295751873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38172729190849100244009989 7157386723284206295751873)
      ·
        refine ⟨5368040042463154721813905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7157386723284206295751873 5368040042463154721813905)
        ·
          refine ⟨4026030031847366041360429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5368040042463154721813905 4026030031847366041360429)
          ·
            refine ⟨1509761261942762265510161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4026030031847366041360429 1509761261942762265510161)
            ·
              refine ⟨1132320946457071699132621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1509761261942762265510161 1132320946457071699132621)
              ·
                refine ⟨424620354921401887174733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1132320946457071699132621 424620354921401887174733)
                ·
                  refine ⟨159232633095525707690525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424620354921401887174733 159232633095525707690525)
                  ·
                    rfl

theorem cell21_697735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 3].length) (baseStart_697735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697735 prefixEnd_697735 := by exact prefixLift 697735
  have htrace : WordTrace (prefixWord ++ tailWord_697735) baseStart_697735 baseEnd_697735 := by
    simpa [prefixWord, tailWord_697735, baseEnd_697735] using wordTrace_append hprefix tailTrace_697735
  have hstable : (prefixWord ++ tailWord_697735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697735).length < 2 ^ (prefixWord ++ tailWord_697735).sum := by decide
  have hdescent : baseEnd_697735 < baseStart_697735 := by decide
  rcases family_descends (prefixWord ++ tailWord_697735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697777 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 5]
def baseStart_697777 : Nat := 118140960795 + 697777 * 2 ^ 59
def prefixEnd_697777 : Nat := 4983230072969 + 3 ^ 40 * 697777 * 2
def baseEnd_697777 : Nat := 159242218067742967990439

theorem tailTrace_697777 : CollatzResearch.WordTrace tailWord_697777 prefixEnd_697777 159242218067742967990439 := by
  unfold tailWord_697777
  simp only [CollatzResearch.WordTrace]
  refine ⟨25450017993080574669035585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16966678662053716446023723 25450017993080574669035585)
  ·
    refine ⟨19087513494810431001776689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25450017993080574669035585 19087513494810431001776689)
    ·
      refine ⟨14315635121107823251332517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19087513494810431001776689 14315635121107823251332517)
      ·
        refine ⟨2684181585207716859624847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14315635121107823251332517 2684181585207716859624847)
        ·
          refine ⟨4026272377811575289437271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684181585207716859624847 4026272377811575289437271)
          ·
            refine ⟨6039408566717362934155907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026272377811575289437271 6039408566717362934155907)
            ·
              refine ⟨9059112850076044401233861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6039408566717362934155907 9059112850076044401233861)
              ·
                refine ⟨1698583659389258325231349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9059112850076044401233861 1698583659389258325231349)
                ·
                  refine ⟨159242218067742967990439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1698583659389258325231349 159242218067742967990439)
                  ·
                    rfl

theorem cell21_697777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_697777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697777 prefixEnd_697777 := by exact prefixLift 697777
  have htrace : WordTrace (prefixWord ++ tailWord_697777) baseStart_697777 baseEnd_697777 := by
    simpa [prefixWord, tailWord_697777, baseEnd_697777] using wordTrace_append hprefix tailTrace_697777
  have hstable : (prefixWord ++ tailWord_697777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697777).length < 2 ^ (prefixWord ++ tailWord_697777).sum := by decide
  have hdescent : baseEnd_697777 < baseStart_697777 := by decide
  rcases family_descends (prefixWord ++ tailWord_697777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697825 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 4]
def baseStart_697825 : Nat := 118140960795 + 697825 * 2 ^ 59
def prefixEnd_697825 : Nat := 4983230072969 + 3 ^ 40 * 697825 * 2
def baseEnd_697825 : Nat := 159253172321705551190341

theorem tailTrace_697825 : CollatzResearch.WordTrace tailWord_697825 prefixEnd_697825 159253172321705551190341 := by
  unfold tailWord_697825
  simp only [CollatzResearch.WordTrace]
  refine ⟨25451768696906678866782929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16967845797937785911188619 25451768696906678866782929)
  ·
    refine ⟨19088826522680009150087197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25451768696906678866782929 19088826522680009150087197)
    ·
      refine ⟨7158309946005003431282699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19088826522680009150087197 7158309946005003431282699)
      ·
        refine ⟨10737464919007505146924049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7158309946005003431282699 10737464919007505146924049)
        ·
          refine ⟨8053098689255628860193037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10737464919007505146924049 8053098689255628860193037)
          ·
            refine ⟨3019912008470860822572389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8053098689255628860193037 3019912008470860822572389)
            ·
              refine ⟨566233501588286404232323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3019912008470860822572389 566233501588286404232323)
              ·
                refine ⟨849350252382429606348485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566233501588286404232323 849350252382429606348485)
                ·
                  refine ⟨159253172321705551190341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 849350252382429606348485 159253172321705551190341)
                  ·
                    rfl

theorem cell21_697825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_697825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697825 prefixEnd_697825 := by exact prefixLift 697825
  have htrace : WordTrace (prefixWord ++ tailWord_697825) baseStart_697825 baseEnd_697825 := by
    simpa [prefixWord, tailWord_697825, baseEnd_697825] using wordTrace_append hprefix tailTrace_697825
  have hstable : (prefixWord ++ tailWord_697825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697825).length < 2 ^ (prefixWord ++ tailWord_697825).sum := by decide
  have hdescent : baseEnd_697825 < baseStart_697825 := by decide
  rcases family_descends (prefixWord ++ tailWord_697825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697862 : List Nat := [6, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_697862 : Nat := 118140960795 + 697862 * 2 ^ 59
def prefixEnd_697862 : Nat := 4983230072969 + 3 ^ 40 * 697862 * 2
def baseEnd_697862 : Nat := 159261616225801709073599

theorem tailTrace_697862 : CollatzResearch.WordTrace tailWord_697862 prefixEnd_697862 159261616225801709073599 := by
  unfold tailWord_697862
  simp only [CollatzResearch.WordTrace]
  refine ⟨795409943680394818308745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16968745465181756123919893 795409943680394818308745)
  ·
    refine ⟨596557457760296113731559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 795409943680394818308745 596557457760296113731559)
    ·
      refine ⟨894836186640444170597339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 596557457760296113731559 894836186640444170597339)
      ·
        refine ⟨1342254279960666255896009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 894836186640444170597339 1342254279960666255896009)
        ·
          refine ⟨1006690709970499691922007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1342254279960666255896009 1006690709970499691922007)
          ·
            refine ⟨1510036064955749537883011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006690709970499691922007 1510036064955749537883011)
            ·
              refine ⟨2265054097433624306824517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510036064955749537883011 2265054097433624306824517)
              ·
                refine ⟨424697643268804557529597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2265054097433624306824517 424697643268804557529597)
                ·
                  refine ⟨159261616225801709073599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424697643268804557529597 159261616225801709073599)
                  ·
                    rfl

theorem cell21_697862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_697862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697862 prefixEnd_697862 := by exact prefixLift 697862
  have htrace : WordTrace (prefixWord ++ tailWord_697862) baseStart_697862 baseEnd_697862 := by
    simpa [prefixWord, tailWord_697862, baseEnd_697862] using wordTrace_append hprefix tailTrace_697862
  have hstable : (prefixWord ++ tailWord_697862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697862).length < 2 ^ (prefixWord ++ tailWord_697862).sum := by decide
  have hdescent : baseEnd_697862 < baseStart_697862 := by decide
  rcases family_descends (prefixWord ++ tailWord_697862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697884 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 4]
def baseStart_697884 : Nat := 118140960795 + 697884 * 2 ^ 59
def prefixEnd_697884 : Nat := 4983230072969 + 3 ^ 40 * 697884 * 2
def baseEnd_697884 : Nat := 159266636925534559706887

theorem tailTrace_697884 : CollatzResearch.WordTrace tailWord_697884 prefixEnd_697884 159266636925534559706887 := by
  unfold tailWord_697884
  simp only [CollatzResearch.WordTrace]
  refine ⟨12726960301846465971590353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16969280402461954628787137 12726960301846465971590353)
  ·
    refine ⟨9545220226384849478692765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12726960301846465971590353 9545220226384849478692765)
    ·
      refine ⟨3579457584894318554509787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9545220226384849478692765 3579457584894318554509787)
      ·
        refine ⟨5369186377341477831764681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579457584894318554509787 5369186377341477831764681)
        ·
          refine ⟨4026889783006108373823511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5369186377341477831764681 4026889783006108373823511)
          ·
            refine ⟨6040334674509162560735267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026889783006108373823511 6040334674509162560735267)
            ·
              refine ⟨9060502011763743841102901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040334674509162560735267 9060502011763743841102901)
              ·
                refine ⟨849422063602850985103397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9060502011763743841102901 849422063602850985103397)
                ·
                  refine ⟨159266636925534559706887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 849422063602850985103397 159266636925534559706887)
                  ·
                    rfl

theorem cell21_697884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_697884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697884 prefixEnd_697884 := by exact prefixLift 697884
  have htrace : WordTrace (prefixWord ++ tailWord_697884) baseStart_697884 baseEnd_697884 := by
    simpa [prefixWord, tailWord_697884, baseEnd_697884] using wordTrace_append hprefix tailTrace_697884
  have hstable : (prefixWord ++ tailWord_697884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697884).length < 2 ^ (prefixWord ++ tailWord_697884).sum := by decide
  have hdescent : baseEnd_697884 < baseStart_697884 := by decide
  rcases family_descends (prefixWord ++ tailWord_697884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697960 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 6]
def baseStart_697960 : Nat := 118140960795 + 697960 * 2 ^ 59
def prefixEnd_697960 : Nat := 4983230072969 + 3 ^ 40 * 697960 * 2
def baseEnd_697960 : Nat := 159283981160975316440065

theorem tailTrace_697960 : CollatzResearch.WordTrace tailWord_697960 prefixEnd_697960 159283981160975316440065 := by
  unfold tailWord_697960
  simp only [CollatzResearch.WordTrace]
  refine ⟨12728346275708798461473667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16971128367611731281964889 12728346275708798461473667)
  ·
    refine ⟨19092519413563197692210501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12728346275708798461473667 19092519413563197692210501)
    ·
      refine ⟨3579847390043099567289469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19092519413563197692210501 3579847390043099567289469)
      ·
        refine ⟨1342442771266162337733551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3579847390043099567289469 1342442771266162337733551)
        ·
          refine ⟨2013664156899243506600327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1342442771266162337733551 2013664156899243506600327)
          ·
            refine ⟨3020496235348865259900491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013664156899243506600327 3020496235348865259900491)
            ·
              refine ⟨4530744353023297889850737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020496235348865259900491 4530744353023297889850737)
              ·
                refine ⟨3398058264767473417388053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4530744353023297889850737 3398058264767473417388053)
                ·
                  refine ⟨159283981160975316440065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3398058264767473417388053 159283981160975316440065)
                  ·
                    rfl

theorem cell21_697960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_697960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697960 prefixEnd_697960 := by exact prefixLift 697960
  have htrace : WordTrace (prefixWord ++ tailWord_697960) baseStart_697960 baseEnd_697960 := by
    simpa [prefixWord, tailWord_697960, baseEnd_697960] using wordTrace_append hprefix tailTrace_697960
  have hstable : (prefixWord ++ tailWord_697960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697960).length < 2 ^ (prefixWord ++ tailWord_697960).sum := by decide
  have hdescent : baseEnd_697960 < baseStart_697960 := by decide
  rcases family_descends (prefixWord ++ tailWord_697960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697994 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_697994 : Nat := 118140960795 + 697994 * 2 ^ 59
def prefixEnd_697994 : Nat := 4983230072969 + 3 ^ 40 * 697994 * 2
def baseEnd_697994 : Nat := 159291740424198812873329

theorem tailTrace_697994 : CollatzResearch.WordTrace tailWord_697994 prefixEnd_697994 159291740424198812873329 := by
  unfold tailWord_697994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6364483158323605182421259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16971955088862947153123357 6364483158323605182421259)
  ·
    refine ⟨9546724737485407773631889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6364483158323605182421259 9546724737485407773631889)
    ·
      refine ⟨7160043553114055830223917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9546724737485407773631889 7160043553114055830223917)
      ·
        refine ⟨2685016332417770936333969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7160043553114055830223917 2685016332417770936333969)
        ·
          refine ⟨2013762249313328202250477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2685016332417770936333969 2013762249313328202250477)
          ·
            refine ⟨755160843492498075843929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2013762249313328202250477 755160843492498075843929)
            ·
              refine ⟨566370632619373556882947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755160843492498075843929 566370632619373556882947)
              ·
                refine ⟨849555948929060335324421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566370632619373556882947 849555948929060335324421)
                ·
                  refine ⟨159291740424198812873329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 849555948929060335324421 159291740424198812873329)
                  ·
                    rfl

theorem cell21_697994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_697994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_697994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_697994 prefixEnd_697994 := by exact prefixLift 697994
  have htrace : WordTrace (prefixWord ++ tailWord_697994) baseStart_697994 baseEnd_697994 := by
    simpa [prefixWord, tailWord_697994, baseEnd_697994] using wordTrace_append hprefix tailTrace_697994
  have hstable : (prefixWord ++ tailWord_697994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697994).length < 2 ^ (prefixWord ++ tailWord_697994).sum := by decide
  have hdescent : baseEnd_697994 < baseStart_697994 := by decide
  rcases family_descends (prefixWord ++ tailWord_697994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698033 : List Nat := [1, 2, 2, 16]
def baseStart_698033 : Nat := 118140960795 + 698033 * 2 ^ 59
def prefixEnd_698033 : Nat := 4983230072969 + 3 ^ 40 * 698033 * 2
def baseEnd_698033 : Nat := 655558192409643669643

theorem tailTrace_698033 : CollatzResearch.WordTrace tailWord_698033 prefixEnd_698033 655558192409643669643 := by
  unfold tailWord_698033
  simp only [CollatzResearch.WordTrace]
  refine ⟨25459355080153130390354753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16972903386768753593569835 25459355080153130390354753)
  ·
    refine ⟨19094516310114847792766065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25459355080153130390354753 19094516310114847792766065)
    ·
      refine ⟨14320887232586135844574549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19094516310114847792766065 14320887232586135844574549)
      ·
        refine ⟨655558192409643669643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 14320887232586135844574549 655558192409643669643)
        ·
          rfl

theorem cell21_698033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 16].length) (baseStart_698033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698033 prefixEnd_698033 := by exact prefixLift 698033
  have htrace : WordTrace (prefixWord ++ tailWord_698033) baseStart_698033 baseEnd_698033 := by
    simpa [prefixWord, tailWord_698033, baseEnd_698033] using wordTrace_append hprefix tailTrace_698033
  have hstable : (prefixWord ++ tailWord_698033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698033).length < 2 ^ (prefixWord ++ tailWord_698033).sum := by decide
  have hdescent : baseEnd_698033 < baseStart_698033 := by decide
  rcases family_descends (prefixWord ++ tailWord_698033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698039 : List Nat := [1, 1, 3, 1, 5, 1, 4, 2, 3]
def baseStart_698039 : Nat := 118140960795 + 698039 * 2 ^ 59
def prefixEnd_698039 : Nat := 4983230072969 + 3 ^ 40 * 698039 * 2
def baseEnd_698039 : Nat := 159302010037288734623237

theorem tailTrace_698039 : CollatzResearch.WordTrace tailWord_698039 prefixEnd_698039 159302010037288734623237 := by
  unfold tailWord_698039
  simp only [CollatzResearch.WordTrace]
  refine ⟨25459573918131393415073171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16973049278754262276715447 25459573918131393415073171)
  ·
    refine ⟨38189360877197090122609757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25459573918131393415073171 38189360877197090122609757)
    ·
      refine ⟨14321010328948908795978659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38189360877197090122609757 14321010328948908795978659)
      ·
        refine ⟨21481515493423363193967989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14321010328948908795978659 21481515493423363193967989)
        ·
          refine ⟨2013892077508440299434499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21481515493423363193967989 2013892077508440299434499)
          ·
            refine ⟨3020838116262660449151749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013892077508440299434499 3020838116262660449151749)
            ·
              refine ⟨566407146799248834215953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3020838116262660449151749 566407146799248834215953)
              ·
                refine ⟨424805360099436625661965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566407146799248834215953 424805360099436625661965)
                ·
                  refine ⟨159302010037288734623237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424805360099436625661965 159302010037288734623237)
                  ·
                    rfl

theorem cell21_698039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 3].length) (baseStart_698039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698039 prefixEnd_698039 := by exact prefixLift 698039
  have htrace : WordTrace (prefixWord ++ tailWord_698039) baseStart_698039 baseEnd_698039 := by
    simpa [prefixWord, tailWord_698039, baseEnd_698039] using wordTrace_append hprefix tailTrace_698039
  have hstable : (prefixWord ++ tailWord_698039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698039).length < 2 ^ (prefixWord ++ tailWord_698039).sum := by decide
  have hdescent : baseEnd_698039 < baseStart_698039 := by decide
  rcases family_descends (prefixWord ++ tailWord_698039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698087 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 4]
def baseStart_698087 : Nat := 118140960795 + 698087 * 2 ^ 59
def prefixEnd_698087 : Nat := 4983230072969 + 3 ^ 40 * 698087 * 2
def baseEnd_698087 : Nat := 159312964291251317823139

theorem tailTrace_698087 : CollatzResearch.WordTrace tailWord_698087 prefixEnd_698087 159312964291251317823139 := by
  unfold tailWord_698087
  simp only [CollatzResearch.WordTrace]
  refine ⟨25461324621957497612820515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16974216414638331741880343 25461324621957497612820515)
  ·
    refine ⟨38191986932936246419230773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25461324621957497612820515 38191986932936246419230773)
    ·
      refine ⟨3580498774962773101802885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38191986932936246419230773 3580498774962773101802885)
      ·
        refine ⟨671343520305519956588041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3580498774962773101802885 671343520305519956588041)
        ·
          refine ⟨503507640229139967441031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671343520305519956588041 503507640229139967441031)
          ·
            refine ⟨755261460343709951161547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503507640229139967441031 755261460343709951161547)
            ·
              refine ⟨1132892190515564926742321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755261460343709951161547 1132892190515564926742321)
              ·
                refine ⟨849669142886673695056741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1132892190515564926742321 849669142886673695056741)
                ·
                  refine ⟨159312964291251317823139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 849669142886673695056741 159312964291251317823139)
                  ·
                    rfl

theorem cell21_698087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 4].length) (baseStart_698087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698087 prefixEnd_698087 := by exact prefixLift 698087
  have htrace : WordTrace (prefixWord ++ tailWord_698087) baseStart_698087 baseEnd_698087 := by
    simpa [prefixWord, tailWord_698087, baseEnd_698087] using wordTrace_append hprefix tailTrace_698087
  have hstable : (prefixWord ++ tailWord_698087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698087).length < 2 ^ (prefixWord ++ tailWord_698087).sum := by decide
  have hdescent : baseEnd_698087 < baseStart_698087 := by decide
  rcases family_descends (prefixWord ++ tailWord_698087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698095 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 6]
def baseStart_698095 : Nat := 118140960795 + 698095 * 2 ^ 59
def prefixEnd_698095 : Nat := 4983230072969 + 3 ^ 40 * 698095 * 2
def baseEnd_698095 : Nat := 159314790000245081689789

theorem tailTrace_698095 : CollatzResearch.WordTrace tailWord_698095 prefixEnd_698095 159314790000245081689789 := by
  unfold tailWord_698095
  simp only [CollatzResearch.WordTrace]
  refine ⟨25461616405928514979111739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16974410937285676652741159 25461616405928514979111739)
  ·
    refine ⟨38192424608892772468667609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25461616405928514979111739 38192424608892772468667609)
    ·
      refine ⟨28644318456669579351500707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38192424608892772468667609 28644318456669579351500707)
      ·
        refine ⟨42966477685004369027251061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28644318456669579351500707 42966477685004369027251061)
        ·
          refine ⟨4028107282969159596304787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42966477685004369027251061 4028107282969159596304787)
          ·
            refine ⟨6042160924453739394457181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028107282969159596304787 6042160924453739394457181)
            ·
              refine ⟨2265810346670152272921443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6042160924453739394457181 2265810346670152272921443)
              ·
                refine ⟨3398715520005228409382165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265810346670152272921443 3398715520005228409382165)
                ·
                  refine ⟨159314790000245081689789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3398715520005228409382165 159314790000245081689789)
                  ·
                    rfl

theorem cell21_698095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_698095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698095 prefixEnd_698095 := by exact prefixLift 698095
  have htrace : WordTrace (prefixWord ++ tailWord_698095) baseStart_698095 baseEnd_698095 := by
    simpa [prefixWord, tailWord_698095, baseEnd_698095] using wordTrace_append hprefix tailTrace_698095
  have hstable : (prefixWord ++ tailWord_698095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698095).length < 2 ^ (prefixWord ++ tailWord_698095).sum := by decide
  have hdescent : baseEnd_698095 < baseStart_698095 := by decide
  rcases family_descends (prefixWord ++ tailWord_698095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698098 : List Nat := [3, 2, 1, 3, 1, 1, 1, 6, 3]
def baseStart_698098 : Nat := 118140960795 + 698098 * 2 ^ 59
def prefixEnd_698098 : Nat := 4983230072969 + 3 ^ 40 * 698098 * 2
def baseEnd_698098 : Nat := 159315474641117743139783

theorem tailTrace_698098 : CollatzResearch.WordTrace tailWord_698098 prefixEnd_698098 159315474641117743139783 := by
  unfold tailWord_698098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6365431456229411622867737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16974483883278430994313965 6365431456229411622867737)
  ·
    refine ⟨4774073592172058717150803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6365431456229411622867737 4774073592172058717150803)
    ·
      refine ⟨7161110388258088075726205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4774073592172058717150803 7161110388258088075726205)
      ·
        refine ⟨2685416395596783028397327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7161110388258088075726205 2685416395596783028397327)
        ·
          refine ⟨4028124593395174542595991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2685416395596783028397327 4028124593395174542595991)
          ·
            refine ⟨6042186890092761813893987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028124593395174542595991 6042186890092761813893987)
            ·
              refine ⟨9063280335139142720840981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6042186890092761813893987 9063280335139142720840981)
              ·
                refine ⟨424841265709647315039421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9063280335139142720840981 424841265709647315039421)
                ·
                  refine ⟨159315474641117743139783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424841265709647315039421 159315474641117743139783)
                  ·
                    rfl

theorem cell21_698098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_698098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698098 prefixEnd_698098 := by exact prefixLift 698098
  have htrace : WordTrace (prefixWord ++ tailWord_698098) baseStart_698098 baseEnd_698098 := by
    simpa [prefixWord, tailWord_698098, baseEnd_698098] using wordTrace_append hprefix tailTrace_698098
  have hstable : (prefixWord ++ tailWord_698098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698098).length < 2 ^ (prefixWord ++ tailWord_698098).sum := by decide
  have hdescent : baseEnd_698098 < baseStart_698098 := by decide
  rcases family_descends (prefixWord ++ tailWord_698098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698185 : List Nat := [1, 2, 1, 1, 2, 4, 1, 9]
def baseStart_698185 : Nat := 118140960795 + 698185 * 2 ^ 59
def prefixEnd_698185 : Nat := 4983230072969 + 3 ^ 40 * 698185 * 2
def baseEnd_698185 : Nat := 53111776408808308396535

theorem tailTrace_698185 : CollatzResearch.WordTrace tailWord_698185 prefixEnd_698185 53111776408808308396535 := by
  unfold tailWord_698185
  simp only [CollatzResearch.WordTrace]
  refine ⟨25464898975602460349888009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16976599317068306899925339 25464898975602460349888009)
  ·
    refine ⟨19098674231701845262416007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25464898975602460349888009 19098674231701845262416007)
    ·
      refine ⟨28648011347552767893624011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19098674231701845262416007 28648011347552767893624011)
      ·
        refine ⟨42972017021329151840436017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28648011347552767893624011 42972017021329151840436017)
        ·
          refine ⟨32229012765996863880327013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42972017021329151840436017 32229012765996863880327013)
          ·
            refine ⟨6042939893624411977561315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32229012765996863880327013 6042939893624411977561315)
            ·
              refine ⟨9064409840436617966341973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6042939893624411977561315 9064409840436617966341973)
              ·
                refine ⟨53111776408808308396535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9064409840436617966341973 53111776408808308396535)
                ·
                  rfl

theorem cell21_698185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 9].length) (baseStart_698185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698185 prefixEnd_698185 := by exact prefixLift 698185
  have htrace : WordTrace (prefixWord ++ tailWord_698185) baseStart_698185 baseEnd_698185 := by
    simpa [prefixWord, tailWord_698185, baseEnd_698185] using wordTrace_append hprefix tailTrace_698185
  have hstable : (prefixWord ++ tailWord_698185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698185).length < 2 ^ (prefixWord ++ tailWord_698185).sum := by decide
  have hdescent : baseEnd_698185 < baseStart_698185 := by decide
  rcases family_descends (prefixWord ++ tailWord_698185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698261 : List Nat := [1, 3, 2, 1, 1, 3, 10]
def baseStart_698261 : Nat := 118140960795 + 698261 * 2 ^ 59
def prefixEnd_698261 : Nat := 4983230072969 + 3 ^ 40 * 698261 * 2
def baseEnd_698261 : Nat := 17705852606873964658087

theorem tailTrace_698261 : CollatzResearch.WordTrace tailWord_698261 prefixEnd_698261 17705852606873964658087 := by
  unfold tailWord_698261
  simp only [CollatzResearch.WordTrace]
  refine ⟨25467670923327125329654637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16978447282218083553103091 25467670923327125329654637)
  ·
    refine ⟨9550376596247671998620489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25467670923327125329654637 9550376596247671998620489)
    ·
      refine ⟨7162782447185753998965367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9550376596247671998620489 7162782447185753998965367)
      ·
        refine ⟨10744173670778630998448051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7162782447185753998965367 10744173670778630998448051)
        ·
          refine ⟨16116260506167946497672077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10744173670778630998448051 16116260506167946497672077)
          ·
            refine ⟨6043597689812979936627029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16116260506167946497672077 6043597689812979936627029)
            ·
              refine ⟨17705852606873964658087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6043597689812979936627029 17705852606873964658087)
              ·
                rfl

theorem cell21_698261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 10].length) (baseStart_698261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698261 prefixEnd_698261 := by exact prefixLift 698261
  have htrace : WordTrace (prefixWord ++ tailWord_698261) baseStart_698261 baseEnd_698261 := by
    simpa [prefixWord, tailWord_698261, baseEnd_698261] using wordTrace_append hprefix tailTrace_698261
  have hstable : (prefixWord ++ tailWord_698261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698261).length < 2 ^ (prefixWord ++ tailWord_698261).sum := by decide
  have hdescent : baseEnd_698261 < baseStart_698261 := by decide
  rcases family_descends (prefixWord ++ tailWord_698261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698309 : List Nat := [1, 3, 1, 1, 1, 1, 1, 9, 3]
def baseStart_698309 : Nat := 118140960795 + 698309 * 2 ^ 59
def prefixEnd_698309 : Nat := 4983230072969 + 3 ^ 40 * 698309 * 2
def baseEnd_698309 : Nat := 159363627715828265122685

theorem tailTrace_698309 : CollatzResearch.WordTrace tailWord_698309 prefixEnd_698309 159363627715828265122685 := by
  unfold tailWord_698309
  simp only [CollatzResearch.WordTrace]
  refine ⟨25469421627153229527401981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16979614418102153018267987 25469421627153229527401981)
  ·
    refine ⟨9551033110182461072775743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25469421627153229527401981 9551033110182461072775743)
    ·
      refine ⟨14326549665273691609163615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9551033110182461072775743 14326549665273691609163615)
      ·
        refine ⟨21489824497910537413745423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14326549665273691609163615 21489824497910537413745423)
        ·
          refine ⟨32234736746865806120618135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21489824497910537413745423 32234736746865806120618135)
          ·
            refine ⟨48352105120298709180927203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32234736746865806120618135 48352105120298709180927203)
            ·
              refine ⟨72528157680448063771390805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48352105120298709180927203 72528157680448063771390805)
              ·
                refine ⟨424969673908875373660493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 72528157680448063771390805 424969673908875373660493)
                ·
                  refine ⟨159363627715828265122685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424969673908875373660493 159363627715828265122685)
                  ·
                    rfl

theorem cell21_698309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_698309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698309 prefixEnd_698309 := by exact prefixLift 698309
  have htrace : WordTrace (prefixWord ++ tailWord_698309) baseStart_698309 baseEnd_698309 := by
    simpa [prefixWord, tailWord_698309, baseEnd_698309] using wordTrace_append hprefix tailTrace_698309
  have hstable : (prefixWord ++ tailWord_698309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698309).length < 2 ^ (prefixWord ++ tailWord_698309).sum := by decide
  have hdescent : baseEnd_698309 < baseStart_698309 := by decide
  rcases family_descends (prefixWord ++ tailWord_698309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698332 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 4]
def baseStart_698332 : Nat := 118140960795 + 698332 * 2 ^ 59
def prefixEnd_698332 : Nat := 4983230072969 + 3 ^ 40 * 698332 * 2
def baseEnd_698332 : Nat := 159368876629185336239305

theorem tailTrace_698332 : CollatzResearch.WordTrace tailWord_698332 prefixEnd_698332 159368876629185336239305 := by
  unfold tailWord_698332
  simp only [CollatzResearch.WordTrace]
  refine ⟨12735130253034952227744625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16980173670713269636992833 12735130253034952227744625)
  ·
    refine ⟨9551347689776214170808469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12735130253034952227744625 9551347689776214170808469)
    ·
      refine ⟨447719422958260039256647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9551347689776214170808469 447719422958260039256647)
      ·
        refine ⟨671579134437390058884971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447719422958260039256647 671579134437390058884971)
        ·
          refine ⟨1007368701656085088327457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671579134437390058884971 1007368701656085088327457)
          ·
            refine ⟨755526526242063816245593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1007368701656085088327457 755526526242063816245593)
            ·
              refine ⟨566644894681547862184195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755526526242063816245593 566644894681547862184195)
              ·
                refine ⟨849967342022321793276293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566644894681547862184195 849967342022321793276293)
                ·
                  refine ⟨159368876629185336239305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 849967342022321793276293 159368876629185336239305)
                  ·
                    rfl

theorem cell21_698332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_698332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698332 prefixEnd_698332 := by exact prefixLift 698332
  have htrace : WordTrace (prefixWord ++ tailWord_698332) baseStart_698332 baseEnd_698332 := by
    simpa [prefixWord, tailWord_698332, baseEnd_698332] using wordTrace_append hprefix tailTrace_698332
  have hstable : (prefixWord ++ tailWord_698332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698332).length < 2 ^ (prefixWord ++ tailWord_698332).sum := by decide
  have hdescent : baseEnd_698332 < baseStart_698332 := by decide
  rcases family_descends (prefixWord ++ tailWord_698332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698337 : List Nat := [1, 2, 3, 1, 2, 1, 3, 8]
def baseStart_698337 : Nat := 118140960795 + 698337 * 2 ^ 59
def prefixEnd_698337 : Nat := 4983230072969 + 3 ^ 40 * 698337 * 2
def baseEnd_698337 : Nat := 53123339232435479551987

theorem tailTrace_698337 : CollatzResearch.WordTrace tailWord_698337 prefixEnd_698337 53123339232435479551987 := by
  unfold tailWord_698337
  simp only [CollatzResearch.WordTrace]
  refine ⟨25470442871051790309421265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16980295247367860206280843 25470442871051790309421265)
  ·
    refine ⟨19102832153288842732065949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25470442871051790309421265 19102832153288842732065949)
    ·
      refine ⟨7163562057483316024524731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19102832153288842732065949 7163562057483316024524731)
      ·
        refine ⟨10745343086224974036787097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7163562057483316024524731 10745343086224974036787097)
        ·
          refine ⟨8059007314668730527590323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10745343086224974036787097 8059007314668730527590323)
          ·
            refine ⟨12088510972003095791385485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8059007314668730527590323 12088510972003095791385485)
            ·
              refine ⟨4533191614501160921769557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12088510972003095791385485 4533191614501160921769557)
              ·
                refine ⟨53123339232435479551987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4533191614501160921769557 53123339232435479551987)
                ·
                  rfl

theorem cell21_698337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 8].length) (baseStart_698337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698337 prefixEnd_698337 := by exact prefixLift 698337
  have htrace : WordTrace (prefixWord ++ tailWord_698337) baseStart_698337 baseEnd_698337 := by
    simpa [prefixWord, tailWord_698337, baseEnd_698337] using wordTrace_append hprefix tailTrace_698337
  have hstable : (prefixWord ++ tailWord_698337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698337).length < 2 ^ (prefixWord ++ tailWord_698337).sum := by decide
  have hdescent : baseEnd_698337 < baseStart_698337 := by decide
  rcases family_descends (prefixWord ++ tailWord_698337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698399 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 4]
def baseStart_698399 : Nat := 118140960795 + 698399 * 2 ^ 59
def prefixEnd_698399 : Nat := 4983230072969 + 3 ^ 40 * 698399 * 2
def baseEnd_698399 : Nat := 159384166942008108622501

theorem tailTrace_698399 : CollatzResearch.WordTrace tailWord_698399 prefixEnd_698399 159384166942008108622501 := by
  unfold tailWord_698399
  simp only [CollatzResearch.WordTrace]
  refine ⟨25472704196827174898178251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16981802797884783265452167 25472704196827174898178251)
  ·
    refine ⟨38209056295240762347267377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25472704196827174898178251 38209056295240762347267377)
    ·
      refine ⟨28656792221430571760450533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38209056295240762347267377 28656792221430571760450533)
      ·
        refine ⟨5373148541518232205084475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28656792221430571760450533 5373148541518232205084475)
        ·
          refine ⟨8059722812277348307626713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5373148541518232205084475 8059722812277348307626713)
          ·
            refine ⟨6044792109208011230720035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8059722812277348307626713 6044792109208011230720035)
            ·
              refine ⟨9067188163812016846080053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6044792109208011230720035 9067188163812016846080053)
              ·
                refine ⟨850048890357376579320005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9067188163812016846080053 850048890357376579320005)
                ·
                  refine ⟨159384166942008108622501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850048890357376579320005 159384166942008108622501)
                  ·
                    rfl

theorem cell21_698399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 4].length) (baseStart_698399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698399 prefixEnd_698399 := by exact prefixLift 698399
  have htrace : WordTrace (prefixWord ++ tailWord_698399) baseStart_698399 baseEnd_698399 := by
    simpa [prefixWord, tailWord_698399, baseEnd_698399] using wordTrace_append hprefix tailTrace_698399
  have hstable : (prefixWord ++ tailWord_698399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698399).length < 2 ^ (prefixWord ++ tailWord_698399).sum := by decide
  have hdescent : baseEnd_698399 < baseStart_698399 := by decide
  rcases family_descends (prefixWord ++ tailWord_698399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698433 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 4]
def baseStart_698433 : Nat := 118140960795 + 698433 * 2 ^ 59
def prefixEnd_698433 : Nat := 4983230072969 + 3 ^ 40 * 698433 * 2
def baseEnd_698433 : Nat := 159391926205231605055765

theorem tailTrace_698433 : CollatzResearch.WordTrace tailWord_698433 prefixEnd_698433 159391926205231605055765 := by
  unfold tailWord_698433
  simp only [CollatzResearch.WordTrace]
  refine ⟨25473944278703998704915953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16982629519135999136610635 25473944278703998704915953)
  ·
    refine ⟨19105458209027999028686965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25473944278703998704915953 19105458209027999028686965)
    ·
      refine ⟨1791136707096374908939403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19105458209027999028686965 1791136707096374908939403)
      ·
        refine ⟨2686705060644562363409105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791136707096374908939403 2686705060644562363409105)
        ·
          refine ⟨2015028795483421772556829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2686705060644562363409105 2015028795483421772556829)
          ·
            refine ⟨755635798306283164708811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2015028795483421772556829 755635798306283164708811)
            ·
              refine ⟨1133453697459424747063217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755635798306283164708811 1133453697459424747063217)
              ·
                refine ⟨850090273094568560297413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133453697459424747063217 850090273094568560297413)
                ·
                  refine ⟨159391926205231605055765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850090273094568560297413 159391926205231605055765)
                  ·
                    rfl

theorem cell21_698433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_698433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698433 prefixEnd_698433 := by exact prefixLift 698433
  have htrace : WordTrace (prefixWord ++ tailWord_698433) baseStart_698433 baseEnd_698433 := by
    simpa [prefixWord, tailWord_698433, baseEnd_698433] using wordTrace_append hprefix tailTrace_698433
  have hstable : (prefixWord ++ tailWord_698433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698433).length < 2 ^ (prefixWord ++ tailWord_698433).sum := by decide
  have hdescent : baseEnd_698433 < baseStart_698433 := by decide
  rcases family_descends (prefixWord ++ tailWord_698433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698444 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_698444 : Nat := 118140960795 + 698444 * 2 ^ 59
def prefixEnd_698444 : Nat := 4983230072969 + 3 ^ 40 * 698444 * 2
def baseEnd_698444 : Nat := 159394436555098030372409

theorem tailTrace_698444 : CollatzResearch.WordTrace tailWord_698444 prefixEnd_698444 159394436555098030372409 := by
  unfold tailWord_698444
  simp only [CollatzResearch.WordTrace]
  refine ⟨12737172740832073791783193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16982896987776098389044257 12737172740832073791783193)
  ·
    refine ⟨9552879555624055343837395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12737172740832073791783193 9552879555624055343837395)
    ·
      refine ⟨14329319333436083015756093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9552879555624055343837395 14329319333436083015756093)
      ·
        refine ⟨5373494750038531130908535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14329319333436083015756093 5373494750038531130908535)
        ·
          refine ⟨8060242125057796696362803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5373494750038531130908535 8060242125057796696362803)
          ·
            refine ⟨12090363187586695044544205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8060242125057796696362803 12090363187586695044544205)
            ·
              refine ⟨4533886195345010641704077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12090363187586695044544205 4533886195345010641704077)
              ·
                refine ⟨1700207323254378990639029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4533886195345010641704077 1700207323254378990639029)
                ·
                  refine ⟨159394436555098030372409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1700207323254378990639029 159394436555098030372409)
                  ·
                    rfl

theorem cell21_698444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_698444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698444 prefixEnd_698444 := by exact prefixLift 698444
  have htrace : WordTrace (prefixWord ++ tailWord_698444) baseStart_698444 baseEnd_698444 := by
    simpa [prefixWord, tailWord_698444, baseEnd_698444] using wordTrace_append hprefix tailTrace_698444
  have hstable : (prefixWord ++ tailWord_698444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698444).length < 2 ^ (prefixWord ++ tailWord_698444).sum := by decide
  have hdescent : baseEnd_698444 < baseStart_698444 := by decide
  rcases family_descends (prefixWord ++ tailWord_698444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698489 : List Nat := [1, 2, 1, 3, 4, 1, 9]
def baseStart_698489 : Nat := 118140960795 + 698489 * 2 ^ 59
def prefixEnd_698489 : Nat := 4983230072969 + 3 ^ 40 * 698489 * 2
def baseEnd_698489 : Nat := 17711634018687550235813

theorem tailTrace_698489 : CollatzResearch.WordTrace tailWord_698489 prefixEnd_698489 17711634018687550235813 := by
  unfold tailWord_698489
  simp only [CollatzResearch.WordTrace]
  refine ⟨25475986766501120268954521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16983991177667413512636347 25475986766501120268954521)
  ·
    refine ⟨19106990074875840201715891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25475986766501120268954521 19106990074875840201715891)
    ·
      refine ⟨28660485112313760302573837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19106990074875840201715891 28660485112313760302573837)
      ·
        refine ⟨10747681917117660113465189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28660485112313760302573837 10747681917117660113465189)
        ·
          refine ⟨2015190359459561271274723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10747681917117660113465189 2015190359459561271274723)
          ·
            refine ⟨3022785539189341906912085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015190359459561271274723 3022785539189341906912085)
            ·
              refine ⟨17711634018687550235813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3022785539189341906912085 17711634018687550235813)
              ·
                rfl

theorem cell21_698489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 9].length) (baseStart_698489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698489 prefixEnd_698489 := by exact prefixLift 698489
  have htrace : WordTrace (prefixWord ++ tailWord_698489) baseStart_698489 baseEnd_698489 := by
    simpa [prefixWord, tailWord_698489, baseEnd_698489] using wordTrace_append hprefix tailTrace_698489
  have hstable : (prefixWord ++ tailWord_698489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698489).length < 2 ^ (prefixWord ++ tailWord_698489).sum := by decide
  have hdescent : baseEnd_698489 < baseStart_698489 := by decide
  rcases family_descends (prefixWord ++ tailWord_698489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698506 : List Nat := [3, 1, 2, 3, 1, 3, 2, 6]
def baseStart_698506 : Nat := 118140960795 + 698506 * 2 ^ 59
def prefixEnd_698506 : Nat := 4983230072969 + 3 ^ 40 * 698506 * 2
def baseEnd_698506 : Nat := 53136195266599900112983

theorem tailTrace_698506 : CollatzResearch.WordTrace tailWord_698506 prefixEnd_698506 53136195266599900112983 := by
  unfold tailWord_698506
  simp only [CollatzResearch.WordTrace]
  refine ⟨6369151701859883043080843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16984404538293021448215581 6369151701859883043080843)
  ·
    refine ⟨9553727552789824564621265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6369151701859883043080843 9553727552789824564621265)
    ·
      refine ⟨7165295664592368423465949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9553727552789824564621265 7165295664592368423465949)
      ·
        refine ⟨2686985874222138158799731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7165295664592368423465949 2686985874222138158799731)
        ·
          refine ⟨4030478811333207238199597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686985874222138158799731 4030478811333207238199597)
          ·
            refine ⟨1511429554249952714324849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4030478811333207238199597 1511429554249952714324849)
            ·
              refine ⟨1133572165687464535743637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511429554249952714324849 1133572165687464535743637)
              ·
                refine ⟨53136195266599900112983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1133572165687464535743637 53136195266599900112983)
                ·
                  rfl

theorem cell21_698506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_698506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698506 prefixEnd_698506 := by exact prefixLift 698506
  have htrace : WordTrace (prefixWord ++ tailWord_698506) baseStart_698506 baseEnd_698506 := by
    simpa [prefixWord, tailWord_698506, baseEnd_698506] using wordTrace_append hprefix tailTrace_698506
  have hstable : (prefixWord ++ tailWord_698506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698506).length < 2 ^ (prefixWord ++ tailWord_698506).sum := by decide
  have hdescent : baseEnd_698506 < baseStart_698506 := by decide
  rcases family_descends (prefixWord ++ tailWord_698506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698551 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 4]
def baseStart_698551 : Nat := 118140960795 + 698551 * 2 ^ 59
def prefixEnd_698551 : Nat := 4983230072969 + 3 ^ 40 * 698551 * 2
def baseEnd_698551 : Nat := 159418855412889622088857

theorem tailTrace_698551 : CollatzResearch.WordTrace tailWord_698551 prefixEnd_698551 159418855412889622088857 := by
  unfold tailWord_698551
  simp only [CollatzResearch.WordTrace]
  refine ⟨25478248092276504857711507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16985498728184336571807671 25478248092276504857711507)
  ·
    refine ⟨38217372138414757286567261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25478248092276504857711507 38217372138414757286567261)
    ·
      refine ⟨14331514551905533982462723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38217372138414757286567261 14331514551905533982462723)
      ·
        refine ⟨21497271827858300973694085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14331514551905533982462723 21497271827858300973694085)
        ·
          refine ⟨4030738467723431432567641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21497271827858300973694085 4030738467723431432567641)
          ·
            refine ⟨3023053850792573574425731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4030738467723431432567641 3023053850792573574425731)
            ·
              refine ⟨4534580776188860361638597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023053850792573574425731 4534580776188860361638597)
              ·
                refine ⟨850233895535411317807237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4534580776188860361638597 850233895535411317807237)
                ·
                  refine ⟨159418855412889622088857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850233895535411317807237 159418855412889622088857)
                  ·
                    rfl

theorem cell21_698551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 4].length) (baseStart_698551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698551 prefixEnd_698551 := by exact prefixLift 698551
  have htrace : WordTrace (prefixWord ++ tailWord_698551) baseStart_698551 baseEnd_698551 := by
    simpa [prefixWord, tailWord_698551, baseEnd_698551] using wordTrace_append hprefix tailTrace_698551
  have hstable : (prefixWord ++ tailWord_698551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698551).length < 2 ^ (prefixWord ++ tailWord_698551).sum := by decide
  have hdescent : baseEnd_698551 < baseStart_698551 := by decide
  rcases family_descends (prefixWord ++ tailWord_698551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698554 : List Nat := [3, 1, 1, 1, 2, 2, 6, 2, 3]
def baseStart_698554 : Nat := 118140960795 + 698554 * 2 ^ 59
def prefixEnd_698554 : Nat := 4983230072969 + 3 ^ 40 * 698554 * 2
def baseEnd_698554 : Nat := 159419540053762283538851

theorem tailTrace_698554 : CollatzResearch.WordTrace tailWord_698554 prefixEnd_698554 159419540053762283538851 := by
  unfold tailWord_698554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6369589377816409092517679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16985571674177090913380477 6369589377816409092517679)
  ·
    refine ⟨9554384066724613638776519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6369589377816409092517679 9554384066724613638776519)
    ·
      refine ⟨14331576100086920458164779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9554384066724613638776519 14331576100086920458164779)
      ·
        refine ⟨21497364150130380687247169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14331576100086920458164779 21497364150130380687247169)
        ·
          refine ⟨16123023112597785515435377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21497364150130380687247169 16123023112597785515435377)
          ·
            refine ⟨12092267334448339136576533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16123023112597785515435377 12092267334448339136576533)
            ·
              refine ⟨566825031302265897027025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12092267334448339136576533 566825031302265897027025)
              ·
                refine ⟨425118773476699422770269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566825031302265897027025 425118773476699422770269)
                ·
                  refine ⟨159419540053762283538851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425118773476699422770269 159419540053762283538851)
                  ·
                    rfl

theorem cell21_698554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_698554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698554 prefixEnd_698554 := by exact prefixLift 698554
  have htrace : WordTrace (prefixWord ++ tailWord_698554) baseStart_698554 baseEnd_698554 := by
    simpa [prefixWord, tailWord_698554, baseEnd_698554] using wordTrace_append hprefix tailTrace_698554
  have hstable : (prefixWord ++ tailWord_698554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698554).length < 2 ^ (prefixWord ++ tailWord_698554).sum := by decide
  have hdescent : baseEnd_698554 < baseStart_698554 := by decide
  rcases family_descends (prefixWord ++ tailWord_698554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698565 : List Nat := [1, 3, 1, 1, 1, 1, 7, 6]
def baseStart_698565 : Nat := 118140960795 + 698565 * 2 ^ 59
def prefixEnd_698565 : Nat := 4983230072969 + 3 ^ 40 * 698565 * 2
def baseEnd_698565 : Nat := 53140683467876236285165

theorem tailTrace_698565 : CollatzResearch.WordTrace tailWord_698565 prefixEnd_698565 53140683467876236285165 := by
  unfold tailWord_698565
  simp only [CollatzResearch.WordTrace]
  refine ⟨25478758714225785248721149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16985839142817190165814099 25478758714225785248721149)
  ·
    refine ⟨9554534517834669468270431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25478758714225785248721149 9554534517834669468270431)
    ·
      refine ⟨14331801776752004202405647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9554534517834669468270431 14331801776752004202405647)
      ·
        refine ⟨21497702665128006303608471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14331801776752004202405647 21497702665128006303608471)
        ·
          refine ⟨32246553997692009455412707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21497702665128006303608471 32246553997692009455412707)
          ·
            refine ⟨48369830996538014183119061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32246553997692009455412707 48369830996538014183119061)
            ·
              refine ⟨1133667913981359707416853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48369830996538014183119061 1133667913981359707416853)
              ·
                refine ⟨53140683467876236285165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1133667913981359707416853 53140683467876236285165)
                ·
                  rfl

theorem cell21_698565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 6].length) (baseStart_698565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698565 prefixEnd_698565 := by exact prefixLift 698565
  have htrace : WordTrace (prefixWord ++ tailWord_698565) baseStart_698565 baseEnd_698565 := by
    simpa [prefixWord, tailWord_698565, baseEnd_698565] using wordTrace_append hprefix tailTrace_698565
  have hstable : (prefixWord ++ tailWord_698565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698565).length < 2 ^ (prefixWord ++ tailWord_698565).sum := by decide
  have hdescent : baseEnd_698565 < baseStart_698565 := by decide
  rcases family_descends (prefixWord ++ tailWord_698565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698588 : List Nat := [2, 2, 5, 2, 1, 1, 2, 3, 3]
def baseStart_698588 : Nat := 118140960795 + 698588 * 2 ^ 59
def prefixEnd_698588 : Nat := 4983230072969 + 3 ^ 40 * 698588 * 2
def baseEnd_698588 : Nat := 159427299316985779972115

theorem tailTrace_698588 : CollatzResearch.WordTrace tailWord_698588 prefixEnd_698588 159427299316985779972115 := by
  unfold tailWord_698588
  simp only [CollatzResearch.WordTrace]
  refine ⟨12739798796571230088404209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16986398395428306784538945 12739798796571230088404209)
  ·
    refine ⟨9554849097428422566303157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12739798796571230088404209 9554849097428422566303157)
    ·
      refine ⟨895767102883914615590921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9554849097428422566303157 895767102883914615590921)
      ·
        refine ⟨671825327162935961693191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 895767102883914615590921 671825327162935961693191)
        ·
          refine ⟨1007737990744403942539787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671825327162935961693191 1007737990744403942539787)
          ·
            refine ⟨1511606986116605913809681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007737990744403942539787 1511606986116605913809681)
            ·
              refine ⟨1133705239587454435357261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511606986116605913809681 1133705239587454435357261)
              ·
                refine ⟨425139464845295413258973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1133705239587454435357261 425139464845295413258973)
                ·
                  refine ⟨159427299316985779972115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425139464845295413258973 159427299316985779972115)
                  ·
                    rfl

theorem cell21_698588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_698588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698588 prefixEnd_698588 := by exact prefixLift 698588
  have htrace : WordTrace (prefixWord ++ tailWord_698588) baseStart_698588 baseEnd_698588 := by
    simpa [prefixWord, tailWord_698588, baseEnd_698588] using wordTrace_append hprefix tailTrace_698588
  have hstable : (prefixWord ++ tailWord_698588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698588).length < 2 ^ (prefixWord ++ tailWord_698588).sum := by decide
  have hdescent : baseEnd_698588 < baseStart_698588 := by decide
  rcases family_descends (prefixWord ++ tailWord_698588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698641 : List Nat := [1, 2, 2, 1, 1, 6, 1, 7]
def baseStart_698641 : Nat := 118140960795 + 698641 * 2 ^ 59
def prefixEnd_698641 : Nat := 4983230072969 + 3 ^ 40 * 698641 * 2
def baseEnd_698641 : Nat := 53146464879689821862891

theorem tailTrace_698641 : CollatzResearch.WordTrace tailWord_698641 prefixEnd_698641 53146464879689821862891 := by
  unfold tailWord_698641
  simp only [CollatzResearch.WordTrace]
  refine ⟨25481530661950450228487777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16987687107966966818991851 25481530661950450228487777)
  ·
    refine ⟨19111147996462837671365833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25481530661950450228487777 19111147996462837671365833)
    ·
      refine ⟨14333360997347128253524375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19111147996462837671365833 14333360997347128253524375)
      ·
        refine ⟨21500041496020692380286563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14333360997347128253524375 21500041496020692380286563)
        ·
          refine ⟨32250062244031038570429845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21500041496020692380286563 32250062244031038570429845)
          ·
            refine ⟨1511721667688954932988899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32250062244031038570429845 1511721667688954932988899)
            ·
              refine ⟨2267582501533432399483349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511721667688954932988899 2267582501533432399483349)
              ·
                refine ⟨53146464879689821862891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2267582501533432399483349 53146464879689821862891)
                ·
                  rfl

theorem cell21_698641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 7].length) (baseStart_698641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698641 prefixEnd_698641 := by exact prefixLift 698641
  have htrace : WordTrace (prefixWord ++ tailWord_698641) baseStart_698641 baseEnd_698641 := by
    simpa [prefixWord, tailWord_698641, baseEnd_698641] using wordTrace_append hprefix tailTrace_698641
  have hstable : (prefixWord ++ tailWord_698641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698641).length < 2 ^ (prefixWord ++ tailWord_698641).sum := by decide
  have hdescent : baseEnd_698641 < baseStart_698641 := by decide
  rcases family_descends (prefixWord ++ tailWord_698641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698658 : List Nat := [3, 3, 1, 1, 3, 3, 7]
def baseStart_698658 : Nat := 118140960795 + 698658 * 2 ^ 59
def prefixEnd_698658 : Nat := 4983230072969 + 3 ^ 40 * 698658 * 2
def baseEnd_698658 : Nat := 17715919363409023756145

theorem tailTrace_698658 : CollatzResearch.WordTrace tailWord_698658 prefixEnd_698658 17715919363409023756145 := by
  unfold tailWord_698658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370537675722215532964157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16988100468592574754571085 6370537675722215532964157)
  ·
    refine ⟨2388951628395830824861559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6370537675722215532964157 2388951628395830824861559)
    ·
      refine ⟨3583427442593746237292339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388951628395830824861559 3583427442593746237292339)
      ·
        refine ⟨5375141163890619355938509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583427442593746237292339 5375141163890619355938509)
        ·
          refine ⟨2015677936458982258476941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5375141163890619355938509 2015677936458982258476941)
          ·
            refine ⟨755879226172118346928853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2015677936458982258476941 755879226172118346928853)
            ·
              refine ⟨17715919363409023756145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 755879226172118346928853 17715919363409023756145)
              ·
                rfl

theorem cell21_698658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 7].length) (baseStart_698658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698658 prefixEnd_698658 := by exact prefixLift 698658
  have htrace : WordTrace (prefixWord ++ tailWord_698658) baseStart_698658 baseEnd_698658 := by
    simpa [prefixWord, tailWord_698658, baseEnd_698658] using wordTrace_append hprefix tailTrace_698658
  have hstable : (prefixWord ++ tailWord_698658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698658).length < 2 ^ (prefixWord ++ tailWord_698658).sum := by decide
  have hdescent : baseEnd_698658 < baseStart_698658 := by decide
  rcases family_descends (prefixWord ++ tailWord_698658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698720 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 4]
def baseStart_698720 : Nat := 118140960795 + 698720 * 2 ^ 59
def prefixEnd_698720 : Nat := 4983230072969 + 3 ^ 40 * 698720 * 2
def baseEnd_698720 : Nat := 159457423515382883771845

theorem tailTrace_698720 : CollatzResearch.WordTrace tailWord_698720 prefixEnd_698720 159457423515382883771845 := by
  unfold tailWord_698720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12742206014332123360306807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16989608019109497813742409 12742206014332123360306807)
  ·
    refine ⟨19113309021498185040460211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12742206014332123360306807 19113309021498185040460211)
    ·
      refine ⟨28669963532247277560690317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19113309021498185040460211 28669963532247277560690317)
      ·
        refine ⟨10751236324592729085258869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28669963532247277560690317 10751236324592729085258869)
        ·
          refine ⟨1007928405430568351743019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10751236324592729085258869 1007928405430568351743019)
          ·
            refine ⟨1511892608145852527614529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007928405430568351743019 1511892608145852527614529)
            ·
              refine ⟨1133919456109389395710897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511892608145852527614529 1133919456109389395710897)
              ·
                refine ⟨850439592082042046783173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133919456109389395710897 850439592082042046783173)
                ·
                  refine ⟨159457423515382883771845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850439592082042046783173 159457423515382883771845)
                  ·
                    rfl

theorem cell21_698720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_698720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698720 prefixEnd_698720 := by exact prefixLift 698720
  have htrace : WordTrace (prefixWord ++ tailWord_698720) baseStart_698720 baseEnd_698720 := by
    simpa [prefixWord, tailWord_698720, baseEnd_698720] using wordTrace_append hprefix tailTrace_698720
  have hstable : (prefixWord ++ tailWord_698720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698720).length < 2 ^ (prefixWord ++ tailWord_698720).sum := by decide
  have hdescent : baseEnd_698720 < baseStart_698720 := by decide
  rcases family_descends (prefixWord ++ tailWord_698720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698782 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_698782 : Nat := 118140960795 + 698782 * 2 ^ 59
def prefixEnd_698782 : Nat := 4983230072969 + 3 ^ 40 * 698782 * 2
def baseEnd_698782 : Nat := 159471572760084553738385

theorem tailTrace_698782 : CollatzResearch.WordTrace tailWord_698782 prefixEnd_698782 159471572760084553738385 := by
  unfold tailWord_698782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3185834169304953913671325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16991115569626420872913733 3185834169304953913671325)
  ·
    refine ⟨1194687813489357717626747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3185834169304953913671325 1194687813489357717626747)
    ·
      refine ⟨1792031720234036576440121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1194687813489357717626747 1792031720234036576440121)
      ·
        refine ⟨1344023790175527432330091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1792031720234036576440121 1344023790175527432330091)
        ·
          refine ⟨2016035685263291148495137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344023790175527432330091 2016035685263291148495137)
          ·
            refine ⟨1512026763947468361371353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2016035685263291148495137 1512026763947468361371353)
            ·
              refine ⟨1134020072960601271028515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1512026763947468361371353 1134020072960601271028515)
              ·
                refine ⟨1701030109440901906542773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134020072960601271028515 1701030109440901906542773)
                ·
                  refine ⟨159471572760084553738385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1701030109440901906542773 159471572760084553738385)
                  ·
                    rfl

theorem cell21_698782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_698782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698782 prefixEnd_698782 := by exact prefixLift 698782
  have htrace : WordTrace (prefixWord ++ tailWord_698782) baseStart_698782 baseEnd_698782 := by
    simpa [prefixWord, tailWord_698782, baseEnd_698782] using wordTrace_append hprefix tailTrace_698782
  have hstable : (prefixWord ++ tailWord_698782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698782).length < 2 ^ (prefixWord ++ tailWord_698782).sum := by decide
  have hdescent : baseEnd_698782 < baseStart_698782 := by decide
  rcases family_descends (prefixWord ++ tailWord_698782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698855 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 4]
def baseStart_698855 : Nat := 118140960795 + 698855 * 2 ^ 59
def prefixEnd_698855 : Nat := 4983230072969 + 3 ^ 40 * 698855 * 2
def baseEnd_698855 : Nat := 159488232354652649021569

theorem tailTrace_698855 : CollatzResearch.WordTrace tailWord_698855 prefixEnd_698855 159488232354652649021569 := by
  unfold tailWord_698855
  simp only [CollatzResearch.WordTrace]
  refine ⟨25489335883175164776778019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16992890588783443184518679 25489335883175164776778019)
  ·
    refine ⟨38234003824762747165167029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25489335883175164776778019 38234003824762747165167029)
    ·
      refine ⟨3584437858571507546734409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38234003824762747165167029 3584437858571507546734409)
      ·
        refine ⟨2688328393928630660050807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3584437858571507546734409 2688328393928630660050807)
        ·
          refine ⟨4032492590892945990076211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688328393928630660050807 4032492590892945990076211)
          ·
            refine ⟨6048738886339418985114317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032492590892945990076211 6048738886339418985114317)
            ·
              refine ⟨2268277082377282119417869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6048738886339418985114317 2268277082377282119417869)
              ·
                refine ⟨850603905891480794781701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2268277082377282119417869 850603905891480794781701)
                ·
                  refine ⟨159488232354652649021569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850603905891480794781701 159488232354652649021569)
                  ·
                    rfl

theorem cell21_698855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 4].length) (baseStart_698855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698855 prefixEnd_698855 := by exact prefixLift 698855
  have htrace : WordTrace (prefixWord ++ tailWord_698855) baseStart_698855 baseEnd_698855 := by
    simpa [prefixWord, tailWord_698855, baseEnd_698855] using wordTrace_append hprefix tailTrace_698855
  have hstable : (prefixWord ++ tailWord_698855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698855).length < 2 ^ (prefixWord ++ tailWord_698855).sum := by decide
  have hdescent : baseEnd_698855 < baseStart_698855 := by decide
  rcases family_descends (prefixWord ++ tailWord_698855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698903 : List Nat := [1, 1, 3, 6, 1, 2, 1, 6]
def baseStart_698903 : Nat := 118140960795 + 698903 * 2 ^ 59
def prefixEnd_698903 : Nat := 4983230072969 + 3 ^ 40 * 698903 * 2
def baseEnd_698903 : Nat := 53166395536205077407157

theorem tailTrace_698903 : CollatzResearch.WordTrace tailWord_698903 prefixEnd_698903 53166395536205077407157 := by
  unfold tailWord_698903
  simp only [CollatzResearch.WordTrace]
  refine ⟨25491086587001268974525363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16994057724667512649683575 25491086587001268974525363)
  ·
    refine ⟨38236629880501903461788045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25491086587001268974525363 38236629880501903461788045)
    ·
      refine ⟨14338736205188213798170517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38236629880501903461788045 14338736205188213798170517)
      ·
        refine ⟨672128259618197521789243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14338736205188213798170517 672128259618197521789243)
        ·
          refine ⟨1008192389427296282683865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672128259618197521789243 1008192389427296282683865)
          ·
            refine ⟨756144292070472212012899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1008192389427296282683865 756144292070472212012899)
            ·
              refine ⟨1134216438105708318019349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756144292070472212012899 1134216438105708318019349)
              ·
                refine ⟨53166395536205077407157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1134216438105708318019349 53166395536205077407157)
                ·
                  rfl

theorem cell21_698903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 6].length) (baseStart_698903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698903 prefixEnd_698903 := by exact prefixLift 698903
  have htrace : WordTrace (prefixWord ++ tailWord_698903) baseStart_698903 baseEnd_698903 := by
    simpa [prefixWord, tailWord_698903, baseEnd_698903] using wordTrace_append hprefix tailTrace_698903
  have hstable : (prefixWord ++ tailWord_698903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698903).length < 2 ^ (prefixWord ++ tailWord_698903).sum := by decide
  have hdescent : baseEnd_698903 < baseStart_698903 := by decide
  rcases family_descends (prefixWord ++ tailWord_698903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698914 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_698914 : Nat := 118140960795 + 698914 * 2 ^ 59
def prefixEnd_698914 : Nat := 4983230072969 + 3 ^ 40 * 698914 * 2
def baseEnd_698914 : Nat := 159501696958481657538115

theorem tailTrace_698914 : CollatzResearch.WordTrace tailWord_698914 prefixEnd_698914 159501696958481657538115 := by
  unfold tailWord_698914
  simp only [CollatzResearch.WordTrace]
  refine ⟨6372871947490354463293949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16994325193307611902117197 6372871947490354463293949)
  ·
    refine ⟨2389826980308882923735231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6372871947490354463293949 2389826980308882923735231)
    ·
      refine ⟨3584740470463324385602847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2389826980308882923735231 3584740470463324385602847)
      ·
        refine ⟨5377110705694986578404271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3584740470463324385602847 5377110705694986578404271)
        ·
          refine ⟨8065666058542479867606407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5377110705694986578404271 8065666058542479867606407)
          ·
            refine ⟨12098499087813719801409611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8065666058542479867606407 12098499087813719801409611)
            ·
              refine ⟨18147748631720579702114417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12098499087813719801409611 18147748631720579702114417)
              ·
                refine ⟨13610811473790434776585813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18147748631720579702114417 13610811473790434776585813)
                ·
                  refine ⟨159501696958481657538115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13610811473790434776585813 159501696958481657538115)
                  ·
                    rfl

theorem cell21_698914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_698914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698914 prefixEnd_698914 := by exact prefixLift 698914
  have htrace : WordTrace (prefixWord ++ tailWord_698914) baseStart_698914 baseEnd_698914 := by
    simpa [prefixWord, tailWord_698914, baseEnd_698914] using wordTrace_append hprefix tailTrace_698914
  have hstable : (prefixWord ++ tailWord_698914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698914).length < 2 ^ (prefixWord ++ tailWord_698914).sum := by decide
  have hdescent : baseEnd_698914 < baseStart_698914 := by decide
  rcases family_descends (prefixWord ++ tailWord_698914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698928 : List Nat := [2, 1, 1, 1, 2, 3, 2, 9]
def baseStart_698928 : Nat := 118140960795 + 698928 * 2 ^ 59
def prefixEnd_698928 : Nat := 4983230072969 + 3 ^ 40 * 698928 * 2
def baseEnd_698928 : Nat := 53168297316406914768251

theorem tailTrace_698928 : CollatzResearch.WordTrace tailWord_698928 prefixEnd_698928 53168297316406914768251 := by
  unfold tailWord_698928
  simp only [CollatzResearch.WordTrace]
  refine ⟨12745999205955349122092719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16994665607940465496123625 12745999205955349122092719)
  ·
    refine ⟨19118998808933023683139079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12745999205955349122092719 19118998808933023683139079)
    ·
      refine ⟨28678498213399535524708619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19118998808933023683139079 28678498213399535524708619)
      ·
        refine ⟨43017747320099303287062929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28678498213399535524708619 43017747320099303287062929)
        ·
          refine ⟨32263310490074477465297197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43017747320099303287062929 32263310490074477465297197)
          ·
            refine ⟨12098741433777929049486449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32263310490074477465297197 12098741433777929049486449)
            ·
              refine ⟨9074056075333446787114837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12098741433777929049486449 9074056075333446787114837)
              ·
                refine ⟨53168297316406914768251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9074056075333446787114837 53168297316406914768251)
                ·
                  rfl

theorem cell21_698928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_698928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698928 prefixEnd_698928 := by exact prefixLift 698928
  have htrace : WordTrace (prefixWord ++ tailWord_698928) baseStart_698928 baseEnd_698928 := by
    simpa [prefixWord, tailWord_698928, baseEnd_698928] using wordTrace_append hprefix tailTrace_698928
  have hstable : (prefixWord ++ tailWord_698928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698928).length < 2 ^ (prefixWord ++ tailWord_698928).sum := by decide
  have hdescent : baseEnd_698928 < baseStart_698928 := by decide
  rcases family_descends (prefixWord ++ tailWord_698928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698934 : List Nat := [5, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_698934 : Nat := 118140960795 + 698934 * 2 ^ 59
def prefixEnd_698934 : Nat := 4983230072969 + 3 ^ 40 * 698934 * 2
def baseEnd_698934 : Nat := 159506261230966067204741

theorem tailTrace_698934 : CollatzResearch.WordTrace tailWord_698934 prefixEnd_698934 159506261230966067204741 := by
  unfold tailWord_698934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1593263578118060079306491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16994811499925974179269237 1593263578118060079306491)
  ·
    refine ⟨2389895367177090118959737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1593263578118060079306491 2389895367177090118959737)
    ·
      refine ⟨1792421525382817589219803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2389895367177090118959737 1792421525382817589219803)
      ·
        refine ⟨2688632288074226383829705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792421525382817589219803 2688632288074226383829705)
        ·
          refine ⟨2016474216055669787872279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2688632288074226383829705 2016474216055669787872279)
          ·
            refine ⟨3024711324083504681808419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016474216055669787872279 3024711324083504681808419)
            ·
              refine ⟨4537066986125257022712629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024711324083504681808419 4537066986125257022712629)
              ·
                refine ⟨425350029949242845879309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4537066986125257022712629 425350029949242845879309)
                ·
                  refine ⟨159506261230966067204741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425350029949242845879309 159506261230966067204741)
                  ·
                    rfl

theorem cell21_698934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_698934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698934 prefixEnd_698934 := by exact prefixLift 698934
  have htrace : WordTrace (prefixWord ++ tailWord_698934) baseStart_698934 baseEnd_698934 := by
    simpa [prefixWord, tailWord_698934, baseEnd_698934] using wordTrace_append hprefix tailTrace_698934
  have hstable : (prefixWord ++ tailWord_698934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698934).length < 2 ^ (prefixWord ++ tailWord_698934).sum := by decide
  have hdescent : baseEnd_698934 < baseStart_698934 := by decide
  rcases family_descends (prefixWord ++ tailWord_698934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698945 : List Nat := [1, 2, 5, 1, 1, 3, 8]
def baseStart_698945 : Nat := 118140960795 + 698945 * 2 ^ 59
def prefixEnd_698945 : Nat := 4983230072969 + 3 ^ 40 * 698945 * 2
def baseEnd_698945 : Nat := 17723196842314721391265

theorem tailTrace_698945 : CollatzResearch.WordTrace tailWord_698945 prefixEnd_698945 17723196842314721391265 := by
  unfold tailWord_698945
  simp only [CollatzResearch.WordTrace]
  refine ⟨25492618452849110147554289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16995078968566073431702859 25492618452849110147554289)
  ·
    refine ⟨19119463839636832610665717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25492618452849110147554289 19119463839636832610665717)
    ·
      refine ⟨1792449734965953057249911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19119463839636832610665717 1792449734965953057249911)
      ·
        refine ⟨2688674602448929585874867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792449734965953057249911 2688674602448929585874867)
        ·
          refine ⟨4033011903673394378812301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688674602448929585874867 4033011903673394378812301)
          ·
            refine ⟨1512379463877522892054613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4033011903673394378812301 1512379463877522892054613)
            ·
              refine ⟨17723196842314721391265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1512379463877522892054613 17723196842314721391265)
              ·
                rfl

theorem cell21_698945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 8].length) (baseStart_698945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698945 prefixEnd_698945 := by exact prefixLift 698945
  have htrace : WordTrace (prefixWord ++ tailWord_698945) baseStart_698945 baseEnd_698945 := by
    simpa [prefixWord, tailWord_698945, baseEnd_698945] using wordTrace_append hprefix tailTrace_698945
  have hstable : (prefixWord ++ tailWord_698945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698945).length < 2 ^ (prefixWord ++ tailWord_698945).sum := by decide
  have hdescent : baseEnd_698945 < baseStart_698945 := by decide
  rcases family_descends (prefixWord ++ tailWord_698945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698959 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 5]
def baseStart_698959 : Nat := 118140960795 + 698959 * 2 ^ 59
def prefixEnd_698959 : Nat := 4983230072969 + 3 ^ 40 * 698959 * 2
def baseEnd_698959 : Nat := 159511966571571579288023

theorem tailTrace_698959 : CollatzResearch.WordTrace tailWord_698959 prefixEnd_698959 159511966571571579288023 := by
  unfold tailWord_698959
  simp only [CollatzResearch.WordTrace]
  refine ⟨25493129074798390538563931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16995419383198927025709287 25493129074798390538563931)
  ·
    refine ⟨38239693612197585807845897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25493129074798390538563931 38239693612197585807845897)
    ·
      refine ⟨28679770209148189355884423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38239693612197585807845897 28679770209148189355884423)
      ·
        refine ⟨43019655313722284033826635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28679770209148189355884423 43019655313722284033826635)
        ·
          refine ⟨64529482970583426050739953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43019655313722284033826635 64529482970583426050739953)
          ·
            refine ⟨48397112227937569538054965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64529482970583426050739953 48397112227937569538054965)
            ·
              refine ⟨4537229271369147144192653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48397112227937569538054965 4537229271369147144192653)
              ·
                refine ⟨1701460976763430179072245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4537229271369147144192653 1701460976763430179072245)
                ·
                  refine ⟨159511966571571579288023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1701460976763430179072245 159511966571571579288023)
                  ·
                    rfl

theorem cell21_698959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_698959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_698959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_698959 prefixEnd_698959 := by exact prefixLift 698959
  have htrace : WordTrace (prefixWord ++ tailWord_698959) baseStart_698959 baseEnd_698959 := by
    simpa [prefixWord, tailWord_698959, baseEnd_698959] using wordTrace_append hprefix tailTrace_698959
  have hstable : (prefixWord ++ tailWord_698959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698959).length < 2 ^ (prefixWord ++ tailWord_698959).sum := by decide
  have hdescent : baseEnd_698959 < baseStart_698959 := by decide
  rcases family_descends (prefixWord ++ tailWord_698959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699004 : List Nat := [2, 2, 2, 1, 1, 2, 11]
def baseStart_699004 : Nat := 118140960795 + 699004 * 2 ^ 59
def prefixEnd_699004 : Nat := 4983230072969 + 3 ^ 40 * 699004 * 2
def baseEnd_699004 : Nat := 17724692909406833448659

theorem tailTrace_699004 : CollatzResearch.WordTrace tailWord_699004 prefixEnd_699004 17724692909406833448659 := by
  unfold tailWord_699004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12747385179817681611976033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16996513573090242149301377 12747385179817681611976033)
  ·
    refine ⟨9560538884863261208982025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12747385179817681611976033 9560538884863261208982025)
    ·
      refine ⟨7170404163647445906736519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9560538884863261208982025 7170404163647445906736519)
      ·
        refine ⟨10755606245471168860104779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7170404163647445906736519 10755606245471168860104779)
        ·
          refine ⟨16133409368206753290157169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10755606245471168860104779 16133409368206753290157169)
          ·
            refine ⟨12100057026155064967617877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16133409368206753290157169 12100057026155064967617877)
            ·
              refine ⟨17724692909406833448659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12100057026155064967617877 17724692909406833448659)
              ·
                rfl

theorem cell21_699004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 11].length) (baseStart_699004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699004 prefixEnd_699004 := by exact prefixLift 699004
  have htrace : WordTrace (prefixWord ++ tailWord_699004) baseStart_699004 baseEnd_699004 := by
    simpa [prefixWord, tailWord_699004, baseEnd_699004] using wordTrace_append hprefix tailTrace_699004
  have hstable : (prefixWord ++ tailWord_699004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699004).length < 2 ^ (prefixWord ++ tailWord_699004).sum := by decide
  have hdescent : baseEnd_699004 < baseStart_699004 := by decide
  rcases family_descends (prefixWord ++ tailWord_699004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699069 : List Nat := [1, 4, 1, 2, 1, 4, 1, 4, 3]
def baseStart_699069 : Nat := 118140960795 + 699069 * 2 ^ 59
def prefixEnd_699069 : Nat := 4983230072969 + 3 ^ 40 * 699069 * 2
def baseEnd_699069 : Nat := 159537070070235832454465

theorem tailTrace_699069 : CollatzResearch.WordTrace tailWord_699069 prefixEnd_699069 159537070070235832454465 := by
  unfold tailWord_699069
  simp only [CollatzResearch.WordTrace]
  refine ⟨25497141104399879325068261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16998094069599919550045507 25497141104399879325068261)
  ·
    refine ⟨4780713957074977373450299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25497141104399879325068261 4780713957074977373450299)
    ·
      refine ⟨7171070935612466060175449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4780713957074977373450299 7171070935612466060175449)
      ·
        refine ⟨5378303201709349545131587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7171070935612466060175449 5378303201709349545131587)
        ·
          refine ⟨8067454802564024317697381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5378303201709349545131587 8067454802564024317697381)
          ·
            refine ⟨1512647775480754559568259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8067454802564024317697381 1512647775480754559568259)
            ·
              refine ⟨2268971663221131839352389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512647775480754559568259 2268971663221131839352389)
              ·
                refine ⟨425432186853962219878573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2268971663221131839352389 425432186853962219878573)
                ·
                  refine ⟨159537070070235832454465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425432186853962219878573 159537070070235832454465)
                  ·
                    rfl

theorem cell21_699069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_699069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699069 prefixEnd_699069 := by exact prefixLift 699069
  have htrace : WordTrace (prefixWord ++ tailWord_699069) baseStart_699069 baseEnd_699069 := by
    simpa [prefixWord, tailWord_699069, baseEnd_699069] using wordTrace_append hprefix tailTrace_699069
  have hstable : (prefixWord ++ tailWord_699069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699069).length < 2 ^ (prefixWord ++ tailWord_699069).sum := by decide
  have hdescent : baseEnd_699069 < baseStart_699069 := by decide
  rcases family_descends (prefixWord ++ tailWord_699069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699097 : List Nat := [1, 2, 1, 2, 3, 2, 5, 5]
def baseStart_699097 : Nat := 118140960795 + 699097 * 2 ^ 59
def prefixEnd_699097 : Nat := 4983230072969 + 3 ^ 40 * 699097 * 2
def baseEnd_699097 : Nat := 53181153350571335329247

theorem tailTrace_699097 : CollatzResearch.WordTrace tailWord_699097 prefixEnd_699097 53181153350571335329247 := by
  unfold tailWord_699097
  simp only [CollatzResearch.WordTrace]
  refine ⟨25498162348298440107087545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16998774898865626738058363 25498162348298440107087545)
  ·
    refine ⟨19123621761223830080315659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25498162348298440107087545 19123621761223830080315659)
    ·
      refine ⟨28685432641835745120473489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19123621761223830080315659 28685432641835745120473489)
      ·
        refine ⟨21514074481376808840355117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28685432641835745120473489 21514074481376808840355117)
        ·
          refine ⟨8067777930516303315133169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21514074481376808840355117 8067777930516303315133169)
          ·
            refine ⟨6050833447887227486349877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8067777930516303315133169 6050833447887227486349877)
            ·
              refine ⟨567265635739427576845301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6050833447887227486349877 567265635739427576845301)
              ·
                refine ⟨53181153350571335329247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 567265635739427576845301 53181153350571335329247)
                ·
                  rfl

theorem cell21_699097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 5].length) (baseStart_699097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699097 prefixEnd_699097 := by exact prefixLift 699097
  have htrace : WordTrace (prefixWord ++ tailWord_699097) baseStart_699097 baseEnd_699097 := by
    simpa [prefixWord, tailWord_699097, baseEnd_699097] using wordTrace_append hprefix tailTrace_699097
  have hstable : (prefixWord ++ tailWord_699097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699097).length < 2 ^ (prefixWord ++ tailWord_699097).sum := by decide
  have hdescent : baseEnd_699097 < baseStart_699097 := by decide
  rcases family_descends (prefixWord ++ tailWord_699097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699128 : List Nat := [2, 1, 2, 1, 1, 2, 3, 6, 3]
def baseStart_699128 : Nat := 118140960795 + 699128 * 2 ^ 59
def prefixEnd_699128 : Nat := 4983230072969 + 3 ^ 40 * 699128 * 2
def baseEnd_699128 : Nat := 159550534674064840971011

theorem tailTrace_699128 : CollatzResearch.WordTrace tailWord_699128 prefixEnd_699128 159550534674064840971011 := by
  unfold tailWord_699128
  simp only [CollatzResearch.WordTrace]
  refine ⟨12749646505593066200733019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16999528674124088267644025 12749646505593066200733019)
  ·
    refine ⟨19124469758389599301099529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12749646505593066200733019 19124469758389599301099529)
    ·
      refine ⟨14343352318792199475824647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19124469758389599301099529 14343352318792199475824647)
      ·
        refine ⟨21515028478188299213736971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14343352318792199475824647 21515028478188299213736971)
        ·
          refine ⟨32272542717282448820605457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21515028478188299213736971 32272542717282448820605457)
          ·
            refine ⟨24204407037961836615454093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32272542717282448820605457 24204407037961836615454093)
            ·
              refine ⟨9076652639235688730795285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24204407037961836615454093 9076652639235688730795285)
              ·
                refine ⟨425468092464172909256029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9076652639235688730795285 425468092464172909256029)
                ·
                  refine ⟨159550534674064840971011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425468092464172909256029 159550534674064840971011)
                  ·
                    rfl

theorem cell21_699128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 3].length) (baseStart_699128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699128 prefixEnd_699128 := by exact prefixLift 699128
  have htrace : WordTrace (prefixWord ++ tailWord_699128) baseStart_699128 baseEnd_699128 := by
    simpa [prefixWord, tailWord_699128, baseEnd_699128] using wordTrace_append hprefix tailTrace_699128
  have hstable : (prefixWord ++ tailWord_699128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699128).length < 2 ^ (prefixWord ++ tailWord_699128).sum := by decide
  have hdescent : baseEnd_699128 < baseStart_699128 := by decide
  rcases family_descends (prefixWord ++ tailWord_699128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699235 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 4]
def baseStart_699235 : Nat := 118140960795 + 699235 * 2 ^ 59
def prefixEnd_699235 : Nat := 4983230072969 + 3 ^ 40 * 699235 * 2
def baseEnd_699235 : Nat := 159574953531856432687459

theorem tailTrace_699235 : CollatzResearch.WordTrace tailWord_699235 prefixEnd_699235 159574953531856432687459 := by
  unfold tailWord_699235
  simp only [CollatzResearch.WordTrace]
  refine ⟨25503195621798489675611159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17002130414532326450407439 25503195621798489675611159)
  ·
    refine ⟨38254793432697734513416739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25503195621798489675611159 38254793432697734513416739)
    ·
      refine ⟨57382190149046601770125109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38254793432697734513416739 57382190149046601770125109)
      ·
        refine ⟨5379580326473118915949229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57382190149046601770125109 5379580326473118915949229)
        ·
          refine ⟨2017342622427419593480961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5379580326473118915949229 2017342622427419593480961)
          ·
            refine ⟨1513006966820564695110721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2017342622427419593480961 1513006966820564695110721)
            ·
              refine ⟨1134755225115423521333041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1513006966820564695110721 1134755225115423521333041)
              ·
                refine ⟨851066418836567640999781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134755225115423521333041 851066418836567640999781)
                ·
                  refine ⟨159574953531856432687459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 851066418836567640999781 159574953531856432687459)
                  ·
                    rfl

theorem cell21_699235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 4].length) (baseStart_699235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699235 prefixEnd_699235 := by exact prefixLift 699235
  have htrace : WordTrace (prefixWord ++ tailWord_699235) baseStart_699235 baseEnd_699235 := by
    simpa [prefixWord, tailWord_699235, baseEnd_699235] using wordTrace_append hprefix tailTrace_699235
  have hstable : (prefixWord ++ tailWord_699235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699235).length < 2 ^ (prefixWord ++ tailWord_699235).sum := by decide
  have hdescent : baseEnd_699235 < baseStart_699235 := by decide
  rcases family_descends (prefixWord ++ tailWord_699235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699249 : List Nat := [1, 2, 2, 2, 1, 6, 1, 6]
def baseStart_699249 : Nat := 118140960795 + 699249 * 2 ^ 59
def prefixEnd_699249 : Nat := 4983230072969 + 3 ^ 40 * 699249 * 2
def baseEnd_699249 : Nat := 53192716174198506484699

theorem tailTrace_699249 : CollatzResearch.WordTrace tailWord_699249 prefixEnd_699249 53192716174198506484699 := by
  unfold tailWord_699249
  simp only [CollatzResearch.WordTrace]
  refine ⟨25503706243747770066620801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17002470829165180044413867 25503706243747770066620801)
  ·
    refine ⟨19127779682810827549965601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25503706243747770066620801 19127779682810827549965601)
    ·
      refine ⟨14345834762108120662474201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19127779682810827549965601 14345834762108120662474201)
      ·
        refine ⟨10759376071581090496855651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14345834762108120662474201 10759376071581090496855651)
        ·
          refine ⟨16139064107371635745283477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10759376071581090496855651 16139064107371635745283477)
          ·
            refine ⟨756518630033045425560163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16139064107371635745283477 756518630033045425560163)
            ·
              refine ⟨1134777945049568138340245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756518630033045425560163 1134777945049568138340245)
              ·
                refine ⟨53192716174198506484699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1134777945049568138340245 53192716174198506484699)
                ·
                  rfl

theorem cell21_699249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 6].length) (baseStart_699249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699249 prefixEnd_699249 := by exact prefixLift 699249
  have htrace : WordTrace (prefixWord ++ tailWord_699249) baseStart_699249 baseEnd_699249 := by
    simpa [prefixWord, tailWord_699249, baseEnd_699249] using wordTrace_append hprefix tailTrace_699249
  have hstable : (prefixWord ++ tailWord_699249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699249).length < 2 ^ (prefixWord ++ tailWord_699249).sum := by decide
  have hdescent : baseEnd_699249 < baseStart_699249 := by decide
  rcases family_descends (prefixWord ++ tailWord_699249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699286 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_699286 : Nat := 118140960795 + 699286 * 2 ^ 59
def prefixEnd_699286 : Nat := 4983230072969 + 3 ^ 40 * 699286 * 2
def baseEnd_699286 : Nat := 159586592426691677337355

theorem tailTrace_699286 : CollatzResearch.WordTrace tailWord_699286 prefixEnd_699286 159586592426691677337355 := by
  unfold tailWord_699286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594065984038357836607357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17003370496409150257145141 1594065984038357836607357)
  ·
    refine ⟨597774744014384188727759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1594065984038357836607357 597774744014384188727759)
    ·
      refine ⟨896662116021576283091639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597774744014384188727759 896662116021576283091639)
      ·
        refine ⟨1344993174032364424637459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896662116021576283091639 1344993174032364424637459)
        ·
          refine ⟨2017489761048546636956189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344993174032364424637459 2017489761048546636956189)
          ·
            refine ⟨756558660393204988858571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2017489761048546636956189 756558660393204988858571)
            ·
              refine ⟨1134837990589807483287857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756558660393204988858571 1134837990589807483287857)
              ·
                refine ⟨851128492942355612465893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134837990589807483287857 851128492942355612465893)
                ·
                  refine ⟨159586592426691677337355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 851128492942355612465893 159586592426691677337355)
                  ·
                    rfl

theorem cell21_699286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_699286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699286 prefixEnd_699286 := by exact prefixLift 699286
  have htrace : WordTrace (prefixWord ++ tailWord_699286) baseStart_699286 baseEnd_699286 := by
    simpa [prefixWord, tailWord_699286, baseEnd_699286] using wordTrace_append hprefix tailTrace_699286
  have hstable : (prefixWord ++ tailWord_699286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699286).length < 2 ^ (prefixWord ++ tailWord_699286).sum := by decide
  have hdescent : baseEnd_699286 < baseStart_699286 := by decide
  rcases family_descends (prefixWord ++ tailWord_699286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699297 : List Nat := [1, 2, 3, 4, 1, 1, 2, 4, 3]
def baseStart_699297 : Nat := 118140960795 + 699297 * 2 ^ 59
def prefixEnd_699297 : Nat := 4983230072969 + 3 ^ 40 * 699297 * 2
def baseEnd_699297 : Nat := 159589102776558102653999

theorem tailTrace_699297 : CollatzResearch.WordTrace tailWord_699297 prefixEnd_699297 159589102776558102653999 := by
  unfold tailWord_699297
  simp only [CollatzResearch.WordTrace]
  refine ⟨25505456947573874264368145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17003637965049249509578763 25505456947573874264368145)
  ·
    refine ⟨19129092710680405698276109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25505456947573874264368145 19129092710680405698276109)
    ·
      refine ⟨7173409766505152136853541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19129092710680405698276109 7173409766505152136853541)
      ·
        refine ⟨1345014331219716025660039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7173409766505152136853541 1345014331219716025660039)
        ·
          refine ⟨2017521496829574038490059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345014331219716025660039 2017521496829574038490059)
          ·
            refine ⟨3026282245244361057735089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017521496829574038490059 3026282245244361057735089)
            ·
              refine ⟨2269711683933270793301317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026282245244361057735089 2269711683933270793301317)
              ·
                refine ⟨425570940737488273743997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2269711683933270793301317 425570940737488273743997)
                ·
                  refine ⟨159589102776558102653999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425570940737488273743997 159589102776558102653999)
                  ·
                    rfl

theorem cell21_699297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 3].length) (baseStart_699297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699297 prefixEnd_699297 := by exact prefixLift 699297
  have htrace : WordTrace (prefixWord ++ tailWord_699297) baseStart_699297 baseEnd_699297 := by
    simpa [prefixWord, tailWord_699297, baseEnd_699297] using wordTrace_append hprefix tailTrace_699297
  have hstable : (prefixWord ++ tailWord_699297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699297).length < 2 ^ (prefixWord ++ tailWord_699297).sum := by decide
  have hdescent : baseEnd_699297 < baseStart_699297 := by decide
  rcases family_descends (prefixWord ++ tailWord_699297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699325 : List Nat := [1, 4, 1, 2, 4, 1, 1, 7]
def baseStart_699325 : Nat := 118140960795 + 699325 * 2 ^ 59
def prefixEnd_699325 : Nat := 4983230072969 + 3 ^ 40 * 699325 * 2
def baseEnd_699325 : Nat := 53198497586012092062425

theorem tailTrace_699325 : CollatzResearch.WordTrace tailWord_699325 prefixEnd_699325 53198497586012092062425 := by
  unfold tailWord_699325
  simp only [CollatzResearch.WordTrace]
  refine ⟨25506478191472435046387429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17004318794314956697591619 25506478191472435046387429)
  ·
    refine ⟨4782464660901081571197643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25506478191472435046387429 4782464660901081571197643)
    ·
      refine ⟨7173696991351622356796465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4782464660901081571197643 7173696991351622356796465)
      ·
        refine ⟨5380272743513716767597349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7173696991351622356796465 5380272743513716767597349)
        ·
          refine ⟨1008801139408821893924503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5380272743513716767597349 1008801139408821893924503)
          ·
            refine ⟨1513201709113232840886755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008801139408821893924503 1513201709113232840886755)
            ·
              refine ⟨2269802563669849261330133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513201709113232840886755 2269802563669849261330133)
              ·
                refine ⟨53198497586012092062425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2269802563669849261330133 53198497586012092062425)
                ·
                  rfl

theorem cell21_699325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 7].length) (baseStart_699325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699325 prefixEnd_699325 := by exact prefixLift 699325
  have htrace : WordTrace (prefixWord ++ tailWord_699325) baseStart_699325 baseEnd_699325 := by
    simpa [prefixWord, tailWord_699325, baseEnd_699325] using wordTrace_append hprefix tailTrace_699325
  have hstable : (prefixWord ++ tailWord_699325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699325).length < 2 ^ (prefixWord ++ tailWord_699325).sum := by decide
  have hdescent : baseEnd_699325 < baseStart_699325 := by decide
  rcases family_descends (prefixWord ++ tailWord_699325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699449 : List Nat := [1, 2, 1, 5, 2, 2, 2, 3, 3]
def baseStart_699449 : Nat := 118140960795 + 699449 * 2 ^ 59
def prefixEnd_699449 : Nat := 4983230072969 + 3 ^ 40 * 699449 * 2
def baseEnd_699449 : Nat := 159623791247439616120355

theorem tailTrace_699449 : CollatzResearch.WordTrace tailWord_699449 prefixEnd_699449 159623791247439616120355 := by
  unfold tailWord_699449
  simp only [CollatzResearch.WordTrace]
  refine ⟨25511000843023204223901401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17007333895348802815934267 25511000843023204223901401)
  ·
    refine ⟨19133250632267403167926051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25511000843023204223901401 19133250632267403167926051)
    ·
      refine ⟨28699875948401104751889077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19133250632267403167926051 28699875948401104751889077)
      ·
        refine ⟨2690613370162603570489601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28699875948401104751889077 2690613370162603570489601)
        ·
          refine ⟨2017960027621952677867201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2690613370162603570489601 2017960027621952677867201)
          ·
            refine ⟨1513470020716464508400401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2017960027621952677867201 1513470020716464508400401)
            ·
              refine ⟨1135102515537348381300301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1513470020716464508400401 1135102515537348381300301)
              ·
                refine ⟨425663443326505642987613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1135102515537348381300301 425663443326505642987613)
                ·
                  refine ⟨159623791247439616120355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425663443326505642987613 159623791247439616120355)
                  ·
                    rfl

theorem cell21_699449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 3].length) (baseStart_699449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699449 prefixEnd_699449 := by exact prefixLift 699449
  have htrace : WordTrace (prefixWord ++ tailWord_699449) baseStart_699449 baseEnd_699449 := by
    simpa [prefixWord, tailWord_699449, baseEnd_699449] using wordTrace_append hprefix tailTrace_699449
  have hstable : (prefixWord ++ tailWord_699449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699449).length < 2 ^ (prefixWord ++ tailWord_699449).sum := by decide
  have hdescent : baseEnd_699449 < baseStart_699449 := by decide
  rcases family_descends (prefixWord ++ tailWord_699449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699463 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 4]
def baseStart_699463 : Nat := 118140960795 + 699463 * 2 ^ 59
def prefixEnd_699463 : Nat := 4983230072969 + 3 ^ 40 * 699463 * 2
def baseEnd_699463 : Nat := 159626986238178702886993

theorem tailTrace_699463 : CollatzResearch.WordTrace tailWord_699463 prefixEnd_699463 159626986238178702886993 := by
  unfold tailWord_699463
  simp only [CollatzResearch.WordTrace]
  refine ⟨25511511464972484614911043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17007674309981656409940695 25511511464972484614911043)
  ·
    refine ⟨38267267197458726922366565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25511511464972484614911043 38267267197458726922366565)
    ·
      refine ⟨7175112599523511297943731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38267267197458726922366565 7175112599523511297943731)
      ·
        refine ⟨10762668899285266946915597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7175112599523511297943731 10762668899285266946915597)
        ·
          refine ⟨4036000837231975105093349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10762668899285266946915597 4036000837231975105093349)
          ·
            refine ⟨756750156980995332205003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4036000837231975105093349 756750156980995332205003)
            ·
              refine ⟨1135125235471492998307505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756750156980995332205003 1135125235471492998307505)
              ·
                refine ⟨851343926603619748730629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1135125235471492998307505 851343926603619748730629)
                ·
                  refine ⟨159626986238178702886993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 851343926603619748730629 159626986238178702886993)
                  ·
                    rfl

theorem cell21_699463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 4].length) (baseStart_699463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699463 prefixEnd_699463 := by exact prefixLift 699463
  have htrace : WordTrace (prefixWord ++ tailWord_699463) baseStart_699463 baseEnd_699463 := by
    simpa [prefixWord, tailWord_699463, baseEnd_699463] using wordTrace_append hprefix tailTrace_699463
  have hstable : (prefixWord ++ tailWord_699463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699463).length < 2 ^ (prefixWord ++ tailWord_699463).sum := by decide
  have hdescent : baseEnd_699463 < baseStart_699463 := by decide
  rcases family_descends (prefixWord ++ tailWord_699463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699525 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 5]
def baseStart_699525 : Nat := 118140960795 + 699525 * 2 ^ 59
def prefixEnd_699525 : Nat := 4983230072969 + 3 ^ 40 * 699525 * 2
def baseEnd_699525 : Nat := 159641135482880372853533

theorem tailTrace_699525 : CollatzResearch.WordTrace tailWord_699525 prefixEnd_699525 159641135482880372853533 := by
  unfold tailWord_699525
  simp only [CollatzResearch.WordTrace]
  refine ⟨25513772790747869203668029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17009181860498579469112019 25513772790747869203668029)
  ·
    refine ⟨9567664796530450951375511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25513772790747869203668029 9567664796530450951375511)
    ·
      refine ⟨14351497194795676427063267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9567664796530450951375511 14351497194795676427063267)
      ·
        refine ⟨21527245792193514640594901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14351497194795676427063267 21527245792193514640594901)
        ·
          refine ⟨504544823254535499388943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 21527245792193514640594901 504544823254535499388943)
          ·
            refine ⟨756817234881803249083415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504544823254535499388943 756817234881803249083415)
            ·
              refine ⟨1135225852322704873625123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756817234881803249083415 1135225852322704873625123)
              ·
                refine ⟨1702838778484057310437685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135225852322704873625123 1702838778484057310437685)
                ·
                  refine ⟨159641135482880372853533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1702838778484057310437685 159641135482880372853533)
                  ·
                    rfl

theorem cell21_699525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_699525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699525 prefixEnd_699525 := by exact prefixLift 699525
  have htrace : WordTrace (prefixWord ++ tailWord_699525) baseStart_699525 baseEnd_699525 := by
    simpa [prefixWord, tailWord_699525, baseEnd_699525] using wordTrace_append hprefix tailTrace_699525
  have hstable : (prefixWord ++ tailWord_699525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699525).length < 2 ^ (prefixWord ++ tailWord_699525).sum := by decide
  have hdescent : baseEnd_699525 < baseStart_699525 := by decide
  rcases family_descends (prefixWord ++ tailWord_699525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699581 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 6]
def baseStart_699581 : Nat := 118140960795 + 699581 * 2 ^ 59
def prefixEnd_699581 : Nat := 4983230072969 + 3 ^ 40 * 699581 * 2
def baseEnd_699581 : Nat := 159653915445836719920085

theorem tailTrace_699581 : CollatzResearch.WordTrace tailWord_699581 prefixEnd_699581 159653915445836719920085 := by
  unfold tailWord_699581
  simp only [CollatzResearch.WordTrace]
  refine ⟨25515815278544990767706597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17010543519029993845137731 25515815278544990767706597)
  ·
    refine ⟨4784215364727185768944987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25515815278544990767706597 4784215364727185768944987)
    ·
      refine ⟨7176323047090778653417481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4784215364727185768944987 7176323047090778653417481)
      ·
        refine ⟨5382242285318083990063111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7176323047090778653417481 5382242285318083990063111)
        ·
          refine ⟨8073363427977125985094667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5382242285318083990063111 8073363427977125985094667)
          ·
            refine ⟨12110045141965688977642001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8073363427977125985094667 12110045141965688977642001)
            ·
              refine ⟨9082533856474266733231501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12110045141965688977642001 9082533856474266733231501)
              ·
                refine ⟨3405950196177850024961813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9082533856474266733231501 3405950196177850024961813)
                ·
                  refine ⟨159653915445836719920085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3405950196177850024961813 159653915445836719920085)
                  ·
                    rfl

theorem cell21_699581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_699581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699581 prefixEnd_699581 := by exact prefixLift 699581
  have htrace : WordTrace (prefixWord ++ tailWord_699581) baseStart_699581 baseEnd_699581 := by
    simpa [prefixWord, tailWord_699581, baseEnd_699581] using wordTrace_append hprefix tailTrace_699581
  have hstable : (prefixWord ++ tailWord_699581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699581).length < 2 ^ (prefixWord ++ tailWord_699581).sum := by decide
  have hdescent : baseEnd_699581 < baseStart_699581 := by decide
  rcases family_descends (prefixWord ++ tailWord_699581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699595 : List Nat := [1, 1, 1, 1, 3, 2, 2, 10]
def baseStart_699595 : Nat := 118140960795 + 699595 * 2 ^ 59
def prefixEnd_699595 : Nat := 4983230072969 + 3 ^ 40 * 699595 * 2
def baseEnd_699595 : Nat := 53219036812191935562241

theorem tailTrace_699595 : CollatzResearch.WordTrace tailWord_699595 prefixEnd_699595 53219036812191935562241 := by
  unfold tailWord_699595
  simp only [CollatzResearch.WordTrace]
  refine ⟨25516325900494271158716239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17010883933662847439144159 25516325900494271158716239)
  ·
    refine ⟨38274488850741406738074359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25516325900494271158716239 38274488850741406738074359)
    ·
      refine ⟨57411733276112110107111539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38274488850741406738074359 57411733276112110107111539)
      ·
        refine ⟨86117599914168165160667309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57411733276112110107111539 86117599914168165160667309)
        ·
          refine ⟨32294099967813061935250241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86117599914168165160667309 32294099967813061935250241)
          ·
            refine ⟨24220574975859796451437681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32294099967813061935250241 24220574975859796451437681)
            ·
              refine ⟨18165431231894847338578261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24220574975859796451437681 18165431231894847338578261)
              ·
                refine ⟨53219036812191935562241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18165431231894847338578261 53219036812191935562241)
                ·
                  rfl

theorem cell21_699595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 10].length) (baseStart_699595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699595 prefixEnd_699595 := by exact prefixLift 699595
  have htrace : WordTrace (prefixWord ++ tailWord_699595) baseStart_699595 baseEnd_699595 := by
    simpa [prefixWord, tailWord_699595, baseEnd_699595] using wordTrace_append hprefix tailTrace_699595
  have hstable : (prefixWord ++ tailWord_699595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699595).length < 2 ^ (prefixWord ++ tailWord_699595).sum := by decide
  have hdescent : baseEnd_699595 < baseStart_699595 := by decide
  rcases family_descends (prefixWord ++ tailWord_699595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699677 : List Nat := [1, 4, 2, 3, 1, 1, 3, 3, 3]
def baseStart_699677 : Nat := 118140960795 + 699677 * 2 ^ 59
def prefixEnd_699677 : Nat := 4983230072969 + 3 ^ 40 * 699677 * 2
def baseEnd_699677 : Nat := 159675823953761886319889

theorem tailTrace_699677 : CollatzResearch.WordTrace tailWord_699677 prefixEnd_699677 159675823953761886319889 := by
  unfold tailWord_699677
  simp only [CollatzResearch.WordTrace]
  refine ⟨25519316686197199163201285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17012877790798132775467523 25519316686197199163201285)
  ·
    refine ⟨4784871878661974843100241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25519316686197199163201285 4784871878661974843100241)
    ·
      refine ⟨3588653908996481132325181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4784871878661974843100241 3588653908996481132325181)
      ·
        refine ⟨1345745215873680424621943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3588653908996481132325181 1345745215873680424621943)
        ·
          refine ⟨2018617823810520636932915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345745215873680424621943 2018617823810520636932915)
          ·
            refine ⟨3027926735715780955399373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018617823810520636932915 3027926735715780955399373)
            ·
              refine ⟨1135472525893417858274765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3027926735715780955399373 1135472525893417858274765)
              ·
                refine ⟨425802197210031696853037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1135472525893417858274765 425802197210031696853037)
                ·
                  refine ⟨159675823953761886319889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425802197210031696853037 159675823953761886319889)
                  ·
                    rfl

theorem cell21_699677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_699677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699677 prefixEnd_699677 := by exact prefixLift 699677
  have htrace : WordTrace (prefixWord ++ tailWord_699677) baseStart_699677 baseEnd_699677 := by
    simpa [prefixWord, tailWord_699677, baseEnd_699677] using wordTrace_append hprefix tailTrace_699677
  have hstable : (prefixWord ++ tailWord_699677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699677).length < 2 ^ (prefixWord ++ tailWord_699677).sum := by decide
  have hdescent : baseEnd_699677 < baseStart_699677 := by decide
  rcases family_descends (prefixWord ++ tailWord_699677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699688 : List Nat := [2, 1, 5, 1, 2, 1, 9]
def baseStart_699688 : Nat := 118140960795 + 699688 * 2 ^ 59
def prefixEnd_699688 : Nat := 4983230072969 + 3 ^ 40 * 699688 * 2
def baseEnd_699688 : Nat := 17742037144847590181837

theorem tailTrace_699688 : CollatzResearch.WordTrace tailWord_699688 prefixEnd_699688 17742037144847590181837 := by
  unfold tailWord_699688
  simp only [CollatzResearch.WordTrace]
  refine ⟨12759858944578674020925859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17013145259438232027901145 12759858944578674020925859)
  ·
    refine ⟨19139788416868011031388789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12759858944578674020925859 19139788416868011031388789)
    ·
      refine ⟨1794355164081376034192699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19139788416868011031388789 1794355164081376034192699)
      ·
        refine ⟨2691532746122064051289049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1794355164081376034192699 2691532746122064051289049)
        ·
          refine ⟨2018649559591548038466787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2691532746122064051289049 2018649559591548038466787)
          ·
            refine ⟨3027974339387322057700181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018649559591548038466787 3027974339387322057700181)
            ·
              refine ⟨17742037144847590181837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3027974339387322057700181 17742037144847590181837)
              ·
                rfl

theorem cell21_699688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 9].length) (baseStart_699688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699688 prefixEnd_699688 := by exact prefixLift 699688
  have htrace : WordTrace (prefixWord ++ tailWord_699688) baseStart_699688 baseEnd_699688 := by
    simpa [prefixWord, tailWord_699688, baseEnd_699688] using wordTrace_append hprefix tailTrace_699688
  have hstable : (prefixWord ++ tailWord_699688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699688).length < 2 ^ (prefixWord ++ tailWord_699688).sum := by decide
  have hdescent : baseEnd_699688 < baseStart_699688 := by decide
  rcases family_descends (prefixWord ++ tailWord_699688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699705 : List Nat := [1, 2, 1, 6, 2, 1, 2, 6]
def baseStart_699705 : Nat := 118140960795 + 699705 * 2 ^ 59
def prefixEnd_699705 : Nat := 4983230072969 + 3 ^ 40 * 699705 * 2
def baseEnd_699705 : Nat := 53227404645080019951055

theorem tailTrace_699705 : CollatzResearch.WordTrace tailWord_699705 prefixEnd_699705 53227404645080019951055 := by
  unfold tailWord_699705
  simp only [CollatzResearch.WordTrace]
  refine ⟨25520337930095759945220569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17013558620063839963480379 25520337930095759945220569)
  ·
    refine ⟨19140253447571819958915427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25520337930095759945220569 19140253447571819958915427)
    ·
      refine ⟨28710380171357729938373141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19140253447571819958915427 28710380171357729938373141)
      ·
        refine ⟨1345799070532393590861241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28710380171357729938373141 1345799070532393590861241)
        ·
          refine ⟨1009349302899295193145931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1345799070532393590861241 1009349302899295193145931)
          ·
            refine ⟨1514023954348942789718897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009349302899295193145931 1514023954348942789718897)
            ·
              refine ⟨1135517965761707092289173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514023954348942789718897 1135517965761707092289173)
              ·
                refine ⟨53227404645080019951055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1135517965761707092289173 53227404645080019951055)
                ·
                  rfl

theorem cell21_699705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 6].length) (baseStart_699705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699705 prefixEnd_699705 := by exact prefixLift 699705
  have htrace : WordTrace (prefixWord ++ tailWord_699705) baseStart_699705 baseEnd_699705 := by
    simpa [prefixWord, tailWord_699705, baseEnd_699705] using wordTrace_append hprefix tailTrace_699705
  have hstable : (prefixWord ++ tailWord_699705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699705).length < 2 ^ (prefixWord ++ tailWord_699705).sum := by decide
  have hdescent : baseEnd_699705 < baseStart_699705 := by decide
  rcases family_descends (prefixWord ++ tailWord_699705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699747 : List Nat := [1, 1, 1, 5, 2, 11]
def baseStart_699747 : Nat := 118140960795 + 699747 * 2 ^ 59
def prefixEnd_699747 : Nat := 4983230072969 + 3 ^ 40 * 699747 * 2
def baseEnd_699747 : Nat := 5914511070646567413077

theorem tailTrace_699747 : CollatzResearch.WordTrace tailWord_699747 prefixEnd_699747 5914511070646567413077 := by
  unfold tailWord_699747
  simp only [CollatzResearch.WordTrace]
  refine ⟨25521869795943601118249495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17014579863962400745499663 25521869795943601118249495)
  ·
    refine ⟨38282804693915401677374243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25521869795943601118249495 38282804693915401677374243)
    ·
      refine ⟨57424207040873102516061365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38282804693915401677374243 57424207040873102516061365)
      ·
        refine ⟨5383519410081853360880753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57424207040873102516061365 5383519410081853360880753)
        ·
          refine ⟨4037639557561390020660565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5383519410081853360880753 4037639557561390020660565)
          ·
            refine ⟨5914511070646567413077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4037639557561390020660565 5914511070646567413077)
            ·
              rfl

theorem cell21_699747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 11].length) (baseStart_699747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699747 prefixEnd_699747 := by exact prefixLift 699747
  have htrace : WordTrace (prefixWord ++ tailWord_699747) baseStart_699747 baseEnd_699747 := by
    simpa [prefixWord, tailWord_699747, baseEnd_699747] using wordTrace_append hprefix tailTrace_699747
  have hstable : (prefixWord ++ tailWord_699747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699747).length < 2 ^ (prefixWord ++ tailWord_699747).sum := by decide
  have hdescent : baseEnd_699747 < baseStart_699747 := by decide
  rcases family_descends (prefixWord ++ tailWord_699747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699840 : List Nat := [2, 1, 1, 2, 3, 1, 6, 5]
def baseStart_699840 : Nat := 118140960795 + 699840 * 2 ^ 59
def prefixEnd_699840 : Nat := 4983230072969 + 3 ^ 40 * 699840 * 2
def baseEnd_699840 : Nat := 53237674258169941700963

theorem tailTrace_699840 : CollatzResearch.WordTrace tailWord_699840 prefixEnd_699840 53237674258169941700963 := by
  unfold tailWord_699840
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762630892303339000692487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17016841189737785334256649 12762630892303339000692487)
  ·
    refine ⟨19143946338455008501038731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12762630892303339000692487 19143946338455008501038731)
    ·
      refine ⟨28715919507682512751558097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19143946338455008501038731 28715919507682512751558097)
      ·
        refine ⟨21536939630761884563668573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28715919507682512751558097 21536939630761884563668573)
        ·
          refine ⟨8076352361535706711375715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21536939630761884563668573 8076352361535706711375715)
          ·
            refine ⟨12114528542303560067063573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076352361535706711375715 12114528542303560067063573)
            ·
              refine ⟨567868525420479378143605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12114528542303560067063573 567868525420479378143605)
              ·
                refine ⟨53237674258169941700963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 567868525420479378143605 53237674258169941700963)
                ·
                  rfl

theorem cell21_699840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_699840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699840 prefixEnd_699840 := by exact prefixLift 699840
  have htrace : WordTrace (prefixWord ++ tailWord_699840) baseStart_699840 baseEnd_699840 := by
    simpa [prefixWord, tailWord_699840, baseEnd_699840] using wordTrace_append hprefix tailTrace_699840
  have hstable : (prefixWord ++ tailWord_699840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699840).length < 2 ^ (prefixWord ++ tailWord_699840).sum := by decide
  have hdescent : baseEnd_699840 < baseStart_699840 := by decide
  rcases family_descends (prefixWord ++ tailWord_699840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699854 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_699854 : Nat := 118140960795 + 699854 * 2 ^ 59
def prefixEnd_699854 : Nat := 4983230072969 + 3 ^ 40 * 699854 * 2
def baseEnd_699854 : Nat := 159716217765248911869527

theorem tailTrace_699854 : CollatzResearch.WordTrace tailWord_699854 prefixEnd_699854 159716217765248911869527 := by
  unfold tailWord_699854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190721550819494799049327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17017181604370638928263077 3190721550819494799049327)
  ·
    refine ⟨4786082326229242198573991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3190721550819494799049327 4786082326229242198573991)
    ·
      refine ⟨7179123489343863297860987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4786082326229242198573991 7179123489343863297860987)
      ·
        refine ⟨10768685234015794946791481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7179123489343863297860987 10768685234015794946791481)
        ·
          refine ⟨8076513925511846210093611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10768685234015794946791481 8076513925511846210093611)
          ·
            refine ⟨12114770888267769315140417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076513925511846210093611 12114770888267769315140417)
            ·
              refine ⟨9086078166200826986355313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12114770888267769315140417 9086078166200826986355313)
              ·
                refine ⟨6814558624650620239766485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9086078166200826986355313 6814558624650620239766485)
                ·
                  refine ⟨159716217765248911869527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6814558624650620239766485 159716217765248911869527)
                  ·
                    rfl

theorem cell21_699854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_699854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699854 prefixEnd_699854 := by exact prefixLift 699854
  have htrace : WordTrace (prefixWord ++ tailWord_699854) baseStart_699854 baseEnd_699854 := by
    simpa [prefixWord, tailWord_699854, baseEnd_699854] using wordTrace_append hprefix tailTrace_699854
  have hstable : (prefixWord ++ tailWord_699854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699854).length < 2 ^ (prefixWord ++ tailWord_699854).sum := by decide
  have hdescent : baseEnd_699854 < baseStart_699854 := by decide
  rcases family_descends (prefixWord ++ tailWord_699854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699916 : List Nat := [2, 2, 1, 2, 6, 8]
def baseStart_699916 : Nat := 118140960795 + 699916 * 2 ^ 59
def prefixEnd_699916 : Nat := 4983230072969 + 3 ^ 40 * 699916 * 2
def baseEnd_699916 : Nat := 5915939518887058586521

theorem tailTrace_699916 : CollatzResearch.WordTrace tailWord_699916 prefixEnd_699916 5915939518887058586521 := by
  unfold tailWord_699916
  simp only [CollatzResearch.WordTrace]
  refine ⟨12764016866165671490575801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17018689154887561987434401 12764016866165671490575801)
  ·
    refine ⟨9573012649624253617931851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12764016866165671490575801 9573012649624253617931851)
    ·
      refine ⟨14359518974436380426897777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9573012649624253617931851 14359518974436380426897777)
      ·
        refine ⟨10769639230827285320173333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14359518974436380426897777 10769639230827285320173333)
        ·
          refine ⟨504826838945028999383125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10769639230827285320173333 504826838945028999383125)
          ·
            refine ⟨5915939518887058586521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 504826838945028999383125 5915939518887058586521)
            ·
              rfl

theorem cell21_699916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 8].length) (baseStart_699916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699916 prefixEnd_699916 := by exact prefixLift 699916
  have htrace : WordTrace (prefixWord ++ tailWord_699916) baseStart_699916 baseEnd_699916 := by
    simpa [prefixWord, tailWord_699916, baseEnd_699916] using wordTrace_append hprefix tailTrace_699916
  have hstable : (prefixWord ++ tailWord_699916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699916).length < 2 ^ (prefixWord ++ tailWord_699916).sum := by decide
  have hdescent : baseEnd_699916 < baseStart_699916 := by decide
  rcases family_descends (prefixWord ++ tailWord_699916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699930 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_699930 : Nat := 118140960795 + 699930 * 2 ^ 59
def prefixEnd_699930 : Nat := 4983230072969 + 3 ^ 40 * 699930 * 2
def baseEnd_699930 : Nat := 159733562000689668602705

theorem tailTrace_699930 : CollatzResearch.WordTrace tailWord_699930 prefixEnd_699930 159733562000689668602705 := by
  unfold tailWord_699930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6382136088570155843040311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17019029569520415581440829 6382136088570155843040311)
  ·
    refine ⟨9573204132855233764560467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6382136088570155843040311 9573204132855233764560467)
    ·
      refine ⟨14359806199282850646840701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9573204132855233764560467 14359806199282850646840701)
      ·
        refine ⟨5384927324731068992565263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14359806199282850646840701 5384927324731068992565263)
        ·
          refine ⟨8077390987096603488847895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5384927324731068992565263 8077390987096603488847895)
          ·
            refine ⟨12116086480644905233271843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8077390987096603488847895 12116086480644905233271843)
            ·
              refine ⟨18174129720967357849907765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12116086480644905233271843 18174129720967357849907765)
              ·
                refine ⟨1703824661340689798428853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18174129720967357849907765 1703824661340689798428853)
                ·
                  refine ⟨159733562000689668602705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1703824661340689798428853 159733562000689668602705)
                  ·
                    rfl

theorem cell21_699930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_699930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_699930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_699930 prefixEnd_699930 := by exact prefixLift 699930
  have htrace : WordTrace (prefixWord ++ tailWord_699930) baseStart_699930 baseEnd_699930 := by
    simpa [prefixWord, tailWord_699930, baseEnd_699930] using wordTrace_append hprefix tailTrace_699930
  have hstable : (prefixWord ++ tailWord_699930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699930).length < 2 ^ (prefixWord ++ tailWord_699930).sum := by decide
  have hdescent : baseEnd_699930 < baseStart_699930 := by decide
  rcases family_descends (prefixWord ++ tailWord_699930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700037 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 4]
def baseStart_700037 : Nat := 118140960795 + 700037 * 2 ^ 59
def prefixEnd_700037 : Nat := 4983230072969 + 3 ^ 40 * 700037 * 2
def baseEnd_700037 : Nat := 159757980858481260319153

theorem tailTrace_700037 : CollatzResearch.WordTrace tailWord_700037 prefixEnd_700037 159757980858481260319153 := by
  unfold tailWord_700037
  simp only [CollatzResearch.WordTrace]
  refine ⟨25532446964892980646306365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17021631309928653764204243 25532446964892980646306365)
  ·
    refine ⟨9574667611834867742364887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25532446964892980646306365 9574667611834867742364887)
    ·
      refine ⟨14362001417752301613547331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9574667611834867742364887 14362001417752301613547331)
      ·
        refine ⟨21543002126628452420320997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14362001417752301613547331 21543002126628452420320997)
        ·
          refine ⟨4039312898742834828810187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21543002126628452420320997 4039312898742834828810187)
          ·
            refine ⟨6058969348114252243215281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4039312898742834828810187 6058969348114252243215281)
            ·
              refine ⟨4544227011085689182411461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6058969348114252243215281 4544227011085689182411461)
              ·
                refine ⟨852042564578566721702149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4544227011085689182411461 852042564578566721702149)
                ·
                  refine ⟨159757980858481260319153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 852042564578566721702149 159757980858481260319153)
                  ·
                    rfl

theorem cell21_700037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_700037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700037 prefixEnd_700037 := by exact prefixLift 700037
  have htrace : WordTrace (prefixWord ++ tailWord_700037) baseStart_700037 baseEnd_700037 := by
    simpa [prefixWord, tailWord_700037, baseEnd_700037] using wordTrace_append hprefix tailTrace_700037
  have hstable : (prefixWord ++ tailWord_700037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700037).length < 2 ^ (prefixWord ++ tailWord_700037).sum := by decide
  have hdescent : baseEnd_700037 < baseStart_700037 := by decide
  rcases family_descends (prefixWord ++ tailWord_700037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700102 : List Nat := [6, 1, 2, 1, 1, 1, 3, 6]
def baseStart_700102 : Nat := 118140960795 + 700102 * 2 ^ 59
def prefixEnd_700102 : Nat := 4983230072969 + 3 ^ 40 * 700102 * 2
def baseEnd_700102 : Nat := 53257604914685197245229

theorem tailTrace_700102 : CollatzResearch.WordTrace tailWord_700102 prefixEnd_700102 53257604914685197245229 := by
  unfold tailWord_700102
  simp only [CollatzResearch.WordTrace]
  refine ⟨797963053426796773356955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17023211806438331164948373 797963053426796773356955)
  ·
    refine ⟨1196944580140195160035433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 797963053426796773356955 1196944580140195160035433)
    ·
      refine ⟨897708435105146370026575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1196944580140195160035433 897708435105146370026575)
      ·
        refine ⟨1346562652657719555039863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897708435105146370026575 1346562652657719555039863)
        ·
          refine ⟨2019843978986579332559795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346562652657719555039863 2019843978986579332559795)
          ·
            refine ⟨3029765968479868998839693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019843978986579332559795 3029765968479868998839693)
            ·
              refine ⟨1136162238179950874564885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3029765968479868998839693 1136162238179950874564885)
              ·
                refine ⟨53257604914685197245229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1136162238179950874564885 53257604914685197245229)
                ·
                  rfl

theorem cell21_700102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_700102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700102 prefixEnd_700102 := by exact prefixLift 700102
  have htrace : WordTrace (prefixWord ++ tailWord_700102) baseStart_700102 baseEnd_700102 := by
    simpa [prefixWord, tailWord_700102, baseEnd_700102] using wordTrace_append hprefix tailTrace_700102
  have hstable : (prefixWord ++ tailWord_700102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700102).length < 2 ^ (prefixWord ++ tailWord_700102).sum := by decide
  have hdescent : baseEnd_700102 < baseStart_700102 := by decide
  rcases family_descends (prefixWord ++ tailWord_700102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700113 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 4]
def baseStart_700113 : Nat := 118140960795 + 700113 * 2 ^ 59
def prefixEnd_700113 : Nat := 4983230072969 + 3 ^ 40 * 700113 * 2
def baseEnd_700113 : Nat := 159775325093922017052331

theorem tailTrace_700113 : CollatzResearch.WordTrace tailWord_700113 prefixEnd_700113 159775325093922017052331 := by
  unfold tailWord_700113
  simp only [CollatzResearch.WordTrace]
  refine ⟨25535218912617645626072993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17023479275078430417381995 25535218912617645626072993)
  ·
    refine ⟨19151414184463234219554745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25535218912617645626072993 19151414184463234219554745)
    ·
      refine ⟨14363560638347425664666059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19151414184463234219554745 14363560638347425664666059)
      ·
        refine ⟨21545340957521138496999089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14363560638347425664666059 21545340957521138496999089)
        ·
          refine ⟨16159005718140853872749317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21545340957521138496999089 16159005718140853872749317)
          ·
            refine ⟨3029813572151410101140497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16159005718140853872749317 3029813572151410101140497)
            ·
              refine ⟨2272360179113557575855373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3029813572151410101140497 2272360179113557575855373)
              ·
                refine ⟨852135067167584090945765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2272360179113557575855373 852135067167584090945765)
                ·
                  refine ⟨159775325093922017052331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 852135067167584090945765 159775325093922017052331)
                  ·
                    rfl

theorem cell21_700113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_700113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700113 prefixEnd_700113 := by exact prefixLift 700113
  have htrace : WordTrace (prefixWord ++ tailWord_700113) baseStart_700113 baseEnd_700113 := by
    simpa [prefixWord, tailWord_700113, baseEnd_700113] using wordTrace_append hprefix tailTrace_700113
  have hstable : (prefixWord ++ tailWord_700113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700113).length < 2 ^ (prefixWord ++ tailWord_700113).sum := by decide
  have hdescent : baseEnd_700113 < baseStart_700113 := by decide
  rcases family_descends (prefixWord ++ tailWord_700113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700178 : List Nat := [3, 2, 4, 1, 1, 3, 2, 5]
def baseStart_700178 : Nat := 118140960795 + 700178 * 2 ^ 59
def prefixEnd_700178 : Nat := 4983230072969 + 3 ^ 40 * 700178 * 2
def baseEnd_700178 : Nat := 53263386326498782822955

theorem tailTrace_700178 : CollatzResearch.WordTrace tailWord_700178 prefixEnd_700178 53263386326498782822955 := by
  unfold tailWord_700178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6384397414345540431797297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17025059771588107818126125 6384397414345540431797297)
  ·
    refine ⟨4788298060759155323847973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6384397414345540431797297 4788298060759155323847973)
    ·
      refine ⟨897805886392341623221495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4788298060759155323847973 897805886392341623221495)
      ·
        refine ⟨1346708829588512434832243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897805886392341623221495 1346708829588512434832243)
        ·
          refine ⟨2020063244382768652248365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346708829588512434832243 2020063244382768652248365)
          ·
            refine ⟨757523716643538244593137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2020063244382768652248365 757523716643538244593137)
            ·
              refine ⟨568142787482653683444853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757523716643538244593137 568142787482653683444853)
              ·
                refine ⟨53263386326498782822955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 568142787482653683444853 53263386326498782822955)
                ·
                  rfl

theorem cell21_700178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_700178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700178 prefixEnd_700178 := by exact prefixLift 700178
  have htrace : WordTrace (prefixWord ++ tailWord_700178) baseStart_700178 baseEnd_700178 := by
    simpa [prefixWord, tailWord_700178, baseEnd_700178] using wordTrace_append hprefix tailTrace_700178
  have hstable : (prefixWord ++ tailWord_700178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700178).length < 2 ^ (prefixWord ++ tailWord_700178).sum := by decide
  have hdescent : baseEnd_700178 < baseStart_700178 := by decide
  rcases family_descends (prefixWord ++ tailWord_700178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700223 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 4]
def baseStart_700223 : Nat := 118140960795 + 700223 * 2 ^ 59
def prefixEnd_700223 : Nat := 4983230072969 + 3 ^ 40 * 700223 * 2
def baseEnd_700223 : Nat := 159800428592586270218773

theorem tailTrace_700223 : CollatzResearch.WordTrace tailWord_700223 prefixEnd_700223 159800428592586270218773 := by
  unfold tailWord_700223
  simp only [CollatzResearch.WordTrace]
  refine ⟨25539230942219134412577323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17026153961479422941718215 25539230942219134412577323)
  ·
    refine ⟨38308846413328701618865985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25539230942219134412577323 38308846413328701618865985)
    ·
      refine ⟨28731634809996526214149489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38308846413328701618865985 28731634809996526214149489)
      ·
        refine ⟨21548726107497394660612117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28731634809996526214149489 21548726107497394660612117)
        ·
          refine ⟨1010096536288940374716193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21548726107497394660612117 1010096536288940374716193)
          ·
            refine ⟨757572402216705281037145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1010096536288940374716193 757572402216705281037145)
            ·
              refine ⟨568179301662528960777859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757572402216705281037145 568179301662528960777859)
              ·
                refine ⟨852268952493793441166789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568179301662528960777859 852268952493793441166789)
                ·
                  refine ⟨159800428592586270218773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 852268952493793441166789 159800428592586270218773)
                  ·
                    rfl

theorem cell21_700223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 4].length) (baseStart_700223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700223 prefixEnd_700223 := by exact prefixLift 700223
  have htrace : WordTrace (prefixWord ++ tailWord_700223) baseStart_700223 baseEnd_700223 := by
    simpa [prefixWord, tailWord_700223, baseEnd_700223] using wordTrace_append hprefix tailTrace_700223
  have hstable : (prefixWord ++ tailWord_700223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700223).length < 2 ^ (prefixWord ++ tailWord_700223).sum := by decide
  have hdescent : baseEnd_700223 < baseStart_700223 := by decide
  rcases family_descends (prefixWord ++ tailWord_700223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700268 : List Nat := [2, 2, 1, 1, 4, 2, 4, 2, 3]
def baseStart_700268 : Nat := 118140960795 + 700268 * 2 ^ 59
def prefixEnd_700268 : Nat := 4983230072969 + 3 ^ 40 * 700268 * 2
def baseEnd_700268 : Nat := 159810698205676191968681

theorem tailTrace_700268 : CollatzResearch.WordTrace tailWord_700268 prefixEnd_700268 159810698205676191968681 := by
  unfold tailWord_700268
  simp only [CollatzResearch.WordTrace]
  refine ⟨12770436113528053548982729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17027248151370738065310305 12770436113528053548982729)
  ·
    refine ⟨9577827085146040161737047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12770436113528053548982729 9577827085146040161737047)
    ·
      refine ⟨14366740627719060242605571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9577827085146040161737047 14366740627719060242605571)
      ·
        refine ⟨21550110941578590363908357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14366740627719060242605571 21550110941578590363908357)
        ·
          refine ⟨4040645801545985693232817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21550110941578590363908357 4040645801545985693232817)
          ·
            refine ⟨3030484351159489269924613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4040645801545985693232817 3030484351159489269924613)
            ·
              refine ⟨568215815842404238110865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3030484351159489269924613 568215815842404238110865)
              ·
                refine ⟨426161861881803178583149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568215815842404238110865 426161861881803178583149)
                ·
                  refine ⟨159810698205676191968681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426161861881803178583149 159810698205676191968681)
                  ·
                    rfl

theorem cell21_700268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_700268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700268 prefixEnd_700268 := by exact prefixLift 700268
  have htrace : WordTrace (prefixWord ++ tailWord_700268) baseStart_700268 baseEnd_700268 := by
    simpa [prefixWord, tailWord_700268, baseEnd_700268] using wordTrace_append hprefix tailTrace_700268
  have hstable : (prefixWord ++ tailWord_700268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700268).length < 2 ^ (prefixWord ++ tailWord_700268).sum := by decide
  have hdescent : baseEnd_700268 < baseStart_700268 := by decide
  rcases family_descends (prefixWord ++ tailWord_700268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700327 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 5]
def baseStart_700327 : Nat := 118140960795 + 700327 * 2 ^ 59
def prefixEnd_700327 : Nat := 4983230072969 + 3 ^ 40 * 700327 * 2
def baseEnd_700327 : Nat := 159824162809505200485227

theorem tailTrace_700327 : CollatzResearch.WordTrace tailWord_700327 prefixEnd_700327 159824162809505200485227 := by
  unfold tailWord_700327
  simp only [CollatzResearch.WordTrace]
  refine ⟨25543024133842360174363235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17028682755894906782908823 25543024133842360174363235)
  ·
    refine ⟨38314536200763540261544853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25543024133842360174363235 38314536200763540261544853)
    ·
      refine ⟨1795993884410790949759915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38314536200763540261544853 1795993884410790949759915)
      ·
        refine ⟨2693990826616186424639873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795993884410790949759915 2693990826616186424639873)
        ·
          refine ⟨2020493119962139818479905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2693990826616186424639873 2020493119962139818479905)
          ·
            refine ⟨1515369839971604863859929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2020493119962139818479905 1515369839971604863859929)
            ·
              refine ⟨1136527379978703647894947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1515369839971604863859929 1136527379978703647894947)
              ·
                refine ⟨1704791069968055471842421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136527379978703647894947 1704791069968055471842421)
                ·
                  refine ⟨159824162809505200485227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1704791069968055471842421 159824162809505200485227)
                  ·
                    rfl

theorem cell21_700327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 5].length) (baseStart_700327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700327 prefixEnd_700327 := by exact prefixLift 700327
  have htrace : WordTrace (prefixWord ++ tailWord_700327) baseStart_700327 baseEnd_700327 := by
    simpa [prefixWord, tailWord_700327, baseEnd_700327] using wordTrace_append hprefix tailTrace_700327
  have hstable : (prefixWord ++ tailWord_700327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700327).length < 2 ^ (prefixWord ++ tailWord_700327).sum := by decide
  have hdescent : baseEnd_700327 < baseStart_700327 := by decide
  rcases family_descends (prefixWord ++ tailWord_700327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700437 : List Nat := [1, 3, 2, 1, 5, 2, 2, 2, 3]
def baseStart_700437 : Nat := 118140960795 + 700437 * 2 ^ 59
def prefixEnd_700437 : Nat := 4983230072969 + 3 ^ 40 * 700437 * 2
def baseEnd_700437 : Nat := 159849266308169453651669

theorem tailTrace_700437 : CollatzResearch.WordTrace tailWord_700437 prefixEnd_700437 159849266308169453651669 := by
  unfold tailWord_700437
  simp only [CollatzResearch.WordTrace]
  refine ⟨25547036163443848960867565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17031357442295899307245043 25547036163443848960867565)
  ·
    refine ⟨9580138561291443360325337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25547036163443848960867565 9580138561291443360325337)
    ·
      refine ⟨7185103920968582520244003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9580138561291443360325337 7185103920968582520244003)
      ·
        refine ⟨10777655881452873780366005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7185103920968582520244003 10777655881452873780366005)
        ·
          refine ⟨1010405238886206916909313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10777655881452873780366005 1010405238886206916909313)
          ·
            refine ⟨757803929164655187681985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1010405238886206916909313 757803929164655187681985)
            ·
              refine ⟨568352946873491390761489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757803929164655187681985 568352946873491390761489)
              ·
                refine ⟨426264710155118543071117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568352946873491390761489 426264710155118543071117)
                ·
                  refine ⟨159849266308169453651669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426264710155118543071117 159849266308169453651669)
                  ·
                    rfl

theorem cell21_700437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_700437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700437 prefixEnd_700437 := by exact prefixLift 700437
  have htrace : WordTrace (prefixWord ++ tailWord_700437) baseStart_700437 baseEnd_700437 := by
    simpa [prefixWord, tailWord_700437, baseEnd_700437] using wordTrace_append hprefix tailTrace_700437
  have hstable : (prefixWord ++ tailWord_700437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700437).length < 2 ^ (prefixWord ++ tailWord_700437).sum := by decide
  have hdescent : baseEnd_700437 < baseStart_700437 := by decide
  rcases family_descends (prefixWord ++ tailWord_700437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700462 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_700462 : Nat := 118140960795 + 700462 * 2 ^ 59
def prefixEnd_700462 : Nat := 4983230072969 + 3 ^ 40 * 700462 * 2
def baseEnd_700462 : Nat := 159854971648774965734951

theorem tailTrace_700462 : CollatzResearch.WordTrace tailWord_700462 prefixEnd_700462 159854971648774965734951 := by
  unfold tailWord_700462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3193493498544159778815955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17031965325568852153685093 3193493498544159778815955)
  ·
    refine ⟨4790240247816239668223933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3193493498544159778815955 4790240247816239668223933)
    ·
      refine ⟨1796340092931089875583975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4790240247816239668223933 1796340092931089875583975)
      ·
        refine ⟨2694510139396634813375963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796340092931089875583975 2694510139396634813375963)
        ·
          refine ⟨4041765209094952220063945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694510139396634813375963 4041765209094952220063945)
          ·
            refine ⟨3031323906821214165047959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4041765209094952220063945 3031323906821214165047959)
            ·
              refine ⟨4546985860231821247571939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031323906821214165047959 4546985860231821247571939)
              ·
                refine ⟨6820478790347731871357909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546985860231821247571939 6820478790347731871357909)
                ·
                  refine ⟨159854971648774965734951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6820478790347731871357909 159854971648774965734951)
                  ·
                    rfl

theorem cell21_700462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_700462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700462 prefixEnd_700462 := by exact prefixLift 700462
  have htrace : WordTrace (prefixWord ++ tailWord_700462) baseStart_700462 baseEnd_700462 := by
    simpa [prefixWord, tailWord_700462, baseEnd_700462] using wordTrace_append hprefix tailTrace_700462
  have hstable : (prefixWord ++ tailWord_700462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700462).length < 2 ^ (prefixWord ++ tailWord_700462).sum := by decide
  have hdescent : baseEnd_700462 < baseStart_700462 := by decide
  rcases family_descends (prefixWord ++ tailWord_700462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700476 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_700476 : Nat := 118140960795 + 700476 * 2 ^ 59
def prefixEnd_700476 : Nat := 4983230072969 + 3 ^ 40 * 700476 * 2
def baseEnd_700476 : Nat := 159858166639514052501589

theorem tailTrace_700476 : CollatzResearch.WordTrace tailWord_700476 prefixEnd_700476 159858166639514052501589 := by
  unfold tailWord_700476
  simp only [CollatzResearch.WordTrace]
  refine ⟨12774229305151279310768641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17032305740201705747691521 12774229305151279310768641)
  ·
    refine ⟨9580671978863459483076481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12774229305151279310768641 9580671978863459483076481)
    ·
      refine ⟨7185503984147594612307361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9580671978863459483076481 7185503984147594612307361)
      ·
        refine ⟨5389127988110695959230521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7185503984147594612307361 5389127988110695959230521)
        ·
          refine ⟨4041845991083021969422891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5389127988110695959230521 4041845991083021969422891)
          ·
            refine ⟨6062768986624532954134337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4041845991083021969422891 6062768986624532954134337)
            ·
              refine ⟨4547076739968399715600753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6062768986624532954134337 4547076739968399715600753)
              ·
                refine ⟨3410307554976299786700565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4547076739968399715600753 3410307554976299786700565)
                ·
                  refine ⟨159858166639514052501589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3410307554976299786700565 159858166639514052501589)
                  ·
                    rfl

theorem cell21_700476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_700476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700476 prefixEnd_700476 := by exact prefixLift 700476
  have htrace : WordTrace (prefixWord ++ tailWord_700476) baseStart_700476 baseEnd_700476 := by
    simpa [prefixWord, tailWord_700476, baseEnd_700476] using wordTrace_append hprefix tailTrace_700476
  have hstable : (prefixWord ++ tailWord_700476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700476).length < 2 ^ (prefixWord ++ tailWord_700476).sum := by decide
  have hdescent : baseEnd_700476 < baseStart_700476 := by decide
  rcases family_descends (prefixWord ++ tailWord_700476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700493 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 6]
def baseStart_700493 : Nat := 118140960795 + 700493 * 2 ^ 59
def prefixEnd_700493 : Nat := 4983230072969 + 3 ^ 40 * 700493 * 2
def baseEnd_700493 : Nat := 159862046271125800718221

theorem tailTrace_700493 : CollatzResearch.WordTrace tailWord_700493 prefixEnd_700493 159862046271125800718221 := by
  unfold tailWord_700493
  simp only [CollatzResearch.WordTrace]
  refine ⟨25549078651240970524906133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17032719100827313683270755 25549078651240970524906133)
  ·
    refine ⟨1197613061776920493354975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25549078651240970524906133 1197613061776920493354975)
    ·
      refine ⟨1796419592665380740032463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197613061776920493354975 1796419592665380740032463)
      ·
        refine ⟨2694629388998071110048695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796419592665380740032463 2694629388998071110048695)
        ·
          refine ⟨4041944083497106665073043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694629388998071110048695 4041944083497106665073043)
          ·
            refine ⟨6062916125245659997609565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4041944083497106665073043 6062916125245659997609565)
            ·
              refine ⟨2273593546967122499103587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6062916125245659997609565 2273593546967122499103587)
              ·
                refine ⟨3410390320450683748655381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273593546967122499103587 3410390320450683748655381)
                ·
                  refine ⟨159862046271125800718221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3410390320450683748655381 159862046271125800718221)
                  ·
                    rfl

theorem cell21_700493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_700493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700493 prefixEnd_700493 := by exact prefixLift 700493
  have htrace : WordTrace (prefixWord ++ tailWord_700493) baseStart_700493 baseEnd_700493 := by
    simpa [prefixWord, tailWord_700493, baseEnd_700493] using wordTrace_append hprefix tailTrace_700493
  have hstable : (prefixWord ++ tailWord_700493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700493).length < 2 ^ (prefixWord ++ tailWord_700493).sum := by decide
  have hdescent : baseEnd_700493 < baseStart_700493 := by decide
  rcases family_descends (prefixWord ++ tailWord_700493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700521 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 5]
def baseStart_700521 : Nat := 118140960795 + 700521 * 2 ^ 59
def prefixEnd_700521 : Nat := 4983230072969 + 3 ^ 40 * 700521 * 2
def baseEnd_700521 : Nat := 159868436252603974251497

theorem tailTrace_700521 : CollatzResearch.WordTrace tailWord_700521 prefixEnd_700521 159868436252603974251497 := by
  unfold tailWord_700521
  simp only [CollatzResearch.WordTrace]
  refine ⟨25550099895139531306925417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17033399930093020871283611 25550099895139531306925417)
  ·
    refine ⟨19162574921354648480194063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25550099895139531306925417 19162574921354648480194063)
    ·
      refine ⟨28743862382031972720291095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19162574921354648480194063 28743862382031972720291095)
      ·
        refine ⟨43115793573047959080436643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28743862382031972720291095 43115793573047959080436643)
        ·
          refine ⟨64673690359571938620654965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43115793573047959080436643 64673690359571938620654965)
          ·
            refine ⟨6063158471209869245686403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64673690359571938620654965 6063158471209869245686403)
            ·
              refine ⟨9094737706814803868529605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6063158471209869245686403 9094737706814803868529605)
              ·
                refine ⟨1705263320027775725349301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9094737706814803868529605 1705263320027775725349301)
                ·
                  refine ⟨159868436252603974251497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1705263320027775725349301 159868436252603974251497)
                  ·
                    rfl

theorem cell21_700521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_700521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700521 prefixEnd_700521 := by exact prefixLift 700521
  have htrace : WordTrace (prefixWord ++ tailWord_700521) baseStart_700521 baseEnd_700521 := by
    simpa [prefixWord, tailWord_700521, baseEnd_700521] using wordTrace_append hprefix tailTrace_700521
  have hstable : (prefixWord ++ tailWord_700521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700521).length < 2 ^ (prefixWord ++ tailWord_700521).sum := by decide
  have hdescent : baseEnd_700521 < baseStart_700521 := by decide
  rcases family_descends (prefixWord ++ tailWord_700521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700524 : List Nat := [2, 2, 1, 1, 3, 5, 2, 5]
def baseStart_700524 : Nat := 118140960795 + 700524 * 2 ^ 59
def prefixEnd_700524 : Nat := 4983230072969 + 3 ^ 40 * 700524 * 2
def baseEnd_700524 : Nat := 53289706964492211900497

theorem tailTrace_700524 : CollatzResearch.WordTrace tailWord_700524 prefixEnd_700524 53289706964492211900497 := by
  unfold tailWord_700524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12775104657064331409642313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17033472876085775212856417 12775104657064331409642313)
  ·
    refine ⟨9581328492798248557231735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12775104657064331409642313 9581328492798248557231735)
    ·
      refine ⟨14371992739197372835847603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9581328492798248557231735 14371992739197372835847603)
      ·
        refine ⟨21557989108796059253771405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14371992739197372835847603 21557989108796059253771405)
        ·
          refine ⟨8084245915798522220164277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21557989108796059253771405 8084245915798522220164277)
          ·
            refine ⟨757898054606111458140401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8084245915798522220164277 757898054606111458140401)
            ·
              refine ⟨568423540954583593605301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757898054606111458140401 568423540954583593605301)
              ·
                refine ⟨53289706964492211900497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 568423540954583593605301 53289706964492211900497)
                ·
                  rfl

theorem cell21_700524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_700524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700524 prefixEnd_700524 := by exact prefixLift 700524
  have htrace : WordTrace (prefixWord ++ tailWord_700524) baseStart_700524 baseEnd_700524 := by
    simpa [prefixWord, tailWord_700524, baseEnd_700524] using wordTrace_append hprefix tailTrace_700524
  have hstable : (prefixWord ++ tailWord_700524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700524).length < 2 ^ (prefixWord ++ tailWord_700524).sum := by decide
  have hdescent : baseEnd_700524 < baseStart_700524 := by decide
  rcases family_descends (prefixWord ++ tailWord_700524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700606 : List Nat := [4, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_700606 : Nat := 118140960795 + 700606 * 2 ^ 59
def prefixEnd_700606 : Nat := 4983230072969 + 3 ^ 40 * 700606 * 2
def baseEnd_700606 : Nat := 159887834410662715334657

theorem tailTrace_700606 : CollatzResearch.WordTrace tailWord_700606 prefixEnd_700606 159887834410662715334657 := by
  unfold tailWord_700606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194150012478948852971209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17035466733221060549179781 3194150012478948852971209)
  ·
    refine ⟨2395612509359211639728407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3194150012478948852971209 2395612509359211639728407)
    ·
      refine ⟨3593418764038817459592611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2395612509359211639728407 3593418764038817459592611)
      ·
        refine ⟨5390128146058226189388917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3593418764038817459592611 5390128146058226189388917)
        ·
          refine ⟨505324513692958705255211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5390128146058226189388917 505324513692958705255211)
          ·
            refine ⟨757986770539438057882817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505324513692958705255211 757986770539438057882817)
            ·
              refine ⟨568490077904578543412113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757986770539438057882817 568490077904578543412113)
              ·
                refine ⟨426367558428433907559085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568490077904578543412113 426367558428433907559085)
                ·
                  refine ⟨159887834410662715334657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426367558428433907559085 159887834410662715334657)
                  ·
                    rfl

theorem cell21_700606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_700606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700606 prefixEnd_700606 := by exact prefixLift 700606
  have htrace : WordTrace (prefixWord ++ tailWord_700606) baseStart_700606 baseEnd_700606 := by
    simpa [prefixWord, tailWord_700606, baseEnd_700606] using wordTrace_append hprefix tailTrace_700606
  have hstable : (prefixWord ++ tailWord_700606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700606).length < 2 ^ (prefixWord ++ tailWord_700606).sum := by decide
  have hdescent : baseEnd_700606 < baseStart_700606 := by decide
  rcases family_descends (prefixWord ++ tailWord_700606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700611 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 10]
def baseStart_700611 : Nat := 118140960795 + 700611 * 2 ^ 59
def prefixEnd_700611 : Nat := 4983230072969 + 3 ^ 40 * 700611 * 2
def baseEnd_700611 : Nat := 159888975478783817751313

theorem tailTrace_700611 : CollatzResearch.WordTrace tailWord_700611 prefixEnd_700611 159888975478783817751313 := by
  unfold tailWord_700611
  simp only [CollatzResearch.WordTrace]
  refine ⟨25553382464813476677701687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17035588309875651118467791 25553382464813476677701687)
  ·
    refine ⟨38330073697220215016552531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25553382464813476677701687 38330073697220215016552531)
    ·
      refine ⟨57495110545830322524828797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38330073697220215016552531 57495110545830322524828797)
      ·
        refine ⟨21560666454686370946810799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57495110545830322524828797 21560666454686370946810799)
        ·
          refine ⟨32340999682029556420216199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21560666454686370946810799 32340999682029556420216199)
          ·
            refine ⟨48511499523044334630324299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32340999682029556420216199 48511499523044334630324299)
            ·
              refine ⟨72767249284566501945486449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48511499523044334630324299 72767249284566501945486449)
              ·
                refine ⟨54575436963424876459114837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72767249284566501945486449 54575436963424876459114837)
                ·
                  refine ⟨159888975478783817751313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 54575436963424876459114837 159888975478783817751313)
                  ·
                    rfl

theorem cell21_700611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_700611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700611 prefixEnd_700611 := by exact prefixLift 700611
  have htrace : WordTrace (prefixWord ++ tailWord_700611) baseStart_700611 baseEnd_700611 := by
    simpa [prefixWord, tailWord_700611, baseEnd_700611] using wordTrace_append hprefix tailTrace_700611
  have hstable : (prefixWord ++ tailWord_700611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700611).length < 2 ^ (prefixWord ++ tailWord_700611).sum := by decide
  have hdescent : baseEnd_700611 < baseStart_700611 := by decide
  rcases family_descends (prefixWord ++ tailWord_700611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700679 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 4]
def baseStart_700679 : Nat := 118140960795 + 700679 * 2 ^ 59
def prefixEnd_700679 : Nat := 4983230072969 + 3 ^ 40 * 700679 * 2
def baseEnd_700679 : Nat := 159904494005230810617841

theorem tailTrace_700679 : CollatzResearch.WordTrace tailWord_700679 prefixEnd_700679 159904494005230810617841 := by
  unfold tailWord_700679
  simp only [CollatzResearch.WordTrace]
  refine ⟨25555862628567124291177091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17037241752378082860784727 25555862628567124291177091)
  ·
    refine ⟨38333793942850686436765637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25555862628567124291177091 38333793942850686436765637)
    ·
      refine ⟨7187586364284503706893557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38333793942850686436765637 7187586364284503706893557)
      ·
        refine ⟨673836221651672222521271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7187586364284503706893557 673836221651672222521271)
        ·
          refine ⟨1010754332477508333781907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673836221651672222521271 1010754332477508333781907)
          ·
            refine ⟨1516131498716262500672861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010754332477508333781907 1516131498716262500672861)
            ·
              refine ⟨568549312018598437752323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1516131498716262500672861 568549312018598437752323)
              ·
                refine ⟨852823968027897656628485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568549312018598437752323 852823968027897656628485)
                ·
                  refine ⟨159904494005230810617841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 852823968027897656628485 159904494005230810617841)
                  ·
                    rfl

theorem cell21_700679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 4].length) (baseStart_700679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700679 prefixEnd_700679 := by exact prefixLift 700679
  have htrace : WordTrace (prefixWord ++ tailWord_700679) baseStart_700679 baseEnd_700679 := by
    simpa [prefixWord, tailWord_700679, baseEnd_700679] using wordTrace_append hprefix tailTrace_700679
  have hstable : (prefixWord ++ tailWord_700679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700679).length < 2 ^ (prefixWord ++ tailWord_700679).sum := by decide
  have hdescent : baseEnd_700679 < baseStart_700679 := by decide
  rcases family_descends (prefixWord ++ tailWord_700679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700704 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_700704 : Nat := 118140960795 + 700704 * 2 ^ 59
def prefixEnd_700704 : Nat := 4983230072969 + 3 ^ 40 * 700704 * 2
def baseEnd_700704 : Nat := 159910199345836322701123

theorem tailTrace_700704 : CollatzResearch.WordTrace tailWord_700704 prefixEnd_700704 159910199345836322701123 := by
  unfold tailWord_700704
  simp only [CollatzResearch.WordTrace]
  refine ⟨12778387226738276780418583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17037849635651035707224777 12778387226738276780418583)
  ·
    refine ⟨19167580840107415170627875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12778387226738276780418583 19167580840107415170627875)
    ·
      refine ⟨28751371260161122755941813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19167580840107415170627875 28751371260161122755941813)
      ·
        refine ⟨2695441055640105258369545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28751371260161122755941813 2695441055640105258369545)
        ·
          refine ⟨2021580791730078943777159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2695441055640105258369545 2021580791730078943777159)
          ·
            refine ⟨3032371187595118415665739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021580791730078943777159 3032371187595118415665739)
            ·
              refine ⟨4548556781392677623498609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032371187595118415665739 4548556781392677623498609)
              ·
                refine ⟨3411417586044508217623957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4548556781392677623498609 3411417586044508217623957)
                ·
                  refine ⟨159910199345836322701123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3411417586044508217623957 159910199345836322701123)
                  ·
                    rfl

theorem cell21_700704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_700704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700704 prefixEnd_700704 := by exact prefixLift 700704
  have htrace : WordTrace (prefixWord ++ tailWord_700704) baseStart_700704 baseEnd_700704 := by
    simpa [prefixWord, tailWord_700704, baseEnd_700704] using wordTrace_append hprefix tailTrace_700704
  have hstable : (prefixWord ++ tailWord_700704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700704).length < 2 ^ (prefixWord ++ tailWord_700704).sum := by decide
  have hdescent : baseEnd_700704 < baseStart_700704 := by decide
  rcases family_descends (prefixWord ++ tailWord_700704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700811 : List Nat := [1, 1, 1, 1, 4, 5, 3, 5]
def baseStart_700811 : Nat := 118140960795 + 700811 * 2 ^ 59
def prefixEnd_700811 : Nat := 4983230072969 + 3 ^ 40 * 700811 * 2
def baseEnd_700811 : Nat := 53311539401209304805857

theorem tailTrace_700811 : CollatzResearch.WordTrace tailWord_700811 prefixEnd_700811 53311539401209304805857 := by
  unfold tailWord_700811
  simp only [CollatzResearch.WordTrace]
  refine ⟨25560677064088910834982287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17040451376059273889988191 25560677064088910834982287)
  ·
    refine ⟨38341015596133366252473431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25560677064088910834982287 38341015596133366252473431)
    ·
      refine ⟨57511523394200049378710147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38341015596133366252473431 57511523394200049378710147)
      ·
        refine ⟨86267285091300074068065221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57511523394200049378710147 86267285091300074068065221)
        ·
          refine ⟨16175115954618763887762229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86267285091300074068065221 16175115954618763887762229)
          ·
            refine ⟨1516417120745509114477709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16175115954618763887762229 1516417120745509114477709)
            ·
              refine ⟨568656420279565917929141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1516417120745509114477709 568656420279565917929141)
              ·
                refine ⟨53311539401209304805857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 568656420279565917929141 53311539401209304805857)
                ·
                  rfl

theorem cell21_700811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 5].length) (baseStart_700811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700811 prefixEnd_700811 := by exact prefixLift 700811
  have htrace : WordTrace (prefixWord ++ tailWord_700811) baseStart_700811 baseEnd_700811 := by
    simpa [prefixWord, tailWord_700811, baseEnd_700811] using wordTrace_append hprefix tailTrace_700811
  have hstable : (prefixWord ++ tailWord_700811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700811).length < 2 ^ (prefixWord ++ tailWord_700811).sum := by decide
  have hdescent : baseEnd_700811 < baseStart_700811 := by decide
  rcases family_descends (prefixWord ++ tailWord_700811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700876 : List Nat := [2, 2, 1, 4, 3, 2, 1, 3, 3]
def baseStart_700876 : Nat := 118140960795 + 700876 * 2 ^ 59
def prefixEnd_700876 : Nat := 4983230072969 + 3 ^ 40 * 700876 * 2
def baseEnd_700876 : Nat := 159949452089202245834105

theorem tailTrace_700876 : CollatzResearch.WordTrace tailWord_700876 prefixEnd_700876 159949452089202245834105 := by
  unfold tailWord_700876
  simp only [CollatzResearch.WordTrace]
  refine ⟨12781523904426713468049241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17042031872568951290732321 12781523904426713468049241)
  ·
    refine ⟨9586142928320035101036931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12781523904426713468049241 9586142928320035101036931)
    ·
      refine ⟨14379214392480052651555397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9586142928320035101036931 14379214392480052651555397)
      ·
        refine ⟨2696102698590009872166637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14379214392480052651555397 2696102698590009872166637)
        ·
          refine ⟨1011038511971253702062489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2696102698590009872166637 1011038511971253702062489)
          ·
            refine ⟨758278883978440276546867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1011038511971253702062489 758278883978440276546867)
            ·
              refine ⟨1137418325967660414820301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758278883978440276546867 1137418325967660414820301)
              ·
                refine ⟨426531872237872655557613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137418325967660414820301 426531872237872655557613)
                ·
                  refine ⟨159949452089202245834105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426531872237872655557613 159949452089202245834105)
                  ·
                    rfl

theorem cell21_700876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_700876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700876 prefixEnd_700876 := by exact prefixLift 700876
  have htrace : WordTrace (prefixWord ++ tailWord_700876) baseStart_700876 baseEnd_700876 := by
    simpa [prefixWord, tailWord_700876, baseEnd_700876] using wordTrace_append hprefix tailTrace_700876
  have hstable : (prefixWord ++ tailWord_700876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700876).length < 2 ^ (prefixWord ++ tailWord_700876).sum := by decide
  have hdescent : baseEnd_700876 < baseStart_700876 := by decide
  rcases family_descends (prefixWord ++ tailWord_700876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700952 : List Nat := [2, 1, 2, 3, 3, 3, 2, 2, 3]
def baseStart_700952 : Nat := 118140960795 + 700952 * 2 ^ 59
def prefixEnd_700952 : Nat := 4983230072969 + 3 ^ 40 * 700952 * 2
def baseEnd_700952 : Nat := 159966796324643002567283

theorem tailTrace_700952 : CollatzResearch.WordTrace tailWord_700952 prefixEnd_700952 159966796324643002567283 := by
  unfold tailWord_700952
  simp only [CollatzResearch.WordTrace]
  refine ⟨12782909878289045957932555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17043879837718727943910073 12782909878289045957932555)
  ·
    refine ⟨19174364817433568936898833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12782909878289045957932555 19174364817433568936898833)
    ·
      refine ⟨14380773613075176702674125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19174364817433568936898833 14380773613075176702674125)
      ·
        refine ⟨5392790104903191263502797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14380773613075176702674125 5392790104903191263502797)
        ·
          refine ⟨2022296289338696723813549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5392790104903191263502797 2022296289338696723813549)
          ·
            refine ⟨758361108502011271430081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2022296289338696723813549 758361108502011271430081)
            ·
              refine ⟨568770831376508453572561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 758361108502011271430081 568770831376508453572561)
              ·
                refine ⟨426578123532381340179421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568770831376508453572561 426578123532381340179421)
                ·
                  refine ⟨159966796324643002567283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426578123532381340179421 159966796324643002567283)
                  ·
                    rfl

theorem cell21_700952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 3].length) (baseStart_700952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700952 prefixEnd_700952 := by exact prefixLift 700952
  have htrace : WordTrace (prefixWord ++ tailWord_700952) baseStart_700952 baseEnd_700952 := by
    simpa [prefixWord, tailWord_700952, baseEnd_700952] using wordTrace_append hprefix tailTrace_700952
  have hstable : (prefixWord ++ tailWord_700952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700952).length < 2 ^ (prefixWord ++ tailWord_700952).sum := by decide
  have hdescent : baseEnd_700952 < baseStart_700952 := by decide
  rcases family_descends (prefixWord ++ tailWord_700952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700963 : List Nat := [1, 1, 1, 4, 4, 3, 1, 6]
def baseStart_700963 : Nat := 118140960795 + 700963 * 2 ^ 59
def prefixEnd_700963 : Nat := 4983230072969 + 3 ^ 40 * 700963 * 2
def baseEnd_700963 : Nat := 53323102224836475961309

theorem tailTrace_700963 : CollatzResearch.WordTrace tailWord_700963 prefixEnd_700963 53323102224836475961309 := by
  unfold tailWord_700963
  simp only [CollatzResearch.WordTrace]
  refine ⟨25566220959538240794515543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17044147306358827196343695 25566220959538240794515543)
  ·
    refine ⟨38349331439307361191773315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25566220959538240794515543 38349331439307361191773315)
    ·
      refine ⟨57523997158961041787659973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38349331439307361191773315 57523997158961041787659973)
      ·
        refine ⟨10785749467305195335186245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57523997158961041787659973 10785749467305195335186245)
        ·
          refine ⟨2022328025119724125347421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10785749467305195335186245 2022328025119724125347421)
          ·
            refine ⟨758373009419896547005283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2022328025119724125347421 758373009419896547005283)
            ·
              refine ⟨1137559514129844820507925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758373009419896547005283 1137559514129844820507925)
              ·
                refine ⟨53323102224836475961309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1137559514129844820507925 53323102224836475961309)
                ·
                  rfl

theorem cell21_700963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 6].length) (baseStart_700963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700963 prefixEnd_700963 := by exact prefixLift 700963
  have htrace : WordTrace (prefixWord ++ tailWord_700963) baseStart_700963 baseEnd_700963 := by
    simpa [prefixWord, tailWord_700963, baseEnd_700963] using wordTrace_append hprefix tailTrace_700963
  have hstable : (prefixWord ++ tailWord_700963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700963).length < 2 ^ (prefixWord ++ tailWord_700963).sum := by decide
  have hdescent : baseEnd_700963 < baseStart_700963 := by decide
  rcases family_descends (prefixWord ++ tailWord_700963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_700991 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 6]
def baseStart_700991 : Nat := 118140960795 + 700991 * 2 ^ 59
def prefixEnd_700991 : Nat := 4983230072969 + 3 ^ 40 * 700991 * 2
def baseEnd_700991 : Nat := 159975696655987601417203

theorem tailTrace_700991 : CollatzResearch.WordTrace tailWord_700991 prefixEnd_700991 159975696655987601417203 := by
  unfold tailWord_700991
  simp only [CollatzResearch.WordTrace]
  refine ⟨25567242203436801576534827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17044828135624534384356551 25567242203436801576534827)
  ·
    refine ⟨38350863305155202364802241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25567242203436801576534827 38350863305155202364802241)
    ·
      refine ⟨28763147478866401773601681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38350863305155202364802241 28763147478866401773601681)
      ·
        refine ⟨21572360609149801330201261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28763147478866401773601681 21572360609149801330201261)
        ·
          refine ⟨8089635228431175498825473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21572360609149801330201261 8089635228431175498825473)
          ·
            refine ⟨6067226421323381624119105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8089635228431175498825473 6067226421323381624119105)
            ·
              refine ⟨4550419815992536218089329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6067226421323381624119105 4550419815992536218089329)
              ·
                refine ⟨3412814861994402163566997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4550419815992536218089329 3412814861994402163566997)
                ·
                  refine ⟨159975696655987601417203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3412814861994402163566997 159975696655987601417203)
                  ·
                    rfl

theorem cell21_700991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_700991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_700991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_700991 prefixEnd_700991 := by exact prefixLift 700991
  have htrace : WordTrace (prefixWord ++ tailWord_700991) baseStart_700991 baseEnd_700991 := by
    simpa [prefixWord, tailWord_700991, baseEnd_700991] using wordTrace_append hprefix tailTrace_700991
  have hstable : (prefixWord ++ tailWord_700991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_700991).length < 2 ^ (prefixWord ++ tailWord_700991).sum := by decide
  have hdescent : baseEnd_700991 < baseStart_700991 := by decide
  rcases family_descends (prefixWord ++ tailWord_700991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701025 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 4]
def baseStart_701025 : Nat := 118140960795 + 701025 * 2 ^ 59
def prefixEnd_701025 : Nat := 4983230072969 + 3 ^ 40 * 701025 * 2
def baseEnd_701025 : Nat := 159983455919211097850467

theorem tailTrace_701025 : CollatzResearch.WordTrace tailWord_701025 prefixEnd_701025 159983455919211097850467 := by
  unfold tailWord_701025
  simp only [CollatzResearch.WordTrace]
  refine ⟨25568482285313625383272529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17045654856875750255515019 25568482285313625383272529)
  ·
    refine ⟨19176361713985219037454397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25568482285313625383272529 19176361713985219037454397)
    ·
      refine ⟨7191135642744457139045399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19176361713985219037454397 7191135642744457139045399)
      ·
        refine ⟨10786703464116685708568099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7191135642744457139045399 10786703464116685708568099)
        ·
          refine ⟨16180055196175028562852149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10786703464116685708568099 16180055196175028562852149)
          ·
            refine ⟨1516880174641408927767389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16180055196175028562852149 1516880174641408927767389)
            ·
              refine ⟨568830065490528347912771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1516880174641408927767389 568830065490528347912771)
              ·
                refine ⟨853245098235792521869157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568830065490528347912771 853245098235792521869157)
                ·
                  refine ⟨159983455919211097850467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 853245098235792521869157 159983455919211097850467)
                  ·
                    rfl

theorem cell21_701025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_701025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701025 prefixEnd_701025 := by exact prefixLift 701025
  have htrace : WordTrace (prefixWord ++ tailWord_701025) baseStart_701025 baseEnd_701025 := by
    simpa [prefixWord, tailWord_701025, baseEnd_701025] using wordTrace_append hprefix tailTrace_701025
  have hstable : (prefixWord ++ tailWord_701025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701025).length < 2 ^ (prefixWord ++ tailWord_701025).sum := by decide
  have hdescent : baseEnd_701025 < baseStart_701025 := by decide
  rcases family_descends (prefixWord ++ tailWord_701025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701045 : List Nat := [1, 3, 4, 2, 3, 1, 1, 3, 3]
def baseStart_701045 : Nat := 118140960795 + 701045 * 2 ^ 59
def prefixEnd_701045 : Nat := 4983230072969 + 3 ^ 40 * 701045 * 2
def baseEnd_701045 : Nat := 159988020191695507517093

theorem tailTrace_701045 : CollatzResearch.WordTrace tailWord_701045 prefixEnd_701045 159988020191695507517093 := by
  unfold tailWord_701045
  simp only [CollatzResearch.WordTrace]
  refine ⟨25569211745241168799000589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17046141163494112532667059 25569211745241168799000589)
  ·
    refine ⟨9588454404465438299625221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25569211745241168799000589 9588454404465438299625221)
    ·
      refine ⟨1797835200837269681179729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9588454404465438299625221 1797835200837269681179729)
      ·
        refine ⟨1348376400627952260884797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1797835200837269681179729 1348376400627952260884797)
        ·
          refine ⟨505641150235482097831799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1348376400627952260884797 505641150235482097831799)
          ·
            refine ⟨758461725353223146747699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505641150235482097831799 758461725353223146747699)
            ·
              refine ⟨1137692588029834720121549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758461725353223146747699 1137692588029834720121549)
              ·
                refine ⟨426634720511188020045581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137692588029834720121549 426634720511188020045581)
                ·
                  refine ⟨159988020191695507517093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426634720511188020045581 159988020191695507517093)
                  ·
                    rfl

theorem cell21_701045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_701045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701045 prefixEnd_701045 := by exact prefixLift 701045
  have htrace : WordTrace (prefixWord ++ tailWord_701045) baseStart_701045 baseEnd_701045 := by
    simpa [prefixWord, tailWord_701045, baseEnd_701045] using wordTrace_append hprefix tailTrace_701045
  have hstable : (prefixWord ++ tailWord_701045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701045).length < 2 ^ (prefixWord ++ tailWord_701045).sum := by decide
  have hdescent : baseEnd_701045 < baseStart_701045 := by decide
  rcases family_descends (prefixWord ++ tailWord_701045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701174 : List Nat := [5, 1, 1, 1, 1, 2, 10]
def baseStart_701174 : Nat := 118140960795 + 701174 * 2 ^ 59
def prefixEnd_701174 : Nat := 4983230072969 + 3 ^ 40 * 701174 * 2
def baseEnd_701174 : Nat := 17779717749913327762981

theorem tailTrace_701174 : CollatzResearch.WordTrace tailWord_701174 prefixEnd_701174 17779717749913327762981 := by
  unfold tailWord_701174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1598369797610863989402911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17049277841182549220297717 1598369797610863989402911)
  ·
    refine ⟨2397554696416295984104367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1598369797610863989402911 2397554696416295984104367)
    ·
      refine ⟨3596332044624443976156551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397554696416295984104367 3596332044624443976156551)
      ·
        refine ⟨5394498066936665964234827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3596332044624443976156551 5394498066936665964234827)
        ·
          refine ⟨8091747100404998946352241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5394498066936665964234827 8091747100404998946352241)
          ·
            refine ⟨6068810325303749209764181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8091747100404998946352241 6068810325303749209764181)
            ·
              refine ⟨17779717749913327762981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6068810325303749209764181 17779717749913327762981)
              ·
                rfl

theorem cell21_701174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 10].length) (baseStart_701174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701174 prefixEnd_701174 := by exact prefixLift 701174
  have htrace : WordTrace (prefixWord ++ tailWord_701174) baseStart_701174 baseEnd_701174 := by
    simpa [prefixWord, tailWord_701174, baseEnd_701174] using wordTrace_append hprefix tailTrace_701174
  have hstable : (prefixWord ++ tailWord_701174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701174).length < 2 ^ (prefixWord ++ tailWord_701174).sum := by decide
  have hdescent : baseEnd_701174 < baseStart_701174 := by decide
  rcases family_descends (prefixWord ++ tailWord_701174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701264 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_701264 : Nat := 118140960795 + 701264 * 2 ^ 59
def prefixEnd_701264 : Nat := 4983230072969 + 3 ^ 40 * 701264 * 2
def baseEnd_701264 : Nat := 160037998975399793366645

theorem tailTrace_701264 : CollatzResearch.WordTrace tailWord_701264 prefixEnd_701264 160037998975399793366645 := by
  unfold tailWord_701264
  simp only [CollatzResearch.WordTrace]
  refine ⟨12788599665723884600611423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17051466220965179467481897 12788599665723884600611423)
  ·
    refine ⟨19182899498585826900917135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12788599665723884600611423 19182899498585826900917135)
    ·
      refine ⟨28774349247878740351375703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19182899498585826900917135 28774349247878740351375703)
      ·
        refine ⟨43161523871818110527063555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28774349247878740351375703 43161523871818110527063555)
        ·
          refine ⟨64742285807727165790595333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43161523871818110527063555 64742285807727165790595333)
          ·
            refine ⟨12139178588948843585736625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64742285807727165790595333 12139178588948843585736625)
            ·
              refine ⟨9104383941711632689302469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12139178588948843585736625 9104383941711632689302469)
              ·
                refine ⟨1707071989070931129244213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9104383941711632689302469 1707071989070931129244213)
                ·
                  refine ⟨160037998975399793366645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1707071989070931129244213 160037998975399793366645)
                  ·
                    rfl

theorem cell21_701264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_701264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701264 prefixEnd_701264 := by exact prefixLift 701264
  have htrace : WordTrace (prefixWord ++ tailWord_701264) baseStart_701264 baseEnd_701264 := by
    simpa [prefixWord, tailWord_701264, baseEnd_701264] using wordTrace_append hprefix tailTrace_701264
  have hstable : (prefixWord ++ tailWord_701264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701264).length < 2 ^ (prefixWord ++ tailWord_701264).sum := by decide
  have hdescent : baseEnd_701264 < baseStart_701264 := by decide
  rcases family_descends (prefixWord ++ tailWord_701264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701402 : List Nat := [3, 1, 1, 2, 4, 3, 7]
def baseStart_701402 : Nat := 118140960795 + 701402 * 2 ^ 59
def prefixEnd_701402 : Nat := 4983230072969 + 3 ^ 40 * 701402 * 2
def baseEnd_701402 : Nat := 17785499161726913340707

theorem tailTrace_701402 : CollatzResearch.WordTrace tailWord_701402 prefixEnd_701402 17785499161726913340707 := by
  unfold tailWord_701402
  simp only [CollatzResearch.WordTrace]
  refine ⟨6395558151236954692436615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17054821736631879179830973 6395558151236954692436615)
  ·
    refine ⟨9593337226855432038654923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6395558151236954692436615 9593337226855432038654923)
    ·
      refine ⟨14390005840283148057982385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9593337226855432038654923 14390005840283148057982385)
      ·
        refine ⟨10792504380212361043486789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14390005840283148057982385 10792504380212361043486789)
        ·
          refine ⟨2023594571289817695653773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10792504380212361043486789 2023594571289817695653773)
          ·
            refine ⟨758847964233681635870165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2023594571289817695653773 758847964233681635870165)
            ·
              refine ⟨17785499161726913340707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 758847964233681635870165 17785499161726913340707)
              ·
                rfl

theorem cell21_701402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 7].length) (baseStart_701402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701402 prefixEnd_701402 := by exact prefixLift 701402
  have htrace : WordTrace (prefixWord ++ tailWord_701402) baseStart_701402 baseEnd_701402 := by
    simpa [prefixWord, tailWord_701402, baseEnd_701402] using wordTrace_append hprefix tailTrace_701402
  have hstable : (prefixWord ++ tailWord_701402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701402).length < 2 ^ (prefixWord ++ tailWord_701402).sum := by decide
  have hdescent : baseEnd_701402 < baseStart_701402 := by decide
  rcases family_descends (prefixWord ++ tailWord_701402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701422 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_701422 : Nat := 118140960795 + 701422 * 2 ^ 59
def prefixEnd_701422 : Nat := 4983230072969 + 3 ^ 40 * 701422 * 2
def baseEnd_701422 : Nat := 160074056728026629732989

theorem tailTrace_701422 : CollatzResearch.WordTrace tailWord_701422 prefixEnd_701422 160074056728026629732989 := by
  unfold tailWord_701422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197870258109420273184315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17055308043250241456983013 3197870258109420273184315)
  ·
    refine ⟨4796805387164130409776473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3197870258109420273184315 4796805387164130409776473)
    ·
      refine ⟨3597604040373097807332355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4796805387164130409776473 3597604040373097807332355)
      ·
        refine ⟨5396406060559646710998533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3597604040373097807332355 5396406060559646710998533)
        ·
          refine ⟨1011826136354933758312225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5396406060559646710998533 1011826136354933758312225)
          ·
            refine ⟨758869602266200318734169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1011826136354933758312225 758869602266200318734169)
            ·
              refine ⟨569152201699650239050627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 758869602266200318734169 569152201699650239050627)
              ·
                refine ⟨853728302549475358575941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569152201699650239050627 853728302549475358575941)
                ·
                  refine ⟨160074056728026629732989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 853728302549475358575941 160074056728026629732989)
                  ·
                    rfl

theorem cell21_701422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_701422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701422 prefixEnd_701422 := by exact prefixLift 701422
  have htrace : WordTrace (prefixWord ++ tailWord_701422) baseStart_701422 baseEnd_701422 := by
    simpa [prefixWord, tailWord_701422, baseEnd_701422] using wordTrace_append hprefix tailTrace_701422
  have hstable : (prefixWord ++ tailWord_701422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701422).length < 2 ^ (prefixWord ++ tailWord_701422).sum := by decide
  have hdescent : baseEnd_701422 < baseStart_701422 := by decide
  rcases family_descends (prefixWord ++ tailWord_701422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701461 : List Nat := [1, 3, 2, 1, 4, 10]
def baseStart_701461 : Nat := 118140960795 + 701461 * 2 ^ 59
def prefixEnd_701461 : Nat := 4983230072969 + 3 ^ 40 * 701461 * 2
def baseEnd_701461 : Nat := 5928998409606341799367

theorem tailTrace_701461 : CollatzResearch.WordTrace tailWord_701461 prefixEnd_701461 5928998409606341799367 := by
  unfold tailWord_701461
  simp only [CollatzResearch.WordTrace]
  refine ⟨25584384511734071846144237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17056256341156047897429491 25584384511734071846144237)
  ·
    refine ⟨9594144191900276942304089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25584384511734071846144237 9594144191900276942304089)
    ·
      refine ⟨7195608143925207706728067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9594144191900276942304089 7195608143925207706728067)
      ·
        refine ⟨10793412215887811560092101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7195608143925207706728067 10793412215887811560092101)
        ·
          refine ⟨2023764790478964667517269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10793412215887811560092101 2023764790478964667517269)
          ·
            refine ⟨5928998409606341799367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2023764790478964667517269 5928998409606341799367)
            ·
              rfl

theorem cell21_701461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 10].length) (baseStart_701461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701461 prefixEnd_701461 := by exact prefixLift 701461
  have htrace : WordTrace (prefixWord ++ tailWord_701461) baseStart_701461 baseEnd_701461 := by
    simpa [prefixWord, tailWord_701461, baseEnd_701461] using wordTrace_append hprefix tailTrace_701461
  have hstable : (prefixWord ++ tailWord_701461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701461).length < 2 ^ (prefixWord ++ tailWord_701461).sum := by decide
  have hdescent : baseEnd_701461 < baseStart_701461 := by decide
  rcases family_descends (prefixWord ++ tailWord_701461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701464 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 4]
def baseStart_701464 : Nat := 118140960795 + 701464 * 2 ^ 59
def prefixEnd_701464 : Nat := 4983230072969 + 3 ^ 40 * 701464 * 2
def baseEnd_701464 : Nat := 160083641700243890032903

theorem tailTrace_701464 : CollatzResearch.WordTrace tailWord_701464 prefixEnd_701464 160083641700243890032903 := by
  unfold tailWord_701464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12792246965361601679251723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17056329287148802239002297 12792246965361601679251723)
  ·
    refine ⟨19188370448042402518877585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12792246965361601679251723 19188370448042402518877585)
    ·
      refine ⟨14391277836031801889158189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19188370448042402518877585 14391277836031801889158189)
      ·
        refine ⟨5396729188511925708434321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14391277836031801889158189 5396729188511925708434321)
        ·
          refine ⟨4047546891383944281325741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5396729188511925708434321 4047546891383944281325741)
          ·
            refine ⟨1517830084268979105497153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4047546891383944281325741 1517830084268979105497153)
            ·
              refine ⟨1138372563201734329122865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517830084268979105497153 1138372563201734329122865)
              ·
                refine ⟨853779422401300746842149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138372563201734329122865 853779422401300746842149)
                ·
                  refine ⟨160083641700243890032903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 853779422401300746842149 160083641700243890032903)
                  ·
                    rfl

theorem cell21_701464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_701464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701464 prefixEnd_701464 := by exact prefixLift 701464
  have htrace : WordTrace (prefixWord ++ tailWord_701464) baseStart_701464 baseEnd_701464 := by
    simpa [prefixWord, tailWord_701464, baseEnd_701464] using wordTrace_append hprefix tailTrace_701464
  have hstable : (prefixWord ++ tailWord_701464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701464).length < 2 ^ (prefixWord ++ tailWord_701464).sum := by decide
  have hdescent : baseEnd_701464 < baseStart_701464 := by decide
  rcases family_descends (prefixWord ++ tailWord_701464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701509 : List Nat := [1, 3, 1, 1, 1, 3, 3, 5, 3]
def baseStart_701509 : Nat := 118140960795 + 701509 * 2 ^ 59
def prefixEnd_701509 : Nat := 4983230072969 + 3 ^ 40 * 701509 * 2
def baseEnd_701509 : Nat := 160093911313333811782811

theorem tailTrace_701509 : CollatzResearch.WordTrace tailWord_701509 prefixEnd_701509 160093911313333811782811 := by
  unfold tailWord_701509
  simp only [CollatzResearch.WordTrace]
  refine ⟨25586135215560176043891581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17057423477040117362594387 25586135215560176043891581)
  ·
    refine ⟨9594800705835066016459343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25586135215560176043891581 9594800705835066016459343)
    ·
      refine ⟨14392201058752599024689015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9594800705835066016459343 14392201058752599024689015)
      ·
        refine ⟨21588301588128898537033523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14392201058752599024689015 21588301588128898537033523)
        ·
          refine ⟨32382452382193347805550285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21588301588128898537033523 32382452382193347805550285)
          ·
            refine ⟨12143419643322505427081357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32382452382193347805550285 12143419643322505427081357)
            ·
              refine ⟨4553782366245939535155509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12143419643322505427081357 4553782366245939535155509)
              ·
                refine ⟨426917096835556831420829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4553782366245939535155509 426917096835556831420829)
                ·
                  refine ⟨160093911313333811782811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426917096835556831420829 160093911313333811782811)
                  ·
                    rfl

theorem cell21_701509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_701509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701509 prefixEnd_701509 := by exact prefixLift 701509
  have htrace : WordTrace (prefixWord ++ tailWord_701509) baseStart_701509 baseEnd_701509 := by
    simpa [prefixWord, tailWord_701509, baseEnd_701509] using wordTrace_append hprefix tailTrace_701509
  have hstable : (prefixWord ++ tailWord_701509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701509).length < 2 ^ (prefixWord ++ tailWord_701509).sum := by decide
  have hdescent : baseEnd_701509 < baseStart_701509 := by decide
  rcases family_descends (prefixWord ++ tailWord_701509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701627 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 9]
def baseStart_701627 : Nat := 118140960795 + 701627 * 2 ^ 59
def prefixEnd_701627 : Nat := 4983230072969 + 3 ^ 40 * 701627 * 2
def baseEnd_701627 : Nat := 160120840520991828815903

theorem tailTrace_701627 : CollatzResearch.WordTrace tailWord_701627 prefixEnd_701627 160120840520991828815903 := by
  unfold tailWord_701627
  simp only [CollatzResearch.WordTrace]
  refine ⟨25590439029132682196687135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17060292686088454797791423 25590439029132682196687135)
  ·
    refine ⟨38385658543699023295030703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25590439029132682196687135 38385658543699023295030703)
    ·
      refine ⟨57578487815548534942546055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38385658543699023295030703 57578487815548534942546055)
      ·
        refine ⟨86367731723322802413819083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57578487815548534942546055 86367731723322802413819083)
        ·
          refine ⟨129551597584984203620728625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86367731723322802413819083 129551597584984203620728625)
          ·
            refine ⟨97163698188738152715546469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129551597584984203620728625 97163698188738152715546469)
            ·
              refine ⟨18218193410388403634164963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97163698188738152715546469 18218193410388403634164963)
              ·
                refine ⟨27327290115582605451247445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18218193410388403634164963 27327290115582605451247445)
                ·
                  refine ⟨160120840520991828815903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27327290115582605451247445 160120840520991828815903)
                  ·
                    rfl

theorem cell21_701627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_701627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701627 prefixEnd_701627 := by exact prefixLift 701627
  have htrace : WordTrace (prefixWord ++ tailWord_701627) baseStart_701627 baseEnd_701627 := by
    simpa [prefixWord, tailWord_701627, baseEnd_701627] using wordTrace_append hprefix tailTrace_701627
  have hstable : (prefixWord ++ tailWord_701627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701627).length < 2 ^ (prefixWord ++ tailWord_701627).sum := by decide
  have hdescent : baseEnd_701627 < baseStart_701627 := by decide
  rcases family_descends (prefixWord ++ tailWord_701627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701633 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 4]
def baseStart_701633 : Nat := 118140960795 + 701633 * 2 ^ 59
def prefixEnd_701633 : Nat := 4983230072969 + 3 ^ 40 * 701633 * 2
def baseEnd_701633 : Nat := 160122209802737151715891

theorem tailTrace_701633 : CollatzResearch.WordTrace tailWord_701633 prefixEnd_701633 160122209802737151715891 := by
  unfold tailWord_701633
  simp only [CollatzResearch.WordTrace]
  refine ⟨25590657867110945221405553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17060438578073963480937035 25590657867110945221405553)
  ·
    refine ⟨19192993400333208916054165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25590657867110945221405553 19192993400333208916054165)
    ·
      refine ⟨899671565640619167940039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19192993400333208916054165 899671565640619167940039)
      ·
        refine ⟨1349507348460928751910059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899671565640619167940039 1349507348460928751910059)
        ·
          refine ⟨2024261022691393127865089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349507348460928751910059 2024261022691393127865089)
          ·
            refine ⟨1518195767018544845898817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2024261022691393127865089 1518195767018544845898817)
            ·
              refine ⟨1138646825263908634424113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518195767018544845898817 1138646825263908634424113)
              ·
                refine ⟨853985118947931475818085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138646825263908634424113 853985118947931475818085)
                ·
                  refine ⟨160122209802737151715891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 853985118947931475818085 160122209802737151715891)
                  ·
                    rfl

theorem cell21_701633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_701633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701633 prefixEnd_701633 := by exact prefixLift 701633
  have htrace : WordTrace (prefixWord ++ tailWord_701633) baseStart_701633 baseEnd_701633 := by
    simpa [prefixWord, tailWord_701633, baseEnd_701633] using wordTrace_append hprefix tailTrace_701633
  have hstable : (prefixWord ++ tailWord_701633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701633).length < 2 ^ (prefixWord ++ tailWord_701633).sum := by decide
  have hdescent : baseEnd_701633 < baseStart_701633 := by decide
  rcases family_descends (prefixWord ++ tailWord_701633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701636 : List Nat := [2, 3, 3, 1, 3, 2, 2, 2, 3]
def baseStart_701636 : Nat := 118140960795 + 701636 * 2 ^ 59
def prefixEnd_701636 : Nat := 4983230072969 + 3 ^ 40 * 701636 * 2
def baseEnd_701636 : Nat := 160122894443609813165885

theorem tailTrace_701636 : CollatzResearch.WordTrace tailWord_701636 prefixEnd_701636 160122894443609813165885 := by
  unfold tailWord_701636
  simp only [CollatzResearch.WordTrace]
  refine ⟨12795383643050038366882381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17060511524066717822509841 12795383643050038366882381)
  ·
    refine ⟨4798268866143764387580893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12795383643050038366882381 4798268866143764387580893)
    ·
      refine ⟨1799350824803911645342835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4798268866143764387580893 1799350824803911645342835)
      ·
        refine ⟨2699026237205867468014253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799350824803911645342835 2699026237205867468014253)
        ·
          refine ⟨1012134838952200300505345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2699026237205867468014253 1012134838952200300505345)
          ·
            refine ⟨759101129214150225379009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1012134838952200300505345 759101129214150225379009)
            ·
              refine ⟨569325846910612669034257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759101129214150225379009 569325846910612669034257)
              ·
                refine ⟨426994385182959501775693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569325846910612669034257 426994385182959501775693)
                ·
                  refine ⟨160122894443609813165885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426994385182959501775693 160122894443609813165885)
                  ·
                    rfl

theorem cell21_701636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_701636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701636 prefixEnd_701636 := by exact prefixLift 701636
  have htrace : WordTrace (prefixWord ++ tailWord_701636) baseStart_701636 baseEnd_701636 := by
    simpa [prefixWord, tailWord_701636, baseEnd_701636] using wordTrace_append hprefix tailTrace_701636
  have hstable : (prefixWord ++ tailWord_701636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701636).length < 2 ^ (prefixWord ++ tailWord_701636).sum := by decide
  have hdescent : baseEnd_701636 < baseStart_701636 := by decide
  rcases family_descends (prefixWord ++ tailWord_701636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701658 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_701658 : Nat := 118140960795 + 701658 * 2 ^ 59
def prefixEnd_701658 : Nat := 4983230072969 + 3 ^ 40 * 701658 * 2
def baseEnd_701658 : Nat := 160127915143342663799173

theorem tailTrace_701658 : CollatzResearch.WordTrace tailWord_701658 prefixEnd_701658 160127915143342663799173 := by
  unfold tailWord_701658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6397892423005093622766407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17061046461346916327377085 6397892423005093622766407)
  ·
    refine ⟨9596838634507640434149611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6397892423005093622766407 9596838634507640434149611)
    ·
      refine ⟨14395257951761460651224417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9596838634507640434149611 14395257951761460651224417)
      ·
        refine ⟨10796443463821095488418313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14395257951761460651224417 10796443463821095488418313)
        ·
          refine ⟨8097332597865821616313735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10796443463821095488418313 8097332597865821616313735)
          ·
            refine ⟨12145998896798732424470603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8097332597865821616313735 12145998896798732424470603)
            ·
              refine ⟨18218998345198098636705905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12145998896798732424470603 18218998345198098636705905)
              ·
                refine ⟨13664248758898573977529429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18218998345198098636705905 13664248758898573977529429)
                ·
                  refine ⟨160127915143342663799173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13664248758898573977529429 160127915143342663799173)
                  ·
                    rfl

theorem cell21_701658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_701658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701658 prefixEnd_701658 := by exact prefixLift 701658
  have htrace : WordTrace (prefixWord ++ tailWord_701658) baseStart_701658 baseEnd_701658 := by
    simpa [prefixWord, tailWord_701658, baseEnd_701658] using wordTrace_append hprefix tailTrace_701658
  have hstable : (prefixWord ++ tailWord_701658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701658).length < 2 ^ (prefixWord ++ tailWord_701658).sum := by decide
  have hdescent : baseEnd_701658 < baseStart_701658 := by decide
  rcases family_descends (prefixWord ++ tailWord_701658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701684 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 4]
def baseStart_701684 : Nat := 118140960795 + 701684 * 2 ^ 59
def prefixEnd_701684 : Nat := 4983230072969 + 3 ^ 40 * 701684 * 2
def baseEnd_701684 : Nat := 160133848697572396365787

theorem tailTrace_701684 : CollatzResearch.WordTrace tailWord_701684 prefixEnd_701684 160133848697572396365787 := by
  unfold tailWord_701684
  simp only [CollatzResearch.WordTrace]
  refine ⟨12796258994963090465756053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17061678659950787287674737 12796258994963090465756053)
  ·
    refine ⟨599824640388894865582315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12796258994963090465756053 599824640388894865582315)
    ·
      refine ⟨899736960583342298373473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 599824640388894865582315 899736960583342298373473)
      ·
        refine ⟨674802720437506723780105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 899736960583342298373473 674802720437506723780105)
        ·
          refine ⟨506102040328130042835079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674802720437506723780105 506102040328130042835079)
          ·
            refine ⟨759153060492195064252619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506102040328130042835079 759153060492195064252619)
            ·
              refine ⟨1138729590738292596378929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759153060492195064252619 1138729590738292596378929)
              ·
                refine ⟨854047193053719447284197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138729590738292596378929 854047193053719447284197)
                ·
                  refine ⟨160133848697572396365787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 854047193053719447284197 160133848697572396365787)
                  ·
                    rfl

theorem cell21_701684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_701684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701684 prefixEnd_701684 := by exact prefixLift 701684
  have htrace : WordTrace (prefixWord ++ tailWord_701684) baseStart_701684 baseEnd_701684 := by
    simpa [prefixWord, tailWord_701684, baseEnd_701684] using wordTrace_append hprefix tailTrace_701684
  have hstable : (prefixWord ++ tailWord_701684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701684).length < 2 ^ (prefixWord ++ tailWord_701684).sum := by decide
  have hdescent : baseEnd_701684 < baseStart_701684 := by decide
  rcases family_descends (prefixWord ++ tailWord_701684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701720 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_701720 : Nat := 118140960795 + 701720 * 2 ^ 59
def prefixEnd_701720 : Nat := 4983230072969 + 3 ^ 40 * 701720 * 2
def baseEnd_701720 : Nat := 160142064388044333765713

theorem tailTrace_701720 : CollatzResearch.WordTrace tailWord_701720 prefixEnd_701720 160142064388044333765713 := by
  unfold tailWord_701720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12796915508897879539911307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17062554011863839386548409 12796915508897879539911307)
  ·
    refine ⟨19195373263346819309866961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12796915508897879539911307 19195373263346819309866961)
    ·
      refine ⟨14396529947510114482400221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19195373263346819309866961 14396529947510114482400221)
      ·
        refine ⟨5398698730316292930900083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14396529947510114482400221 5398698730316292930900083)
        ·
          refine ⟨8098048095474439396350125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5398698730316292930900083 8098048095474439396350125)
          ·
            refine ⟨3036768035802914773631297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8098048095474439396350125 3036768035802914773631297)
            ·
              refine ⟨2277576026852186080223473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3036768035802914773631297 2277576026852186080223473)
              ·
                refine ⟨1708182020139139560167605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277576026852186080223473 1708182020139139560167605)
                ·
                  refine ⟨160142064388044333765713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1708182020139139560167605 160142064388044333765713)
                  ·
                    rfl

theorem cell21_701720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_701720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701720 prefixEnd_701720 := by exact prefixLift 701720
  have htrace : WordTrace (prefixWord ++ tailWord_701720) baseStart_701720 baseEnd_701720 := by
    simpa [prefixWord, tailWord_701720, baseEnd_701720] using wordTrace_append hprefix tailTrace_701720
  have hstable : (prefixWord ++ tailWord_701720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701720).length < 2 ^ (prefixWord ++ tailWord_701720).sum := by decide
  have hdescent : baseEnd_701720 < baseStart_701720 := by decide
  rcases family_descends (prefixWord ++ tailWord_701720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701754 : List Nat := [3, 1, 1, 1, 4, 1, 5, 2, 3]
def baseStart_701754 : Nat := 118140960795 + 701754 * 2 ^ 59
def prefixEnd_701754 : Nat := 4983230072969 + 3 ^ 40 * 701754 * 2
def baseEnd_701754 : Nat := 160149823651267830198977

theorem tailTrace_701754 : CollatzResearch.WordTrace tailWord_701754 prefixEnd_701754 160149823651267830198977 := by
  unfold tailWord_701754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6398767774918145721640079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17063380733115055257706877 6398767774918145721640079)
  ·
    refine ⟨9598151662377218582460119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6398767774918145721640079 9598151662377218582460119)
    ·
      refine ⟨14397227493565827873690179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9598151662377218582460119 14397227493565827873690179)
      ·
        refine ⟨21595841240348741810535269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14397227493565827873690179 21595841240348741810535269)
        ·
          refine ⟨4049220232565389089475363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21595841240348741810535269 4049220232565389089475363)
          ·
            refine ⟨6073830348848083634213045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4049220232565389089475363 6073830348848083634213045)
            ·
              refine ⟨569421595204507840707473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6073830348848083634213045 569421595204507840707473)
              ·
                refine ⟨427066196403380880530605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569421595204507840707473 427066196403380880530605)
                ·
                  refine ⟨160149823651267830198977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427066196403380880530605 160149823651267830198977)
                  ·
                    rfl

theorem cell21_701754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_701754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701754 prefixEnd_701754 := by exact prefixLift 701754
  have htrace : WordTrace (prefixWord ++ tailWord_701754) baseStart_701754 baseEnd_701754 := by
    simpa [prefixWord, tailWord_701754, baseEnd_701754] using wordTrace_append hprefix tailTrace_701754
  have hstable : (prefixWord ++ tailWord_701754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701754).length < 2 ^ (prefixWord ++ tailWord_701754).sum := by decide
  have hdescent : baseEnd_701754 < baseStart_701754 := by decide
  rcases family_descends (prefixWord ++ tailWord_701754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701779 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 7]
def baseStart_701779 : Nat := 118140960795 + 701779 * 2 ^ 59
def prefixEnd_701779 : Nat := 4983230072969 + 3 ^ 40 * 701779 * 2
def baseEnd_701779 : Nat := 160155528991873342282259

theorem tailTrace_701779 : CollatzResearch.WordTrace tailWord_701779 prefixEnd_701779 160155528991873342282259 := by
  unfold tailWord_701779
  simp only [CollatzResearch.WordTrace]
  refine ⟨25595982924582012156220391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17063988616388008104146927 25595982924582012156220391)
  ·
    refine ⟨38393974386873018234330587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25595982924582012156220391 38393974386873018234330587)
    ·
      refine ⟨57590961580309527351495881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38393974386873018234330587 57590961580309527351495881)
      ·
        refine ⟨43193221185232145513621911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57590961580309527351495881 43193221185232145513621911)
        ·
          refine ⟨64789831777848218270432867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43193221185232145513621911 64789831777848218270432867)
          ·
            refine ⟨97184747666772327405649301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64789831777848218270432867 97184747666772327405649301)
            ·
              refine ⟨4555535046879952847139811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97184747666772327405649301 4555535046879952847139811)
              ·
                refine ⟨6833302570319929270709717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555535046879952847139811 6833302570319929270709717)
                ·
                  refine ⟨160155528991873342282259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6833302570319929270709717 160155528991873342282259)
                  ·
                    rfl

theorem cell21_701779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_701779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701779 prefixEnd_701779 := by exact prefixLift 701779
  have htrace : WordTrace (prefixWord ++ tailWord_701779) baseStart_701779 baseEnd_701779 := by
    simpa [prefixWord, tailWord_701779, baseEnd_701779] using wordTrace_append hprefix tailTrace_701779
  have hstable : (prefixWord ++ tailWord_701779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701779).length < 2 ^ (prefixWord ++ tailWord_701779).sum := by decide
  have hdescent : baseEnd_701779 < baseStart_701779 := by decide
  rcases family_descends (prefixWord ++ tailWord_701779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701827 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 4]
def baseStart_701827 : Nat := 118140960795 + 701827 * 2 ^ 59
def prefixEnd_701827 : Nat := 4983230072969 + 3 ^ 40 * 701827 * 2
def baseEnd_701827 : Nat := 160166483245835925482161

theorem tailTrace_701827 : CollatzResearch.WordTrace tailWord_701827 prefixEnd_701827 160166483245835925482161 := by
  unfold tailWord_701827
  simp only [CollatzResearch.WordTrace]
  refine ⟨25597733628408116353967735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17065155752272077569311823 25597733628408116353967735)
  ·
    refine ⟨38396600442612174530951603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25597733628408116353967735 38396600442612174530951603)
    ·
      refine ⟨57594900663918261796427405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38396600442612174530951603 57594900663918261796427405)
      ·
        refine ⟨21598087748969348173660277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57594900663918261796427405 21598087748969348173660277)
        ·
          refine ⟨2024820726465876391280651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21598087748969348173660277 2024820726465876391280651)
          ·
            refine ⟨3037231089698814586920977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024820726465876391280651 3037231089698814586920977)
            ·
              refine ⟨2277923317274110940190733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037231089698814586920977 2277923317274110940190733)
              ·
                refine ⟨854221243977791602571525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2277923317274110940190733 854221243977791602571525)
                ·
                  refine ⟨160166483245835925482161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 854221243977791602571525 160166483245835925482161)
                  ·
                    rfl

theorem cell21_701827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 4].length) (baseStart_701827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701827 prefixEnd_701827 := by exact prefixLift 701827
  have htrace : WordTrace (prefixWord ++ tailWord_701827) baseStart_701827 baseEnd_701827 := by
    simpa [prefixWord, tailWord_701827, baseEnd_701827] using wordTrace_append hprefix tailTrace_701827
  have hstable : (prefixWord ++ tailWord_701827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701827).length < 2 ^ (prefixWord ++ tailWord_701827).sum := by decide
  have hdescent : baseEnd_701827 < baseStart_701827 := by decide
  rcases family_descends (prefixWord ++ tailWord_701827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701917 : List Nat := [1, 4, 3, 1, 1, 2, 9]
def baseStart_701917 : Nat := 118140960795 + 701917 * 2 ^ 59
def prefixEnd_701917 : Nat := 4983230072969 + 3 ^ 40 * 701917 * 2
def baseEnd_701917 : Nat := 17798558052446196553553

theorem tailTrace_701917 : CollatzResearch.WordTrace tailWord_701917 prefixEnd_701917 17798558052446196553553 := by
  unfold tailWord_701917
  simp only [CollatzResearch.WordTrace]
  refine ⟨25601016198082061724744005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17067344132054707816496003 25601016198082061724744005)
  ·
    refine ⟨4800190537140386573389501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25601016198082061724744005 4800190537140386573389501)
    ·
      refine ⟨1800071451427644965021063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4800190537140386573389501 1800071451427644965021063)
      ·
        refine ⟨2700107177141467447531595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800071451427644965021063 2700107177141467447531595)
        ·
          refine ⟨4050160765712201171297393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700107177141467447531595 4050160765712201171297393)
          ·
            refine ⟨3037620574284150878473045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4050160765712201171297393 3037620574284150878473045)
            ·
              refine ⟨17798558052446196553553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3037620574284150878473045 17798558052446196553553)
              ·
                rfl

theorem cell21_701917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 9].length) (baseStart_701917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701917 prefixEnd_701917 := by exact prefixLift 701917
  have htrace : WordTrace (prefixWord ++ tailWord_701917) baseStart_701917 baseEnd_701917 := by
    simpa [prefixWord, tailWord_701917, baseEnd_701917] using wordTrace_append hprefix tailTrace_701917
  have hstable : (prefixWord ++ tailWord_701917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701917).length < 2 ^ (prefixWord ++ tailWord_701917).sum := by decide
  have hdescent : baseEnd_701917 < baseStart_701917 := by decide
  rcases family_descends (prefixWord ++ tailWord_701917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701931 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 5]
def baseStart_701931 : Nat := 118140960795 + 701931 * 2 ^ 59
def prefixEnd_701931 : Nat := 4983230072969 + 3 ^ 40 * 701931 * 2
def baseEnd_701931 : Nat := 160190217462754855748615

theorem tailTrace_701931 : CollatzResearch.WordTrace tailWord_701931 prefixEnd_701931 160190217462754855748615 := by
  unfold tailWord_701931
  simp only [CollatzResearch.WordTrace]
  refine ⟨25601526820031342115753647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17067684546687561410502431 25601526820031342115753647)
  ·
    refine ⟨38402290230047013173630471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25601526820031342115753647 38402290230047013173630471)
    ·
      refine ⟨57603435345070519760445707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38402290230047013173630471 57603435345070519760445707)
      ·
        refine ⟨86405153017605779640668561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57603435345070519760445707 86405153017605779640668561)
        ·
          refine ⟨64803864763204334730501421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86405153017605779640668561 64803864763204334730501421)
          ·
            refine ⟨24301449286201625523938033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64803864763204334730501421 24301449286201625523938033)
            ·
              refine ⟨18226086964651219142953525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24301449286201625523938033 18226086964651219142953525)
              ·
                refine ⟨1708695652936051794651893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18226086964651219142953525 1708695652936051794651893)
                ·
                  refine ⟨160190217462754855748615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1708695652936051794651893 160190217462754855748615)
                  ·
                    rfl

theorem cell21_701931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_701931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701931 prefixEnd_701931 := by exact prefixLift 701931
  have htrace : WordTrace (prefixWord ++ tailWord_701931) baseStart_701931 baseEnd_701931 := by
    simpa [prefixWord, tailWord_701931, baseEnd_701931] using wordTrace_append hprefix tailTrace_701931
  have hstable : (prefixWord ++ tailWord_701931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701931).length < 2 ^ (prefixWord ++ tailWord_701931).sum := by decide
  have hdescent : baseEnd_701931 < baseStart_701931 := by decide
  rcases family_descends (prefixWord ++ tailWord_701931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_701976 : List Nat := [2, 1, 2, 3, 13]
def baseStart_701976 : Nat := 118140960795 + 701976 * 2 ^ 59
def prefixEnd_701976 : Nat := 4983230072969 + 3 ^ 40 * 701976 * 2
def baseEnd_701976 : Nat := 1977783791059812067883

theorem tailTrace_701976 : CollatzResearch.WordTrace tailWord_701976 prefixEnd_701976 1977783791059812067883 := by
  unfold tailWord_701976
  simp only [CollatzResearch.WordTrace]
  refine ⟨12801584052434157400570891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17068778736578876534094521 12801584052434157400570891)
  ·
    refine ⟨19202376078651236100856337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12801584052434157400570891 19202376078651236100856337)
    ·
      refine ⟨14401782058988427075642253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19202376078651236100856337 14401782058988427075642253)
      ·
        refine ⟨5400668272120660153365845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14401782058988427075642253 5400668272120660153365845)
        ·
          refine ⟨1977783791059812067883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 5400668272120660153365845 1977783791059812067883)
          ·
            rfl

theorem cell21_701976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 13].length) (baseStart_701976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_701976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_701976 prefixEnd_701976 := by exact prefixLift 701976
  have htrace : WordTrace (prefixWord ++ tailWord_701976) baseStart_701976 baseEnd_701976 := by
    simpa [prefixWord, tailWord_701976, baseEnd_701976] using wordTrace_append hprefix tailTrace_701976
  have hstable : (prefixWord ++ tailWord_701976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_701976).length < 2 ^ (prefixWord ++ tailWord_701976).sum := by decide
  have hdescent : baseEnd_701976 < baseStart_701976 := by decide
  rcases family_descends (prefixWord ++ tailWord_701976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
