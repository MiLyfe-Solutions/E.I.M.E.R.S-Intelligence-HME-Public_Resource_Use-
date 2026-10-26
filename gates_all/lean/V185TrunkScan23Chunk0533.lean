import V185TrunkScan23Chunk0532

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3151298 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3151298 : Nat := 118140960795 + 3151298 * 2 ^ 59
def prefixEnd_3151298 : Nat := 4983230072969 + 3 ^ 40 * 3151298 * 2
def baseEnd_3151298 : Nat := 1618130559552316765782451

theorem tailTrace_3151298 : CollatzResearch.WordTrace tailWord_3151298 prefixEnd_3151298 1618130559552316765782451 := by
  unfold tailWord_3151298
  simp only [CollatzResearch.WordTrace]
  refine ⟨28734320134348254923827637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76624853691595346463540365 28734320134348254923827637)
  ·
    refine ⟨2693842512595148899108841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28734320134348254923827637 2693842512595148899108841)
    ·
      refine ⟨2020381884446361674331631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2693842512595148899108841 2020381884446361674331631)
      ·
        refine ⟨3030572826669542511497447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020381884446361674331631 3030572826669542511497447)
        ·
          refine ⟨4545859240004313767246171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030572826669542511497447 4545859240004313767246171)
          ·
            refine ⟨6818788860006470650869257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4545859240004313767246171 6818788860006470650869257)
            ·
              refine ⟨5114091645004852988151943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6818788860006470650869257 5114091645004852988151943)
              ·
                refine ⟨7671137467507279482227915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5114091645004852988151943 7671137467507279482227915)
                ·
                  refine ⟨11506706201260919223341873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7671137467507279482227915 11506706201260919223341873)
                  ·
                    refine ⟨8630029650945689417506405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11506706201260919223341873 8630029650945689417506405)
                    ·
                      refine ⟨1618130559552316765782451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8630029650945689417506405 1618130559552316765782451)
                      ·
                        rfl

theorem cell23_3151298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3151298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151298 prefixEnd_3151298 := by exact prefixLift 3151298
  have htrace : WordTrace (prefixWord ++ tailWord_3151298) baseStart_3151298 baseEnd_3151298 := by
    simpa [prefixWord, tailWord_3151298, baseEnd_3151298] using wordTrace_append hprefix tailTrace_3151298
  have hstable : (prefixWord ++ tailWord_3151298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151298).length < 2 ^ (prefixWord ++ tailWord_3151298).sum := by decide
  have hdescent : baseEnd_3151298 < baseStart_3151298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151300 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3151300 : Nat := 118140960795 + 3151300 * 2 ^ 59
def prefixEnd_3151300 : Nat := 4983230072969 + 3 ^ 40 * 3151300 * 2
def baseEnd_3151300 : Nat := 539377195504541919319147

theorem tailTrace_3151300 : CollatzResearch.WordTrace tailWord_3151300 prefixEnd_3151300 539377195504541919319147 := by
  unfold tailWord_3151300
  simp only [CollatzResearch.WordTrace]
  refine ⟨57468676741692887018441677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76624902322257182691255569 57468676741692887018441677)
  ·
    refine ⟨21550753778134832631915629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57468676741692887018441677 21550753778134832631915629)
    ·
      refine ⟨8081532666800562236968361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21550753778134832631915629 8081532666800562236968361)
      ·
        refine ⟨6061149500100421677726271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8081532666800562236968361 6061149500100421677726271)
        ·
          refine ⟨9091724250150632516589407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061149500100421677726271 9091724250150632516589407)
          ·
            refine ⟨13637586375225948774884111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9091724250150632516589407 13637586375225948774884111)
            ·
              refine ⟨20456379562838923162326167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13637586375225948774884111 20456379562838923162326167)
              ·
                refine ⟨30684569344258384743489251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20456379562838923162326167 30684569344258384743489251)
                ·
                  refine ⟨46026854016387577115233877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30684569344258384743489251 46026854016387577115233877)
                  ·
                    refine ⟨539377195504541919319147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46026854016387577115233877 539377195504541919319147)
                    ·
                      rfl

theorem cell23_3151300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3151300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151300 prefixEnd_3151300 := by exact prefixLift 3151300
  have htrace : WordTrace (prefixWord ++ tailWord_3151300) baseStart_3151300 baseEnd_3151300 := by
    simpa [prefixWord, tailWord_3151300, baseEnd_3151300] using wordTrace_append hprefix tailTrace_3151300
  have hstable : (prefixWord ++ tailWord_3151300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151300).length < 2 ^ (prefixWord ++ tailWord_3151300).sum := by decide
  have hdescent : baseEnd_3151300 < baseStart_3151300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151341 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_3151341 : Nat := 118140960795 + 3151341 * 2 ^ 59
def prefixEnd_3151341 : Nat := 4983230072969 + 3 ^ 40 * 3151341 * 2
def baseEnd_3151341 : Nat := 1618152639220460097544753

theorem tailTrace_3151341 : CollatzResearch.WordTrace tailWord_3151341 prefixEnd_3151341 1618152639220460097544753 := by
  unfold tailWord_3151341
  simp only [CollatzResearch.WordTrace]
  refine ⟨114938848876237238039125877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76625899250824825359417251 114938848876237238039125877)
  ·
    refine ⟨10775517082147241066168051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114938848876237238039125877 10775517082147241066168051)
    ·
      refine ⟨16163275623220861599252077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10775517082147241066168051 16163275623220861599252077)
      ·
        refine ⟨6061228358707823099719529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16163275623220861599252077 6061228358707823099719529)
        ·
          refine ⟨4545921269030867324789647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6061228358707823099719529 4545921269030867324789647)
          ·
            refine ⟨6818881903546300987184471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4545921269030867324789647 6818881903546300987184471)
            ·
              refine ⟨10228322855319451480776707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6818881903546300987184471 10228322855319451480776707)
              ·
                refine ⟨15342484282979177221165061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10228322855319451480776707 15342484282979177221165061)
                ·
                  refine ⟨2876715803058595728968449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15342484282979177221165061 2876715803058595728968449)
                  ·
                    refine ⟨2157536852293946796726337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2876715803058595728968449 2157536852293946796726337)
                    ·
                      refine ⟨1618152639220460097544753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2157536852293946796726337 1618152639220460097544753)
                      ·
                        rfl

theorem cell23_3151341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_3151341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151341 prefixEnd_3151341 := by exact prefixLift 3151341
  have htrace : WordTrace (prefixWord ++ tailWord_3151341) baseStart_3151341 baseEnd_3151341 := by
    simpa [prefixWord, tailWord_3151341, baseEnd_3151341] using wordTrace_append hprefix tailTrace_3151341
  have hstable : (prefixWord ++ tailWord_3151341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151341).length < 2 ^ (prefixWord ++ tailWord_3151341).sum := by decide
  have hdescent : baseEnd_3151341 < baseStart_3151341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151353 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3151353 : Nat := 118140960795 + 3151353 * 2 ^ 59
def prefixEnd_3151353 : Nat := 4983230072969 + 3 ^ 40 * 3151353 * 2
def baseEnd_3151353 : Nat := 1618158800988314050594697

theorem tailTrace_3151353 : CollatzResearch.WordTrace tailWord_3151353 prefixEnd_3151353 1618158800988314050594697 := by
  unfold tailWord_3151353
  simp only [CollatzResearch.WordTrace]
  refine ⟨114939286552193764088562713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76626191034795842725708475 114939286552193764088562713)
  ·
    refine ⟨86204464914145323066422035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114939286552193764088562713 86204464914145323066422035)
    ·
      refine ⟨129306697371217984599633053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86204464914145323066422035 129306697371217984599633053)
      ·
        refine ⟨48490011514206744224862395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129306697371217984599633053 48490011514206744224862395)
        ·
          refine ⟨72735017271310116337293593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48490011514206744224862395 72735017271310116337293593)
          ·
            refine ⟨54551262953482587252970195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72735017271310116337293593 54551262953482587252970195)
            ·
              refine ⟨81826894430223880879455293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54551262953482587252970195 81826894430223880879455293)
              ·
                refine ⟨30685085411333955329795735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81826894430223880879455293 30685085411333955329795735)
                ·
                  refine ⟨46027628117000932994693603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30685085411333955329795735 46027628117000932994693603)
                  ·
                    refine ⟨69041442175501399492040405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46027628117000932994693603 69041442175501399492040405)
                    ·
                      refine ⟨1618158800988314050594697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69041442175501399492040405 1618158800988314050594697)
                      ·
                        rfl

theorem cell23_3151353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3151353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151353 prefixEnd_3151353 := by exact prefixLift 3151353
  have htrace : WordTrace (prefixWord ++ tailWord_3151353) baseStart_3151353 baseEnd_3151353 := by
    simpa [prefixWord, tailWord_3151353, baseEnd_3151353] using wordTrace_append hprefix tailTrace_3151353
  have hstable : (prefixWord ++ tailWord_3151353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151353).length < 2 ^ (prefixWord ++ tailWord_3151353).sum := by decide
  have hdescent : baseEnd_3151353 < baseStart_3151353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151358 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3151358 : Nat := 118140960795 + 3151358 * 2 ^ 59
def prefixEnd_3151358 : Nat := 4983230072969 + 3 ^ 40 * 3151358 * 2
def baseEnd_3151358 : Nat := 1618161368391586531032175

theorem tailTrace_3151358 : CollatzResearch.WordTrace tailWord_3151358 prefixEnd_3151358 1618161368391586531032175 := by
  unfold tailWord_3151358
  simp only [CollatzResearch.WordTrace]
  refine ⟨14367433614646956242811841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76626312611450433294996485 14367433614646956242811841)
  ·
    refine ⟨10775575210985217182108881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14367433614646956242811841 10775575210985217182108881)
    ·
      refine ⟨8081681408238912886581661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10775575210985217182108881 8081681408238912886581661)
      ·
        refine ⟨3030630528089592332468123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8081681408238912886581661 3030630528089592332468123)
        ·
          refine ⟨4545945792134388498702185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030630528089592332468123 4545945792134388498702185)
          ·
            refine ⟨3409459344100791374026639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4545945792134388498702185 3409459344100791374026639)
            ·
              refine ⟨5114189016151187061039959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409459344100791374026639 5114189016151187061039959)
              ·
                refine ⟨7671283524226780591559939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5114189016151187061039959 7671283524226780591559939)
                ·
                  refine ⟨11506925286340170887339909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7671283524226780591559939 11506925286340170887339909)
                  ·
                    refine ⟨2157548491188782041376233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11506925286340170887339909 2157548491188782041376233)
                    ·
                      refine ⟨1618161368391586531032175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2157548491188782041376233 1618161368391586531032175)
                      ·
                        rfl

theorem cell23_3151358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3151358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151358 prefixEnd_3151358 := by exact prefixLift 3151358
  have htrace : WordTrace (prefixWord ++ tailWord_3151358) baseStart_3151358 baseEnd_3151358 := by
    simpa [prefixWord, tailWord_3151358, baseEnd_3151358] using wordTrace_append hprefix tailTrace_3151358
  have hstable : (prefixWord ++ tailWord_3151358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151358).length < 2 ^ (prefixWord ++ tailWord_3151358).sum := by decide
  have hdescent : baseEnd_3151358 < baseStart_3151358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151498 : List Nat := [3, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3]
def baseStart_3151498 : Nat := 118140960795 + 3151498 * 2 ^ 59
def prefixEnd_3151498 : Nat := 4983230072969 + 3 ^ 40 * 3151498 * 2
def baseEnd_3151498 : Nat := 1618233255683215983281531

theorem tailTrace_3151498 : CollatzResearch.WordTrace tailWord_3151498 prefixEnd_3151498 1618233255683215983281531 := by
  unfold tailWord_3151498
  simp only [CollatzResearch.WordTrace]
  refine ⟨28736143784167113463147787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76629716757778969235060765 28736143784167113463147787)
  ·
    refine ⟨43104215676250670194721681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28736143784167113463147787 43104215676250670194721681)
    ·
      refine ⟨32328161757188002646041261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43104215676250670194721681 32328161757188002646041261)
      ·
        refine ⟨12123060658945500992265473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32328161757188002646041261 12123060658945500992265473)
        ·
          refine ⟨9092295494209125744199105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12123060658945500992265473 9092295494209125744199105)
          ·
            refine ⟨6819221620656844308149329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9092295494209125744199105 6819221620656844308149329)
            ·
              refine ⟨5114416215492633231111997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6819221620656844308149329 5114416215492633231111997)
              ·
                refine ⟨1917906080809737461666999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5114416215492633231111997 1917906080809737461666999)
                ·
                  refine ⟨2876859121214606192500499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917906080809737461666999 2876859121214606192500499)
                  ·
                    refine ⟨4315288681821909288750749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2876859121214606192500499 4315288681821909288750749)
                    ·
                      refine ⟨1618233255683215983281531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4315288681821909288750749 1618233255683215983281531)
                      ·
                        rfl

theorem cell23_3151498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_3151498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151498 prefixEnd_3151498 := by exact prefixLift 3151498
  have htrace : WordTrace (prefixWord ++ tailWord_3151498) baseStart_3151498 baseEnd_3151498 := by
    simpa [prefixWord, tailWord_3151498, baseEnd_3151498] using wordTrace_append hprefix tailTrace_3151498
  have hstable : (prefixWord ++ tailWord_3151498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151498).length < 2 ^ (prefixWord ++ tailWord_3151498).sum := by decide
  have hdescent : baseEnd_3151498 < baseStart_3151498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151521 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 3, 2, 2]
def baseStart_3151521 : Nat := 118140960795 + 3151521 * 2 ^ 59
def prefixEnd_3151521 : Nat := 4983230072969 + 3 ^ 40 * 3151521 * 2
def baseEnd_3151521 : Nat := 1618245065738269393293925

theorem tailTrace_3151521 : CollatzResearch.WordTrace tailWord_3151521 prefixEnd_3151521 1618245065738269393293925 := by
  unfold tailWord_3151521
  simp only [CollatzResearch.WordTrace]
  refine ⟨114945414015585128780678417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76630276010390085853785611 114945414015585128780678417)
  ·
    refine ⟨86209060511688846585508813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114945414015585128780678417 86209060511688846585508813)
    ·
      refine ⟨32328397691883317469565805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86209060511688846585508813 32328397691883317469565805)
      ·
        refine ⟨12123149134456244051087177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32328397691883317469565805 12123149134456244051087177)
        ·
          refine ⟨9092361850842183038315383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12123149134456244051087177 9092361850842183038315383)
          ·
            refine ⟨13638542776263274557473075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092361850842183038315383 13638542776263274557473075)
            ·
              refine ⟨20457814164394911836209613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13638542776263274557473075 20457814164394911836209613)
              ·
                refine ⟨7671680311648091938578605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20457814164394911836209613 7671680311648091938578605)
                ·
                  refine ⟨2876880116868034476966977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7671680311648091938578605 2876880116868034476966977)
                  ·
                    refine ⟨2157660087651025857725233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2876880116868034476966977 2157660087651025857725233)
                    ·
                      refine ⟨1618245065738269393293925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2157660087651025857725233 1618245065738269393293925)
                      ·
                        rfl

theorem cell23_3151521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_3151521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151521 prefixEnd_3151521 := by exact prefixLift 3151521
  have htrace : WordTrace (prefixWord ++ tailWord_3151521) baseStart_3151521 baseEnd_3151521 := by
    simpa [prefixWord, tailWord_3151521, baseEnd_3151521] using wordTrace_append hprefix tailTrace_3151521
  have hstable : (prefixWord ++ tailWord_3151521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151521).length < 2 ^ (prefixWord ++ tailWord_3151521).sum := by decide
  have hdescent : baseEnd_3151521 < baseStart_3151521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151547 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 2, 7, 2]
def baseStart_3151547 : Nat := 118140960795 + 3151547 * 2 ^ 59
def prefixEnd_3151547 : Nat := 4983230072969 + 3 ^ 40 * 3151547 * 2
def baseEnd_3151547 : Nat := 1618258416235286291568805

theorem tailTrace_3151547 : CollatzResearch.WordTrace tailWord_3151547 prefixEnd_3151547 1618258416235286291568805 := by
  unfold tailWord_3151547
  simp only [CollatzResearch.WordTrace]
  refine ⟨114946362313490935221124895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76630908208993956814083263 114946362313490935221124895)
  ·
    refine ⟨172419543470236402831687343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114946362313490935221124895 172419543470236402831687343)
    ·
      refine ⟨258629315205354604247531015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172419543470236402831687343 258629315205354604247531015)
      ·
        refine ⟨387943972808031906371296523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258629315205354604247531015 387943972808031906371296523)
        ·
          refine ⟨581915959212047859556944785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387943972808031906371296523 581915959212047859556944785)
          ·
            refine ⟨436436969409035894667708589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581915959212047859556944785 436436969409035894667708589)
            ·
              refine ⟨163663863528388460500390721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 436436969409035894667708589 163663863528388460500390721)
              ·
                refine ⟨122747897646291345375293041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163663863528388460500390721 122747897646291345375293041)
                ·
                  refine ⟨92060923234718509031469781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122747897646291345375293041 92060923234718509031469781)
                  ·
                    refine ⟨2157677888313715055425073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 92060923234718509031469781 2157677888313715055425073)
                    ·
                      refine ⟨1618258416235286291568805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2157677888313715055425073 1618258416235286291568805)
                      ·
                        rfl

theorem cell23_3151547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 7, 2].length) (baseStart_3151547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151547 prefixEnd_3151547 := by exact prefixLift 3151547
  have htrace : WordTrace (prefixWord ++ tailWord_3151547) baseStart_3151547 baseEnd_3151547 := by
    simpa [prefixWord, tailWord_3151547, baseEnd_3151547] using wordTrace_append hprefix tailTrace_3151547
  have hstable : (prefixWord ++ tailWord_3151547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151547).length < 2 ^ (prefixWord ++ tailWord_3151547).sum := by decide
  have hdescent : baseEnd_3151547 < baseStart_3151547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151558 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3151558 : Nat := 118140960795 + 3151558 * 2 ^ 59
def prefixEnd_3151558 : Nat := 4983230072969 + 3 ^ 40 * 3151558 * 2
def baseEnd_3151558 : Nat := 1618264064522485748531255

theorem tailTrace_3151558 : CollatzResearch.WordTrace tailWord_3151558 prefixEnd_3151558 1618264064522485748531255 := by
  unfold tailWord_3151558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3592086359889096378117979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76631175677634056066516885 3592086359889096378117979)
  ·
    refine ⟨5388129539833644567176969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3592086359889096378117979 5388129539833644567176969)
    ·
      refine ⟨4041097154875233425382727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5388129539833644567176969 4041097154875233425382727)
      ·
        refine ⟨6061645732312850138074091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4041097154875233425382727 6061645732312850138074091)
        ·
          refine ⟨9092468598469275207111137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061645732312850138074091 9092468598469275207111137)
          ·
            refine ⟨6819351448851956405333353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9092468598469275207111137 6819351448851956405333353)
            ·
              refine ⟨5114513586638967304000015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6819351448851956405333353 5114513586638967304000015)
              ·
                refine ⟨7671770379958450956000023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5114513586638967304000015 7671770379958450956000023)
                ·
                  refine ⟨11507655569937676434000035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7671770379958450956000023 11507655569937676434000035)
                  ·
                    refine ⟨17261483354906514651000053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11507655569937676434000035 17261483354906514651000053)
                    ·
                      refine ⟨1618264064522485748531255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17261483354906514651000053 1618264064522485748531255)
                      ·
                        rfl

theorem cell23_3151558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3151558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151558 prefixEnd_3151558 := by exact prefixLift 3151558
  have htrace : WordTrace (prefixWord ++ tailWord_3151558) baseStart_3151558 baseEnd_3151558 := by
    simpa [prefixWord, tailWord_3151558, baseEnd_3151558] using wordTrace_append hprefix tailTrace_3151558
  have hstable : (prefixWord ++ tailWord_3151558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151558).length < 2 ^ (prefixWord ++ tailWord_3151558).sum := by decide
  have hdescent : baseEnd_3151558 < baseStart_3151558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151572 : List Nat := [2, 4, 1, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3151572 : Nat := 118140960795 + 3151572 * 2 ^ 59
def prefixEnd_3151572 : Nat := 4983230072969 + 3 ^ 40 * 3151572 * 2
def baseEnd_3151572 : Nat := 1618271253251648693756191

theorem tailTrace_3151572 : CollatzResearch.WordTrace tailWord_3151572 prefixEnd_3151572 1618271253251648693756191 := by
  unfold tailWord_3151572
  simp only [CollatzResearch.WordTrace]
  refine ⟨57473637069200182245392485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76631516092266909660523313 57473637069200182245392485)
  ·
    refine ⟨10776306950475034171011091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57473637069200182245392485 10776306950475034171011091)
    ·
      refine ⟨16164460425712551256516637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10776306950475034171011091 16164460425712551256516637)
      ·
        refine ⟨6061672659642206721193739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16164460425712551256516637 6061672659642206721193739)
        ·
          refine ⟨9092508989463310081790609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061672659642206721193739 9092508989463310081790609)
          ·
            refine ⟨6819381742097482561342957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9092508989463310081790609 6819381742097482561342957)
            ·
              refine ⟨2557268153286555960503609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6819381742097482561342957 2557268153286555960503609)
              ·
                refine ⟨1917951114964916970377707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2557268153286555960503609 1917951114964916970377707)
                ·
                  refine ⟨2876926672447375455566561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917951114964916970377707 2876926672447375455566561)
                  ·
                    refine ⟨2157695004335531591674921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2876926672447375455566561 2157695004335531591674921)
                    ·
                      refine ⟨1618271253251648693756191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2157695004335531591674921 1618271253251648693756191)
                      ·
                        rfl

theorem cell23_3151572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3151572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151572 prefixEnd_3151572 := by exact prefixLift 3151572
  have htrace : WordTrace (prefixWord ++ tailWord_3151572) baseStart_3151572 baseEnd_3151572 := by
    simpa [prefixWord, tailWord_3151572, baseEnd_3151572] using wordTrace_append hprefix tailTrace_3151572
  have hstable : (prefixWord ++ tailWord_3151572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151572).length < 2 ^ (prefixWord ++ tailWord_3151572).sum := by decide
  have hdescent : baseEnd_3151572 < baseStart_3151572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151644 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_3151644 : Nat := 118140960795 + 3151644 * 2 ^ 59
def prefixEnd_3151644 : Nat := 4983230072969 + 3 ^ 40 * 3151644 * 2
def baseEnd_3151644 : Nat := 1618308223858772412055859

theorem tailTrace_3151644 : CollatzResearch.WordTrace tailWord_3151644 prefixEnd_3151644 1618308223858772412055859 := by
  unfold tailWord_3151644
  simp only [CollatzResearch.WordTrace]
  refine ⟨57474950097069760393702993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76633266796093013858270657 57474950097069760393702993)
  ·
    refine ⟨43106212572802320295277245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57474950097069760393702993 43106212572802320295277245)
    ·
      refine ⟨16164829714800870110728967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43106212572802320295277245 16164829714800870110728967)
      ·
        refine ⟨24247244572201305166093451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16164829714800870110728967 24247244572201305166093451)
        ·
          refine ⟨36370866858301957749140177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24247244572201305166093451 36370866858301957749140177)
          ·
            refine ⟨27278150143726468311855133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36370866858301957749140177 27278150143726468311855133)
            ·
              refine ⟨10229306303897425616945675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27278150143726468311855133 10229306303897425616945675)
              ·
                refine ⟨15343959455846138425418513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10229306303897425616945675 15343959455846138425418513)
                ·
                  refine ⟨11507969591884603819063885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15343959455846138425418513 11507969591884603819063885)
                  ·
                    refine ⟨4315488596956726432148957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11507969591884603819063885 4315488596956726432148957)
                    ·
                      refine ⟨1618308223858772412055859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4315488596956726432148957 1618308223858772412055859)
                      ·
                        rfl

theorem cell23_3151644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_3151644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151644 prefixEnd_3151644 := by exact prefixLift 3151644
  have htrace : WordTrace (prefixWord ++ tailWord_3151644) baseStart_3151644 baseEnd_3151644 := by
    simpa [prefixWord, tailWord_3151644, baseEnd_3151644] using wordTrace_append hprefix tailTrace_3151644
  have hstable : (prefixWord ++ tailWord_3151644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151644).length < 2 ^ (prefixWord ++ tailWord_3151644).sum := by decide
  have hdescent : baseEnd_3151644 < baseStart_3151644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151647 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 1, 7]
def baseStart_3151647 : Nat := 118140960795 + 3151647 * 2 ^ 59
def prefixEnd_3151647 : Nat := 4983230072969 + 3 ^ 40 * 3151647 * 2
def baseEnd_3151647 : Nat := 539436588100245300106115

theorem tailTrace_3151647 : CollatzResearch.WordTrace tailWord_3151647 prefixEnd_3151647 539436588100245300106115 := by
  unfold tailWord_3151647
  simp only [CollatzResearch.WordTrace]
  refine ⟨114950009613128652299765195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76633339742085768199843463 114950009613128652299765195)
  ·
    refine ⟨172425014419692978449647793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114950009613128652299765195 172425014419692978449647793)
    ·
      refine ⟨129318760814769733837235845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172425014419692978449647793 129318760814769733837235845)
      ·
        refine ⟨24247267652769325094481721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129318760814769733837235845 24247267652769325094481721)
        ·
          refine ⟨18185450739576993820861291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24247267652769325094481721 18185450739576993820861291)
          ·
            refine ⟨27278176109365490731291937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18185450739576993820861291 27278176109365490731291937)
            ·
              refine ⟨20458632082024118048468953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27278176109365490731291937 20458632082024118048468953)
              ·
                refine ⟨15343974061518088536351715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20458632082024118048468953 15343974061518088536351715)
                ·
                  refine ⟨23015961092277132804527573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15343974061518088536351715 23015961092277132804527573)
                  ·
                    refine ⟨539436588100245300106115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23015961092277132804527573 539436588100245300106115)
                    ·
                      rfl

theorem cell23_3151647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_3151647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151647 prefixEnd_3151647 := by exact prefixLift 3151647
  have htrace : WordTrace (prefixWord ++ tailWord_3151647) baseStart_3151647 baseEnd_3151647 := by
    simpa [prefixWord, tailWord_3151647, baseEnd_3151647] using wordTrace_append hprefix tailTrace_3151647
  have hstable : (prefixWord ++ tailWord_3151647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151647).length < 2 ^ (prefixWord ++ tailWord_3151647).sum := by decide
  have hdescent : baseEnd_3151647 < baseStart_3151647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151668 : List Nat := [2, 5, 1, 1, 2, 2, 2, 3, 5]
def baseStart_3151668 : Nat := 118140960795 + 3151668 * 2 ^ 59
def prefixEnd_3151668 : Nat := 4983230072969 + 3 ^ 40 * 3151668 * 2
def baseEnd_3151668 : Nat := 179813394154942257572861

theorem tailTrace_3151668 : CollatzResearch.WordTrace tailWord_3151668 prefixEnd_3151668 179813394154942257572861 := by
  unfold tailWord_3151668
  simp only [CollatzResearch.WordTrace]
  refine ⟨57475387773026286443139829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76633850364035048590853105 57475387773026286443139829)
  ·
    refine ⟨5388317603721214354044359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57475387773026286443139829 5388317603721214354044359)
    ·
      refine ⟨8082476405581821531066539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5388317603721214354044359 8082476405581821531066539)
      ·
        refine ⟨12123714608372732296599809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8082476405581821531066539 12123714608372732296599809)
        ·
          refine ⟨9092785956279549222449857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12123714608372732296599809 9092785956279549222449857)
          ·
            refine ⟨6819589467209661916837393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9092785956279549222449857 6819589467209661916837393)
            ·
              refine ⟨5114692100407246437628045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6819589467209661916837393 5114692100407246437628045)
              ·
                refine ⟨1918009537652717414110517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5114692100407246437628045 1918009537652717414110517)
                ·
                  refine ⟨179813394154942257572861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1918009537652717414110517 179813394154942257572861)
                  ·
                    rfl

theorem cell23_3151668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_3151668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151668 prefixEnd_3151668 := by exact prefixLift 3151668
  have htrace : WordTrace (prefixWord ++ tailWord_3151668) baseStart_3151668 baseEnd_3151668 := by
    simpa [prefixWord, tailWord_3151668, baseEnd_3151668] using wordTrace_append hprefix tailTrace_3151668
  have hstable : (prefixWord ++ tailWord_3151668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151668).length < 2 ^ (prefixWord ++ tailWord_3151668).sum := by decide
  have hdescent : baseEnd_3151668 < baseStart_3151668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151687 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_3151687 : Nat := 118140960795 + 3151687 * 2 ^ 59
def prefixEnd_3151687 : Nat := 4983230072969 + 3 ^ 40 * 3151687 * 2
def baseEnd_3151687 : Nat := 1618330303526915743818161

theorem tailTrace_3151687 : CollatzResearch.WordTrace tailWord_3151687 prefixEnd_3151687 1618330303526915743818161 := by
  unfold tailWord_3151687
  simp only [CollatzResearch.WordTrace]
  refine ⟨114951468532983739131221315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76634312355322492754147543 114951468532983739131221315)
  ·
    refine ⟨172427202799475608696831973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114951468532983739131221315 172427202799475608696831973)
    ·
      refine ⟨32330100524901676630655995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172427202799475608696831973 32330100524901676630655995)
      ·
        refine ⟨48495150787352514945983993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32330100524901676630655995 48495150787352514945983993)
        ·
          refine ⟨36371363090514386209487995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48495150787352514945983993 36371363090514386209487995)
          ·
            refine ⟨54557044635771579314231993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36371363090514386209487995 54557044635771579314231993)
            ·
              refine ⟨40917783476828684485673995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54557044635771579314231993 40917783476828684485673995)
              ·
                refine ⟨61376675215243026728510993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40917783476828684485673995 61376675215243026728510993)
                ·
                  refine ⟨46032506411432270046383245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61376675215243026728510993 46032506411432270046383245)
                  ·
                    refine ⟨17262189904287101267393717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46032506411432270046383245 17262189904287101267393717)
                    ·
                      refine ⟨1618330303526915743818161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17262189904287101267393717 1618330303526915743818161)
                      ·
                        rfl

theorem cell23_3151687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_3151687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151687 prefixEnd_3151687 := by exact prefixLift 3151687
  have htrace : WordTrace (prefixWord ++ tailWord_3151687) baseStart_3151687 baseEnd_3151687 := by
    simpa [prefixWord, tailWord_3151687, baseEnd_3151687] using wordTrace_append hprefix tailTrace_3151687
  have hstable : (prefixWord ++ tailWord_3151687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151687).length < 2 ^ (prefixWord ++ tailWord_3151687).sum := by decide
  have hdescent : baseEnd_3151687 < baseStart_3151687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151701 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 2, 4, 2]
def baseStart_3151701 : Nat := 118140960795 + 3151701 * 2 ^ 59
def prefixEnd_3151701 : Nat := 4983230072969 + 3 ^ 40 * 3151701 * 2
def baseEnd_3151701 : Nat := 1618337492256078689043097

theorem tailTrace_3151701 : CollatzResearch.WordTrace tailWord_3151701 prefixEnd_3151701 1618337492256078689043097 := by
  unfold tailWord_3151701
  simp only [CollatzResearch.WordTrace]
  refine ⟨114951979154933019522230957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76634652769955346348153971 114951979154933019522230957)
  ·
    refine ⟨43106992183099882320836609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114951979154933019522230957 43106992183099882320836609)
    ·
      refine ⟨32330244137324911740627457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43106992183099882320836609 32330244137324911740627457)
      ·
        refine ⟨24247683102993683805470593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32330244137324911740627457 24247683102993683805470593)
        ·
          refine ⟨18185762327245262854102945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24247683102993683805470593 18185762327245262854102945)
          ·
            refine ⟨13639321745433947140577209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18185762327245262854102945 13639321745433947140577209)
            ·
              refine ⟨10229491309075460355432907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13639321745433947140577209 10229491309075460355432907)
              ·
                refine ⟨15344236963613190533149361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10229491309075460355432907 15344236963613190533149361)
                ·
                  refine ⟨11508177722709892899862021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15344236963613190533149361 11508177722709892899862021)
                  ·
                    refine ⟨2157783323008104918724129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11508177722709892899862021 2157783323008104918724129)
                    ·
                      refine ⟨1618337492256078689043097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2157783323008104918724129 1618337492256078689043097)
                      ·
                        rfl

theorem cell23_3151701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_3151701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151701 prefixEnd_3151701 := by exact prefixLift 3151701
  have htrace : WordTrace (prefixWord ++ tailWord_3151701) baseStart_3151701 baseEnd_3151701 := by
    simpa [prefixWord, tailWord_3151701, baseEnd_3151701] using wordTrace_append hprefix tailTrace_3151701
  have hstable : (prefixWord ++ tailWord_3151701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151701).length < 2 ^ (prefixWord ++ tailWord_3151701).sum := by decide
  have hdescent : baseEnd_3151701 < baseStart_3151701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151745 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3151745 : Nat := 118140960795 + 3151745 * 2 ^ 59
def prefixEnd_3151745 : Nat := 4983230072969 + 3 ^ 40 * 3151745 * 2
def baseEnd_3151745 : Nat := 539453361801625505630965

theorem tailTrace_3151745 : CollatzResearch.WordTrace tailWord_3151745 prefixEnd_3151745 539453361801625505630965 := by
  unfold tailWord_3151745
  simp only [CollatzResearch.WordTrace]
  refine ⟨114953583966773615036832689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76635722644515743357888459 114953583966773615036832689)
  ·
    refine ⟨86215187975080211277624517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114953583966773615036832689 86215187975080211277624517)
    ·
      refine ⟨16165347745327539614554597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86215187975080211277624517 16165347745327539614554597)
      ·
        refine ⟨3031002702248913677728987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16165347745327539614554597 3031002702248913677728987)
        ·
          refine ⟨4546504053373370516593481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031002702248913677728987 4546504053373370516593481)
          ·
            refine ⟨3409878040030027887445111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4546504053373370516593481 3409878040030027887445111)
            ·
              refine ⟨5114817060045041831167667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409878040030027887445111 5114817060045041831167667)
              ·
                refine ⟨7672225590067562746751501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5114817060045041831167667 7672225590067562746751501)
                ·
                  refine ⟨2877084596275336030031813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7672225590067562746751501 2877084596275336030031813)
                  ·
                    refine ⟨539453361801625505630965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2877084596275336030031813 539453361801625505630965)
                    ·
                      rfl

theorem cell23_3151745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3151745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151745 prefixEnd_3151745 := by exact prefixLift 3151745
  have htrace : WordTrace (prefixWord ++ tailWord_3151745) baseStart_3151745 baseEnd_3151745 := by
    simpa [prefixWord, tailWord_3151745, baseEnd_3151745] using wordTrace_append hprefix tailTrace_3151745
  have hstable : (prefixWord ++ tailWord_3151745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151745).length < 2 ^ (prefixWord ++ tailWord_3151745).sum := by decide
  have hdescent : baseEnd_3151745 < baseStart_3151745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151758 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_3151758 : Nat := 118140960795 + 3151758 * 2 ^ 59
def prefixEnd_3151758 : Nat := 4983230072969 + 3 ^ 40 * 3151758 * 2
def baseEnd_3151758 : Nat := 179818528961487218447815

theorem tailTrace_3151758 : CollatzResearch.WordTrace tailWord_3151758 prefixEnd_3151758 179818528961487218447815 := by
  unfold tailWord_3151758
  simp only [CollatzResearch.WordTrace]
  refine ⟨14369257264465814782131991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76636038743817678838037285 14369257264465814782131991)
  ·
    refine ⟨21553885896698722173197987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14369257264465814782131991 21553885896698722173197987)
    ·
      refine ⟨32330828845048083259796981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21553885896698722173197987 32330828845048083259796981)
      ·
        refine ⟨3031015204223257805605967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32330828845048083259796981 3031015204223257805605967)
        ·
          refine ⟨4546522806334886708408951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031015204223257805605967 4546522806334886708408951)
          ·
            refine ⟨6819784209502330062613427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4546522806334886708408951 6819784209502330062613427)
            ·
              refine ⟨10229676314253495093920141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6819784209502330062613427 10229676314253495093920141)
              ·
                refine ⟨3836128617845060660220053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10229676314253495093920141 3836128617845060660220053)
                ·
                  refine ⟨179818528961487218447815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3836128617845060660220053 179818528961487218447815)
                  ·
                    rfl

theorem cell23_3151758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_3151758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151758 prefixEnd_3151758 := by exact prefixLift 3151758
  have htrace : WordTrace (prefixWord ++ tailWord_3151758) baseStart_3151758 baseEnd_3151758 := by
    simpa [prefixWord, tailWord_3151758, baseEnd_3151758] using wordTrace_append hprefix tailTrace_3151758
  have hstable : (prefixWord ++ tailWord_3151758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151758).length < 2 ^ (prefixWord ++ tailWord_3151758).sum := by decide
  have hdescent : baseEnd_3151758 < baseStart_3151758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151796 : List Nat := [2, 5, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3151796 : Nat := 118140960795 + 3151796 * 2 ^ 59
def prefixEnd_3151796 : Nat := 4983230072969 + 3 ^ 40 * 3151796 * 2
def baseEnd_3151796 : Nat := 539462090972751939118387

theorem tailTrace_3151796 : CollatzResearch.WordTrace tailWord_3151796 prefixEnd_3151796 539462090972751939118387 := by
  unfold tailWord_3151796
  simp only [CollatzResearch.WordTrace]
  refine ⟨57477722044794425373469621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76636962726392567164626161 57477722044794425373469621)
  ·
    refine ⟨5388536441699477378762777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57477722044794425373469621 5388536441699477378762777)
    ·
      refine ⟨4041402331274608034072083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5388536441699477378762777 4041402331274608034072083)
      ·
        refine ⟨6062103496911912051108125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4041402331274608034072083 6062103496911912051108125)
        ·
          refine ⟨2273288811341967019165547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6062103496911912051108125 2273288811341967019165547)
          ·
            refine ⟨3409933217012950528748321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273288811341967019165547 3409933217012950528748321)
            ·
              refine ⟨2557449912759712896561241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3409933217012950528748321 2557449912759712896561241)
              ·
                refine ⟨1918087434569784672420931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2557449912759712896561241 1918087434569784672420931)
                ·
                  refine ⟨2877131151854677008631397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918087434569784672420931 2877131151854677008631397)
                  ·
                    refine ⟨539462090972751939118387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2877131151854677008631397 539462090972751939118387)
                    ·
                      rfl

theorem cell23_3151796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3151796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151796 prefixEnd_3151796 := by exact prefixLift 3151796
  have htrace : WordTrace (prefixWord ++ tailWord_3151796) baseStart_3151796 baseEnd_3151796 := by
    simpa [prefixWord, tailWord_3151796, baseEnd_3151796] using wordTrace_append hprefix tailTrace_3151796
  have hstable : (prefixWord ++ tailWord_3151796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151796).length < 2 ^ (prefixWord ++ tailWord_3151796).sum := by decide
  have hdescent : baseEnd_3151796 < baseStart_3151796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151808 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 3, 2, 2]
def baseStart_3151808 : Nat := 118140960795 + 3151808 * 2 ^ 59
def prefixEnd_3151808 : Nat := 4983230072969 + 3 ^ 40 * 3151808 * 2
def baseEnd_3151808 : Nat := 1618392434686109770405105

theorem tailTrace_3151808 : CollatzResearch.WordTrace tailWord_3151808 prefixEnd_3151808 1618392434686109770405105 := by
  unfold tailWord_3151808
  simp only [CollatzResearch.WordTrace]
  refine ⟨57477940882772688398188039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76637254510363584530917385 57477940882772688398188039)
  ·
    refine ⟨86216911324159032597282059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57477940882772688398188039 86216911324159032597282059)
    ·
      refine ⟨129325366986238548895923089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86216911324159032597282059 129325366986238548895923089)
      ·
        refine ⟨96994025239678911671942317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129325366986238548895923089 96994025239678911671942317)
        ·
          refine ⟨36372759464879591876978369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96994025239678911671942317 36372759464879591876978369)
          ·
            refine ⟨27279569598659693907733777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36372759464879591876978369 27279569598659693907733777)
            ·
              refine ⟨20459677198994770430800333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27279569598659693907733777 20459677198994770430800333)
              ·
                refine ⟨7672378949623038911550125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20459677198994770430800333 7672378949623038911550125)
                ·
                  refine ⟨2877142106108639591831297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7672378949623038911550125 2877142106108639591831297)
                  ·
                    refine ⟨2157856579581479693873473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2877142106108639591831297 2157856579581479693873473)
                    ·
                      refine ⟨1618392434686109770405105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2157856579581479693873473 1618392434686109770405105)
                      ·
                        rfl

theorem cell23_3151808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3, 2, 2].length) (baseStart_3151808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151808 prefixEnd_3151808 := by exact prefixLift 3151808
  have htrace : WordTrace (prefixWord ++ tailWord_3151808) baseStart_3151808 baseEnd_3151808 := by
    simpa [prefixWord, tailWord_3151808, baseEnd_3151808] using wordTrace_append hprefix tailTrace_3151808
  have hstable : (prefixWord ++ tailWord_3151808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151808).length < 2 ^ (prefixWord ++ tailWord_3151808).sum := by decide
  have hdescent : baseEnd_3151808 < baseStart_3151808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151828 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3151828 : Nat := 118140960795 + 3151828 * 2 ^ 59
def prefixEnd_3151828 : Nat := 4983230072969 + 3 ^ 40 * 3151828 * 2
def baseEnd_3151828 : Nat := 1618402704299199692155013

theorem tailTrace_3151828 : CollatzResearch.WordTrace tailWord_3151828 prefixEnd_3151828 1618402704299199692155013 := by
  unfold tailWord_3151828
  simp only [CollatzResearch.WordTrace]
  refine ⟨57478305612736460106052069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76637740816981946808069425 57478305612736460106052069)
  ·
    refine ⟨10777182302388086269884763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57478305612736460106052069 10777182302388086269884763)
    ·
      refine ⟨16165773453582129404827145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10777182302388086269884763 16165773453582129404827145)
      ·
        refine ⟨12124330090186597053620359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16165773453582129404827145 12124330090186597053620359)
        ·
          refine ⟨18186495135279895580430539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12124330090186597053620359 18186495135279895580430539)
          ·
            refine ⟨27279742702919843370645809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18186495135279895580430539 27279742702919843370645809)
            ·
              refine ⟨20459807027189882527984357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27279742702919843370645809 20459807027189882527984357)
              ·
                refine ⟨3836213817598102973997067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20459807027189882527984357 3836213817598102973997067)
                ·
                  refine ⟨5754320726397154460995601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836213817598102973997067 5754320726397154460995601)
                  ·
                    refine ⟨4315740544797865845746701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5754320726397154460995601 4315740544797865845746701)
                    ·
                      refine ⟨1618402704299199692155013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4315740544797865845746701 1618402704299199692155013)
                      ·
                        rfl

theorem cell23_3151828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3151828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151828 prefixEnd_3151828 := by exact prefixLift 3151828
  have htrace : WordTrace (prefixWord ++ tailWord_3151828) baseStart_3151828 baseEnd_3151828 := by
    simpa [prefixWord, tailWord_3151828, baseEnd_3151828] using wordTrace_append hprefix tailTrace_3151828
  have hstable : (prefixWord ++ tailWord_3151828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151828).length < 2 ^ (prefixWord ++ tailWord_3151828).sum := by decide
  have hdescent : baseEnd_3151828 < baseStart_3151828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151836 : List Nat := [2, 2, 6, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_3151836 : Nat := 118140960795 + 3151836 * 2 ^ 59
def prefixEnd_3151836 : Nat := 4983230072969 + 3 ^ 40 * 3151836 * 2
def baseEnd_3151836 : Nat := 1618406812144435660854977

theorem tailTrace_3151836 : CollatzResearch.WordTrace tailWord_3151836 prefixEnd_3151836 1618406812144435660854977 := by
  unfold tailWord_3151836
  simp only [CollatzResearch.WordTrace]
  refine ⟨57478451504721968789197681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76637935339629291718930241 57478451504721968789197681)
  ·
    refine ⟨43108838628541476591898261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57478451504721968789197681 43108838628541476591898261)
    ·
      refine ⟨2020726810712881715245231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43108838628541476591898261 2020726810712881715245231)
      ·
        refine ⟨3031090216069322572867847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020726810712881715245231 3031090216069322572867847)
        ·
          refine ⟨4546635324103983859301771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031090216069322572867847 4546635324103983859301771)
          ·
            refine ⟨6819952986155975788952657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4546635324103983859301771 6819952986155975788952657)
            ·
              refine ⟨5114964739616981841714493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6819952986155975788952657 5114964739616981841714493)
              ·
                refine ⟨1918111777356368190642935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5114964739616981841714493 1918111777356368190642935)
                ·
                  refine ⟨2877167666034552285964403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918111777356368190642935 2877167666034552285964403)
                  ·
                    refine ⟨4315751499051828428946605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2877167666034552285964403 4315751499051828428946605)
                    ·
                      refine ⟨1618406812144435660854977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4315751499051828428946605 1618406812144435660854977)
                      ·
                        rfl

theorem cell23_3151836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_3151836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151836 prefixEnd_3151836 := by exact prefixLift 3151836
  have htrace : WordTrace (prefixWord ++ tailWord_3151836) baseStart_3151836 baseEnd_3151836 := by
    simpa [prefixWord, tailWord_3151836, baseEnd_3151836] using wordTrace_append hprefix tailTrace_3151836
  have hstable : (prefixWord ++ tailWord_3151836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151836).length < 2 ^ (prefixWord ++ tailWord_3151836).sum := by decide
  have hdescent : baseEnd_3151836 < baseStart_3151836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151841 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_3151841 : Nat := 118140960795 + 3151841 * 2 ^ 59
def prefixEnd_3151841 : Nat := 4983230072969 + 3 ^ 40 * 3151841 * 2
def baseEnd_3151841 : Nat := 1618409379547708141292453

theorem tailTrace_3151841 : CollatzResearch.WordTrace tailWord_3151841 prefixEnd_3151841 1618409379547708141292453 := by
  unfold tailWord_3151841
  simp only [CollatzResearch.WordTrace]
  refine ⟨114957085374425823432327377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76638056916283882288218251 114957085374425823432327377)
  ·
    refine ⟨86217814030819367574245533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114957085374425823432327377 86217814030819367574245533)
    ·
      refine ⟨32331680261557262840342075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86217814030819367574245533 32331680261557262840342075)
      ·
        refine ⟨48497520392335894260513113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32331680261557262840342075 48497520392335894260513113)
        ·
          refine ⟨36373140294251920695384835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48497520392335894260513113 36373140294251920695384835)
          ·
            refine ⟨54559710441377881043077253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36373140294251920695384835 54559710441377881043077253)
            ·
              refine ⟨10229945707758352695576985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54559710441377881043077253 10229945707758352695576985)
              ·
                refine ⟨7672459280818764521682739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10229945707758352695576985 7672459280818764521682739)
                ·
                  refine ⟨11508688921228146782524109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7672459280818764521682739 11508688921228146782524109)
                  ·
                    refine ⟨4315758345460555043446541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11508688921228146782524109 4315758345460555043446541)
                    ·
                      refine ⟨1618409379547708141292453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4315758345460555043446541 1618409379547708141292453)
                      ·
                        rfl

theorem cell23_3151841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_3151841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151841 prefixEnd_3151841 := by exact prefixLift 3151841
  have htrace : WordTrace (prefixWord ++ tailWord_3151841) baseStart_3151841 baseEnd_3151841 := by
    simpa [prefixWord, tailWord_3151841, baseEnd_3151841] using wordTrace_append hprefix tailTrace_3151841
  have hstable : (prefixWord ++ tailWord_3151841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151841).length < 2 ^ (prefixWord ++ tailWord_3151841).sum := by decide
  have hdescent : baseEnd_3151841 < baseStart_3151841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151864 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_3151864 : Nat := 118140960795 + 3151864 * 2 ^ 59
def prefixEnd_3151864 : Nat := 4983230072969 + 3 ^ 40 * 3151864 * 2
def baseEnd_3151864 : Nat := 1618421189602761551304847

theorem tailTrace_3151864 : CollatzResearch.WordTrace tailWord_3151864 prefixEnd_3151864 1618421189602761551304847 := by
  unfold tailWord_3151864
  simp only [CollatzResearch.WordTrace]
  refine ⟨57478962126671249180207323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76638616168894998906943097 57478962126671249180207323)
  ·
    refine ⟨86218443190006873770310985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57478962126671249180207323 86218443190006873770310985)
    ·
      refine ⟨64663832392505155327733239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86218443190006873770310985 64663832392505155327733239)
      ·
        refine ⟨96995748588757732991599859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64663832392505155327733239 96995748588757732991599859)
        ·
          refine ⟨145493622883136599487399789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96995748588757732991599859 145493622883136599487399789)
          ·
            refine ⟨54560108581176224807774921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145493622883136599487399789 54560108581176224807774921)
            ·
              refine ⟨40920081435882168605831191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54560108581176224807774921 40920081435882168605831191)
              ·
                refine ⟨61380122153823252908746787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40920081435882168605831191 61380122153823252908746787)
                ·
                  refine ⟨92070183230734879363120181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61380122153823252908746787 92070183230734879363120181)
                  ·
                    refine ⟨8631579677881394940292517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92070183230734879363120181 8631579677881394940292517)
                    ·
                      refine ⟨1618421189602761551304847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8631579677881394940292517 1618421189602761551304847)
                      ·
                        rfl

theorem cell23_3151864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_3151864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151864 prefixEnd_3151864 := by exact prefixLift 3151864
  have htrace : WordTrace (prefixWord ++ tailWord_3151864) baseStart_3151864 baseEnd_3151864 := by
    simpa [prefixWord, tailWord_3151864, baseEnd_3151864] using wordTrace_append hprefix tailTrace_3151864
  have hstable : (prefixWord ++ tailWord_3151864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151864).length < 2 ^ (prefixWord ++ tailWord_3151864).sum := by decide
  have hdescent : baseEnd_3151864 < baseStart_3151864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151901 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3151901 : Nat := 118140960795 + 3151901 * 2 ^ 59
def prefixEnd_3151901 : Nat := 4983230072969 + 3 ^ 40 * 3151901 * 2
def baseEnd_3151901 : Nat := 1618440188386977906542177

theorem tailTrace_3151901 : CollatzResearch.WordTrace tailWord_3151901 prefixEnd_3151901 1618440188386977906542177 := by
  unfold tailWord_3151901
  simp only [CollatzResearch.WordTrace]
  refine ⟨114959273754208453679511557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76639515836138969119674371 114959273754208453679511557)
  ·
    refine ⟨21554863828914085064908417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114959273754208453679511557 21554863828914085064908417)
    ·
      refine ⟨16166147871685563798681313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21554863828914085064908417 16166147871685563798681313)
      ·
        refine ⟨12124610903764172849010985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16166147871685563798681313 12124610903764172849010985)
        ·
          refine ⟨9093458177823129636758239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12124610903764172849010985 9093458177823129636758239)
          ·
            refine ⟨13640187266734694455137359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9093458177823129636758239 13640187266734694455137359)
            ·
              refine ⟨20460280900102041682706039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13640187266734694455137359 20460280900102041682706039)
              ·
                refine ⟨30690421350153062524059059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20460280900102041682706039 30690421350153062524059059)
                ·
                  refine ⟨46035632025229593786088589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30690421350153062524059059 46035632025229593786088589)
                  ·
                    refine ⟨17263362009461097669783221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46035632025229593786088589 17263362009461097669783221)
                    ·
                      refine ⟨1618440188386977906542177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17263362009461097669783221 1618440188386977906542177)
                      ·
                        rfl

theorem cell23_3151901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3151901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151901 prefixEnd_3151901 := by exact prefixLift 3151901
  have htrace : WordTrace (prefixWord ++ tailWord_3151901) baseStart_3151901 baseEnd_3151901 := by
    simpa [prefixWord, tailWord_3151901, baseEnd_3151901] using wordTrace_append hprefix tailTrace_3151901
  have hstable : (prefixWord ++ tailWord_3151901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151901).length < 2 ^ (prefixWord ++ tailWord_3151901).sum := by decide
  have hdescent : baseEnd_3151901 < baseStart_3151901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151921 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 7]
def baseStart_3151921 : Nat := 118140960795 + 3151921 * 2 ^ 59
def prefixEnd_3151921 : Nat := 4983230072969 + 3 ^ 40 * 3151921 * 2
def baseEnd_3151921 : Nat := 179827828666674203143565

theorem tailTrace_3151921 : CollatzResearch.WordTrace tailWord_3151921 prefixEnd_3151921 179827828666674203143565 := by
  unfold tailWord_3151921
  simp only [CollatzResearch.WordTrace]
  refine ⟨114960003214135997095239617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76640002142757331396826411 114960003214135997095239617)
  ·
    refine ⟨86220002410601997821429713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114960003214135997095239617 86220002410601997821429713)
    ·
      refine ⟨64665001807951498366072285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86220002410601997821429713 64665001807951498366072285)
      ·
        refine ⟨24249375677981811887277107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64665001807951498366072285 24249375677981811887277107)
        ·
          refine ⟨36374063516972717830915661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24249375677981811887277107 36374063516972717830915661)
          ·
            refine ⟨13640273818864769186593373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36374063516972717830915661 13640273818864769186593373)
            ·
              refine ⟨5115102682074288444972515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13640273818864769186593373 5115102682074288444972515)
              ·
                refine ⟨7672654023111432667458773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5115102682074288444972515 7672654023111432667458773)
                ·
                  refine ⟨179827828666674203143565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7672654023111432667458773 179827828666674203143565)
                  ·
                    rfl

theorem cell23_3151921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 7].length) (baseStart_3151921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151921 prefixEnd_3151921 := by exact prefixLift 3151921
  have htrace : WordTrace (prefixWord ++ tailWord_3151921) baseStart_3151921 baseEnd_3151921 := by
    simpa [prefixWord, tailWord_3151921, baseEnd_3151921] using wordTrace_append hprefix tailTrace_3151921
  have hstable : (prefixWord ++ tailWord_3151921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151921).length < 2 ^ (prefixWord ++ tailWord_3151921).sum := by decide
  have hdescent : baseEnd_3151921 < baseStart_3151921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152005 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 4]
def baseStart_3152005 : Nat := 118140960795 + 3152005 * 2 ^ 59
def prefixEnd_3152005 : Nat := 4983230072969 + 3 ^ 40 * 3152005 * 2
def baseEnd_3152005 : Nat := 1618493590375045499641699

theorem tailTrace_3152005 : CollatzResearch.WordTrace tailWord_3152005 prefixEnd_3152005 1618493590375045499641699 := by
  unfold tailWord_3152005
  simp only [CollatzResearch.WordTrace]
  refine ⟨114963066945831679441297469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76642044630554452960864979 114963066945831679441297469)
  ·
    refine ⟨43111150104686879790486551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114963066945831679441297469 43111150104686879790486551)
    ·
      refine ⟨64666725157030319685729827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43111150104686879790486551 64666725157030319685729827)
      ·
        refine ⟨97000087735545479528594741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64666725157030319685729827 97000087735545479528594741)
        ·
          refine ⟨9093758225207388705805757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97000087735545479528594741 9093758225207388705805757)
          ·
            refine ⟨3410159334452770764677159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9093758225207388705805757 3410159334452770764677159)
            ·
              refine ⟨5115239001679156147015739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410159334452770764677159 5115239001679156147015739)
              ·
                refine ⟨7672858502518734220523609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5115239001679156147015739 7672858502518734220523609)
                ·
                  refine ⟨5754643876889050665392707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7672858502518734220523609 5754643876889050665392707)
                  ·
                    refine ⟨8631965815333575998089061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5754643876889050665392707 8631965815333575998089061)
                    ·
                      refine ⟨1618493590375045499641699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8631965815333575998089061 1618493590375045499641699)
                      ·
                        rfl

theorem cell23_3152005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_3152005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152005 prefixEnd_3152005 := by exact prefixLift 3152005
  have htrace : WordTrace (prefixWord ++ tailWord_3152005) baseStart_3152005 baseEnd_3152005 := by
    simpa [prefixWord, tailWord_3152005, baseEnd_3152005] using wordTrace_append hprefix tailTrace_3152005
  have hstable : (prefixWord ++ tailWord_3152005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152005).length < 2 ^ (prefixWord ++ tailWord_3152005).sum := by decide
  have hdescent : baseEnd_3152005 < baseStart_3152005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152055 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 3, 1, 3]
def baseStart_3152055 : Nat := 118140960795 + 3152055 * 2 ^ 59
def prefixEnd_3152055 : Nat := 4983230072969 + 3 ^ 40 * 3152055 * 2
def baseEnd_3152055 : Nat := 1618519264407770304016469

theorem tailTrace_3152055 : CollatzResearch.WordTrace tailWord_3152055 prefixEnd_3152055 1618519264407770304016469 := by
  unfold tailWord_3152055
  simp only [CollatzResearch.WordTrace]
  refine ⟨114964890595650537980617619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76643260397100358653745079 114964890595650537980617619)
  ·
    refine ⟨172447335893475806970926429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114964890595650537980617619 172447335893475806970926429)
    ·
      refine ⟨64667750960053427614097411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172447335893475806970926429 64667750960053427614097411)
      ·
        refine ⟨97001626440080141421146117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64667750960053427614097411 97001626440080141421146117)
        ·
          refine ⟨18187804957515026516464897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97001626440080141421146117 18187804957515026516464897)
          ·
            refine ⟨13640853718136269887348673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18187804957515026516464897 13640853718136269887348673)
            ·
              refine ⟨10230640288602202415511505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13640853718136269887348673 10230640288602202415511505)
              ·
                refine ⟨7672980216451651811633629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10230640288602202415511505 7672980216451651811633629)
                ·
                  refine ⟨2877367581169369429362611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7672980216451651811633629 2877367581169369429362611)
                  ·
                    refine ⟨4316051371754054144043917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2877367581169369429362611 4316051371754054144043917)
                    ·
                      refine ⟨1618519264407770304016469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4316051371754054144043917 1618519264407770304016469)
                      ·
                        rfl

theorem cell23_3152055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_3152055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152055 prefixEnd_3152055 := by exact prefixLift 3152055
  have htrace : WordTrace (prefixWord ++ tailWord_3152055) baseStart_3152055 baseEnd_3152055 := by
    simpa [prefixWord, tailWord_3152055, baseEnd_3152055] using wordTrace_append hprefix tailTrace_3152055
  have hstable : (prefixWord ++ tailWord_3152055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152055).length < 2 ^ (prefixWord ++ tailWord_3152055).sum := by decide
  have hdescent : baseEnd_3152055 < baseStart_3152055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152058 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 1, 5]
def baseStart_3152058 : Nat := 118140960795 + 3152058 * 2 ^ 59
def prefixEnd_3152058 : Nat := 4983230072969 + 3 ^ 40 * 3152058 * 2
def baseEnd_3152058 : Nat := 539506934949911264092985

theorem tailTrace_3152058 : CollatzResearch.WordTrace tailWord_3152058 prefixEnd_3152058 539506934949911264092985 := by
  unfold tailWord_3152058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28741250003659917373244207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76643333343093112995317885 28741250003659917373244207)
  ·
    refine ⟨43111875005489876059866311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28741250003659917373244207 43111875005489876059866311)
    ·
      refine ⟨64667812508234814089799467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43111875005489876059866311 64667812508234814089799467)
      ·
        refine ⟨97001718762352221134699201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64667812508234814089799467 97001718762352221134699201)
        ·
          refine ⟨72751289071764165851024401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97001718762352221134699201 72751289071764165851024401)
          ·
            refine ⟨54563466803823124388268301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72751289071764165851024401 54563466803823124388268301)
            ·
              refine ⟨20461300051433671645600613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54563466803823124388268301 20461300051433671645600613)
              ·
                refine ⟨3836493759643813433550115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20461300051433671645600613 3836493759643813433550115)
                ·
                  refine ⟨5754740639465720150325173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836493759643813433550115 5754740639465720150325173)
                  ·
                    refine ⟨539506934949911264092985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5754740639465720150325173 539506934949911264092985)
                    ·
                      rfl

theorem cell23_3152058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_3152058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152058 prefixEnd_3152058 := by exact prefixLift 3152058
  have htrace : WordTrace (prefixWord ++ tailWord_3152058) baseStart_3152058 baseEnd_3152058 := by
    simpa [prefixWord, tailWord_3152058, baseEnd_3152058] using wordTrace_append hprefix tailTrace_3152058
  have hstable : (prefixWord ++ tailWord_3152058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152058).length < 2 ^ (prefixWord ++ tailWord_3152058).sum := by decide
  have hdescent : baseEnd_3152058 < baseStart_3152058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152066 : List Nat := [3, 5, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3152066 : Nat := 118140960795 + 3152066 * 2 ^ 59
def prefixEnd_3152066 : Nat := 4983230072969 + 3 ^ 40 * 3152066 * 2
def baseEnd_3152066 : Nat := 539508304231656586992973

theorem tailTrace_3152066 : CollatzResearch.WordTrace tailWord_3152066 prefixEnd_3152066 539508304231656586992973 := by
  unfold tailWord_3152066
  simp only [CollatzResearch.WordTrace]
  refine ⟨28741322949652671714817013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76643527865740457906178701 28741322949652671714817013)
  ·
    refine ⟨2694499026529937973264095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28741322949652671714817013 2694499026529937973264095)
    ·
      refine ⟨4041748539794906959896143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2694499026529937973264095 4041748539794906959896143)
      ·
        refine ⟨6062622809692360439844215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4041748539794906959896143 6062622809692360439844215)
        ·
          refine ⟨9093934214538540659766323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6062622809692360439844215 9093934214538540659766323)
          ·
            refine ⟨13640901321807810989649485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9093934214538540659766323 13640901321807810989649485)
            ·
              refine ⟨5115337995677929121118557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13640901321807810989649485 5115337995677929121118557)
              ·
                refine ⟨1918251748379223420419459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5115337995677929121118557 1918251748379223420419459)
                ·
                  refine ⟨2877377622568835130629189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918251748379223420419459 2877377622568835130629189)
                  ·
                    refine ⟨539508304231656586992973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2877377622568835130629189 539508304231656586992973)
                    ·
                      rfl

theorem cell23_3152066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3152066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152066 prefixEnd_3152066 := by exact prefixLift 3152066
  have htrace : WordTrace (prefixWord ++ tailWord_3152066) baseStart_3152066 baseEnd_3152066 := by
    simpa [prefixWord, tailWord_3152066, baseEnd_3152066] using wordTrace_append hprefix tailTrace_3152066
  have hstable : (prefixWord ++ tailWord_3152066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152066).length < 2 ^ (prefixWord ++ tailWord_3152066).sum := by decide
  have hdescent : baseEnd_3152066 < baseStart_3152066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152082 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_3152082 : Nat := 118140960795 + 3152082 * 2 ^ 59
def prefixEnd_3152082 : Nat := 4983230072969 + 3 ^ 40 * 3152082 * 2
def baseEnd_3152082 : Nat := 1618533128385441698378845

theorem tailTrace_3152082 : CollatzResearch.WordTrace tailWord_3152082 prefixEnd_3152082 1618533128385441698378845 := by
  unfold tailWord_3152082
  simp only [CollatzResearch.WordTrace]
  refine ⟨28741468841638180397962625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76643916911035147727900333 28741468841638180397962625)
  ·
    refine ⟨21556101631228635298471969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28741468841638180397962625 21556101631228635298471969)
    ·
      refine ⟨16167076223421476473853977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21556101631228635298471969 16167076223421476473853977)
      ·
        refine ⟨12125307167566107355390483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16167076223421476473853977 12125307167566107355390483)
        ·
          refine ⟨18187960751349161033085725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12125307167566107355390483 18187960751349161033085725)
          ·
            refine ⟨6820485281755935387407147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18187960751349161033085725 6820485281755935387407147)
            ·
              refine ⟨10230727922633903081110721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6820485281755935387407147 10230727922633903081110721)
              ·
                refine ⟨7673045941975427310833041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10230727922633903081110721 7673045941975427310833041)
                ·
                  refine ⟨5754784456481570483124781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7673045941975427310833041 5754784456481570483124781)
                  ·
                    refine ⟨2158044171180588931171793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5754784456481570483124781 2158044171180588931171793)
                    ·
                      refine ⟨1618533128385441698378845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158044171180588931171793 1618533128385441698378845)
                      ·
                        rfl

theorem cell23_3152082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_3152082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152082 prefixEnd_3152082 := by exact prefixLift 3152082
  have htrace : WordTrace (prefixWord ++ tailWord_3152082) baseStart_3152082 baseEnd_3152082 := by
    simpa [prefixWord, tailWord_3152082, baseEnd_3152082] using wordTrace_append hprefix tailTrace_3152082
  have hstable : (prefixWord ++ tailWord_3152082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152082).length < 2 ^ (prefixWord ++ tailWord_3152082).sum := by decide
  have hdescent : baseEnd_3152082 < baseStart_3152082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152091 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 6]
def baseStart_3152091 : Nat := 118140960795 + 3152091 * 2 ^ 59
def prefixEnd_3152091 : Nat := 4983230072969 + 3 ^ 40 * 3152091 * 2
def baseEnd_3152091 : Nat := 1618537749711332163166303

theorem tailTrace_3152091 : CollatzResearch.WordTrace tailWord_3152091 prefixEnd_3152091 1618537749711332163166303 := by
  unfold tailWord_3152091
  simp only [CollatzResearch.WordTrace]
  refine ⟨114966203623520116128928127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76644135749013410752618751 114966203623520116128928127)
  ·
    refine ⟨172449305435280174193392191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114966203623520116128928127 172449305435280174193392191)
    ·
      refine ⟨258673958152920261290088287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172449305435280174193392191 258673958152920261290088287)
      ·
        refine ⟨388010937229380391935132431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258673958152920261290088287 388010937229380391935132431)
        ·
          refine ⟨582016405844070587902698647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388010937229380391935132431 582016405844070587902698647)
          ·
            refine ⟨873024608766105881854047971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582016405844070587902698647 873024608766105881854047971)
            ·
              refine ⟨1309536913149158822781071957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873024608766105881854047971 1309536913149158822781071957)
              ·
                refine ⟨15346135700966704954465687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1309536913149158822781071957 15346135700966704954465687)
                ·
                  refine ⟨23019203551450057431698531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15346135700966704954465687 23019203551450057431698531)
                  ·
                    refine ⟨34528805327175086147547797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23019203551450057431698531 34528805327175086147547797)
                    ·
                      refine ⟨1618537749711332163166303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34528805327175086147547797 1618537749711332163166303)
                      ·
                        rfl

theorem cell23_3152091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 6].length) (baseStart_3152091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152091 prefixEnd_3152091 := by exact prefixLift 3152091
  have htrace : WordTrace (prefixWord ++ tailWord_3152091) baseStart_3152091 baseEnd_3152091 := by
    simpa [prefixWord, tailWord_3152091, baseEnd_3152091] using wordTrace_append hprefix tailTrace_3152091
  have hstable : (prefixWord ++ tailWord_3152091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152091).length < 2 ^ (prefixWord ++ tailWord_3152091).sum := by decide
  have hdescent : baseEnd_3152091 < baseStart_3152091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152108 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_3152108 : Nat := 118140960795 + 3152108 * 2 ^ 59
def prefixEnd_3152108 : Nat := 4983230072969 + 3 ^ 40 * 3152108 * 2
def baseEnd_3152108 : Nat := 1618546478882458596653725

theorem tailTrace_3152108 : CollatzResearch.WordTrace tailWord_3152108 prefixEnd_3152108 1618546478882458596653725 := by
  unfold tailWord_3152108
  simp only [CollatzResearch.WordTrace]
  refine ⟨57483411832229264016148489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76644549109639018688197985 57483411832229264016148489)
  ·
    refine ⟨43112558874171948012111367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57483411832229264016148489 43112558874171948012111367)
    ·
      refine ⟨64668838311257922018167051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43112558874171948012111367 64668838311257922018167051)
      ·
        refine ⟨97003257466886883027250577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64668838311257922018167051 97003257466886883027250577)
        ·
          refine ⟨72752443100165162270437933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97003257466886883027250577 72752443100165162270437933)
          ·
            refine ⟨27282166162561935851414225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72752443100165162270437933 27282166162561935851414225)
            ·
              refine ⟨20461624621921451888560669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27282166162561935851414225 20461624621921451888560669)
              ·
                refine ⟨7673109233220544458210251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20461624621921451888560669 7673109233220544458210251)
                ·
                  refine ⟨11509663849830816687315377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7673109233220544458210251 11509663849830816687315377)
                  ·
                    refine ⟨8632247887373112515486533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11509663849830816687315377 8632247887373112515486533)
                    ·
                      refine ⟨1618546478882458596653725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8632247887373112515486533 1618546478882458596653725)
                      ·
                        rfl

theorem cell23_3152108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_3152108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152108 prefixEnd_3152108 := by exact prefixLift 3152108
  have htrace : WordTrace (prefixWord ++ tailWord_3152108) baseStart_3152108 baseEnd_3152108 := by
    simpa [prefixWord, tailWord_3152108, baseEnd_3152108] using wordTrace_append hprefix tailTrace_3152108
  have hstable : (prefixWord ++ tailWord_3152108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152108).length < 2 ^ (prefixWord ++ tailWord_3152108).sum := by decide
  have hdescent : baseEnd_3152108 < baseStart_3152108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152109 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_3152109 : Nat := 118140960795 + 3152109 * 2 ^ 59
def prefixEnd_3152109 : Nat := 4983230072969 + 3 ^ 40 * 3152109 * 2
def baseEnd_3152109 : Nat := 539515664121037697580407

theorem tailTrace_3152109 : CollatzResearch.WordTrace tailWord_3152109 prefixEnd_3152109 539515664121037697580407 := by
  unfold tailWord_3152109
  simp only [CollatzResearch.WordTrace]
  refine ⟨114966860137454905203083381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76644573424969936802055587 114966860137454905203083381)
  ·
    refine ⟨10778143137886397362789067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114966860137454905203083381 10778143137886397362789067)
    ·
      refine ⟨16167214706829596044183601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10778143137886397362789067 16167214706829596044183601)
      ·
        refine ⟨12125411030122197033137701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16167214706829596044183601 12125411030122197033137701)
        ·
          refine ⟨2273514568147911943713319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12125411030122197033137701 2273514568147911943713319)
          ·
            refine ⟨3410271852221867915569979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273514568147911943713319 3410271852221867915569979)
            ·
              refine ⟨5115407778332801873354969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410271852221867915569979 5115407778332801873354969)
              ·
                refine ⟨3836555833749601405016227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5115407778332801873354969 3836555833749601405016227)
                ·
                  refine ⟨5754833750624402107524341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836555833749601405016227 5754833750624402107524341)
                  ·
                    refine ⟨539515664121037697580407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5754833750624402107524341 539515664121037697580407)
                    ·
                      rfl

theorem cell23_3152109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_3152109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152109 prefixEnd_3152109 := by exact prefixLift 3152109
  have htrace : WordTrace (prefixWord ++ tailWord_3152109) baseStart_3152109 baseEnd_3152109 := by
    simpa [prefixWord, tailWord_3152109, baseEnd_3152109] using wordTrace_append hprefix tailTrace_3152109
  have hstable : (prefixWord ++ tailWord_3152109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152109).length < 2 ^ (prefixWord ++ tailWord_3152109).sum := by decide
  have hdescent : baseEnd_3152109 < baseStart_3152109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152118 : List Nat := [5, 1, 1, 1, 1, 1, 4, 9]
def baseStart_3152118 : Nat := 118140960795 + 3152118 * 2 ^ 59
def prefixEnd_3152118 : Nat := 4983230072969 + 3 ^ 40 * 3152118 * 2
def baseEnd_3152118 : Nat := 59946356062555687315877

theorem tailTrace_3152118 : CollatzResearch.WordTrace tailWord_3152118 prefixEnd_3152118 59946356062555687315877 := by
  unfold tailWord_3152118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7185449274651393733760063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76644792262948199826774005 7185449274651393733760063)
  ·
    refine ⟨10778173911977090600640095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7185449274651393733760063 10778173911977090600640095)
    ·
      refine ⟨16167260867965635900960143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10778173911977090600640095 16167260867965635900960143)
      ·
        refine ⟨24250891301948453851440215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16167260867965635900960143 24250891301948453851440215)
        ·
          refine ⟨36376336952922680777160323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24250891301948453851440215 36376336952922680777160323)
          ·
            refine ⟨54564505429384021165740485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36376336952922680777160323 54564505429384021165740485)
            ·
              refine ⟨10230844768009503968576341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54564505429384021165740485 10230844768009503968576341)
              ·
                refine ⟨59946356062555687315877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10230844768009503968576341 59946356062555687315877)
                ·
                  rfl

theorem cell23_3152118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_3152118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152118 prefixEnd_3152118 := by exact prefixLift 3152118
  have htrace : WordTrace (prefixWord ++ tailWord_3152118) baseStart_3152118 baseEnd_3152118 := by
    simpa [prefixWord, tailWord_3152118, baseEnd_3152118] using wordTrace_append hprefix tailTrace_3152118
  have hstable : (prefixWord ++ tailWord_3152118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152118).length < 2 ^ (prefixWord ++ tailWord_3152118).sum := by decide
  have hdescent : baseEnd_3152118 < baseStart_3152118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152128 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 3]
def baseStart_3152128 : Nat := 118140960795 + 3152128 * 2 ^ 59
def prefixEnd_3152128 : Nat := 4983230072969 + 3 ^ 40 * 3152128 * 2
def baseEnd_3152128 : Nat := 1618556748495548518403633

theorem tailTrace_3152128 : CollatzResearch.WordTrace tailWord_3152128 prefixEnd_3152128 1618556748495548518403633 := by
  unfold tailWord_3152128
  simp only [CollatzResearch.WordTrace]
  refine ⟨57483776562193035724012519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76645035416257380965350025 57483776562193035724012519)
  ·
    refine ⟨86225664843289553586018779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57483776562193035724012519 86225664843289553586018779)
    ·
      refine ⟨129338497264934330379028169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86225664843289553586018779 129338497264934330379028169)
      ·
        refine ⟨97003872948700747784271127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129338497264934330379028169 97003872948700747784271127)
        ·
          refine ⟨145505809423051121676406691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97003872948700747784271127 145505809423051121676406691)
          ·
            refine ⟨218258714134576682514610037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145505809423051121676406691 218258714134576682514610037)
            ·
              refine ⟨20461754450116563985744691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218258714134576682514610037 20461754450116563985744691)
              ·
                refine ⟨30692631675174845978617037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20461754450116563985744691 30692631675174845978617037)
                ·
                  refine ⟨11509736878190567241981389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30692631675174845978617037 11509736878190567241981389)
                  ·
                    refine ⟨4316151329321462715743021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11509736878190567241981389 4316151329321462715743021)
                    ·
                      refine ⟨1618556748495548518403633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4316151329321462715743021 1618556748495548518403633)
                      ·
                        rfl

theorem cell23_3152128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_3152128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152128 prefixEnd_3152128 := by exact prefixLift 3152128
  have htrace : WordTrace (prefixWord ++ tailWord_3152128) baseStart_3152128 baseEnd_3152128 := by
    simpa [prefixWord, tailWord_3152128, baseEnd_3152128] using wordTrace_append hprefix tailTrace_3152128
  have hstable : (prefixWord ++ tailWord_3152128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152128).length < 2 ^ (prefixWord ++ tailWord_3152128).sum := by decide
  have hdescent : baseEnd_3152128 < baseStart_3152128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152129 : List Nat := [1, 2, 4, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_3152129 : Nat := 118140960795 + 3152129 * 2 ^ 59
def prefixEnd_3152129 : Nat := 4983230072969 + 3 ^ 40 * 3152129 * 2
def baseEnd_3152129 : Nat := 1618557261976203014491129

theorem tailTrace_3152129 : CollatzResearch.WordTrace tailWord_3152129 prefixEnd_3152129 1618557261976203014491129 := by
  unfold tailWord_3152129
  simp only [CollatzResearch.WordTrace]
  refine ⟨114967589597382448618811441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76645059731588299079207627 114967589597382448618811441)
  ·
    refine ⟨86225692198036836464108581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114967589597382448618811441 86225692198036836464108581)
    ·
      refine ⟨16167317287131906837020359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86225692198036836464108581 16167317287131906837020359)
      ·
        refine ⟨24250975930697860255530539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16167317287131906837020359 24250975930697860255530539)
        ·
          refine ⟨36376463896046790383295809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24250975930697860255530539 36376463896046790383295809)
          ·
            refine ⟨27282347922035092787471857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36376463896046790383295809 27282347922035092787471857)
            ·
              refine ⟨20461760941526319590603893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27282347922035092787471857 20461760941526319590603893)
              ·
                refine ⟨1918290088268092461619115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20461760941526319590603893 1918290088268092461619115)
                ·
                  refine ⟨2877435132402138692428673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918290088268092461619115 2877435132402138692428673)
                  ·
                    refine ⟨2158076349301604019321505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2877435132402138692428673 2158076349301604019321505)
                    ·
                      refine ⟨1618557261976203014491129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158076349301604019321505 1618557261976203014491129)
                      ·
                        rfl

theorem cell23_3152129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_3152129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152129 prefixEnd_3152129 := by exact prefixLift 3152129
  have htrace : WordTrace (prefixWord ++ tailWord_3152129) baseStart_3152129 baseEnd_3152129 := by
    simpa [prefixWord, tailWord_3152129, baseEnd_3152129] using wordTrace_append hprefix tailTrace_3152129
  have hstable : (prefixWord ++ tailWord_3152129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152129).length < 2 ^ (prefixWord ++ tailWord_3152129).sum := by decide
  have hdescent : baseEnd_3152129 < baseStart_3152129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152132 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_3152132 : Nat := 118140960795 + 3152132 * 2 ^ 59
def prefixEnd_3152132 : Nat := 4983230072969 + 3 ^ 40 * 3152132 * 2
def baseEnd_3152132 : Nat := 1618558802418166502753615

theorem tailTrace_3152132 : CollatzResearch.WordTrace tailWord_3152132 prefixEnd_3152132 1618558802418166502753615 := by
  unfold tailWord_3152132
  simp only [CollatzResearch.WordTrace]
  refine ⟨57483849508185790065585325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76645132677581053420780433 57483849508185790065585325)
  ·
    refine ⟨21556443565569671274594497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57483849508185790065585325 21556443565569671274594497)
    ·
      refine ⟨16167332674177253455945873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21556443565569671274594497 16167332674177253455945873)
      ·
        refine ⟨12125499505632940091959405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16167332674177253455945873 12125499505632940091959405)
        ·
          refine ⟨4547062314612352534484777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12125499505632940091959405 4547062314612352534484777)
          ·
            refine ⟨3410296735959264400863583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4547062314612352534484777 3410296735959264400863583)
            ·
              refine ⟨5115445103938896601295375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410296735959264400863583 5115445103938896601295375)
              ·
                refine ⟨7673167655908344901943063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5115445103938896601295375 7673167655908344901943063)
                ·
                  refine ⟨11509751483862517352914595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7673167655908344901943063 11509751483862517352914595)
                  ·
                    refine ⟨17264627225793776029371893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11509751483862517352914595 17264627225793776029371893)
                    ·
                      refine ⟨1618558802418166502753615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17264627225793776029371893 1618558802418166502753615)
                      ·
                        rfl

theorem cell23_3152132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_3152132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152132 prefixEnd_3152132 := by exact prefixLift 3152132
  have htrace : WordTrace (prefixWord ++ tailWord_3152132) baseStart_3152132 baseEnd_3152132 := by
    simpa [prefixWord, tailWord_3152132, baseEnd_3152132] using wordTrace_append hprefix tailTrace_3152132
  have hstable : (prefixWord ++ tailWord_3152132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152132).length < 2 ^ (prefixWord ++ tailWord_3152132).sum := by decide
  have hdescent : baseEnd_3152132 < baseStart_3152132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152135 : List Nat := [1, 1, 4, 5, 2, 10]
def baseStart_3152135 : Nat := 118140960795 + 3152135 * 2 ^ 59
def prefixEnd_3152135 : Nat := 4983230072969 + 3 ^ 40 * 3152135 * 2
def baseEnd_3152135 : Nat := 6660742151687777740807

theorem tailTrace_3152135 : CollatzResearch.WordTrace tailWord_3152135 prefixEnd_3152135 6660742151687777740807 := by
  unfold tailWord_3152135
  simp only [CollatzResearch.WordTrace]
  refine ⟨114967808435360711643529859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76645205623573807762353239 114967808435360711643529859)
  ·
    refine ⟨172451712653041067465294789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114967808435360711643529859 172451712653041067465294789)
    ·
      refine ⟨32334696122445200149742773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172451712653041067465294789 32334696122445200149742773)
      ·
        refine ⟨3031377761479237514038385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32334696122445200149742773 3031377761479237514038385)
        ·
          refine ⟨2273533321109428135528789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3031377761479237514038385 2273533321109428135528789)
          ·
            refine ⟨6660742151687777740807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2273533321109428135528789 6660742151687777740807)
            ·
              rfl

theorem cell23_3152135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 10].length) (baseStart_3152135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152135 prefixEnd_3152135 := by exact prefixLift 3152135
  have htrace : WordTrace (prefixWord ++ tailWord_3152135) baseStart_3152135 baseEnd_3152135 := by
    simpa [prefixWord, tailWord_3152135, baseEnd_3152135] using wordTrace_append hprefix tailTrace_3152135
  have hstable : (prefixWord ++ tailWord_3152135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152135).length < 2 ^ (prefixWord ++ tailWord_3152135).sum := by decide
  have hdescent : baseEnd_3152135 < baseStart_3152135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152155 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 3, 3, 2]
def baseStart_3152155 : Nat := 118140960795 + 3152155 * 2 ^ 59
def prefixEnd_3152155 : Nat := 4983230072969 + 3 ^ 40 * 3152155 * 2
def baseEnd_3152155 : Nat := 1618570612473219912766009

theorem tailTrace_3152155 : CollatzResearch.WordTrace tailWord_3152155 prefixEnd_3152155 1618570612473219912766009 := by
  unfold tailWord_3152155
  simp only [CollatzResearch.WordTrace]
  refine ⟨114968537895288255059257919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76645691930192170039505279 114968537895288255059257919)
  ·
    refine ⟨172452806842932382588886879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114968537895288255059257919 172452806842932382588886879)
    ·
      refine ⟨258679210264398573883330319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172452806842932382588886879 258679210264398573883330319)
      ·
        refine ⟨388018815396597860824995479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258679210264398573883330319 388018815396597860824995479)
        ·
          refine ⟨582028223094896791237493219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388018815396597860824995479 582028223094896791237493219)
          ·
            refine ⟨873042334642345186856239829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582028223094896791237493219 873042334642345186856239829)
            ·
              refine ⟨20461929718179965316943121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 873042334642345186856239829 20461929718179965316943121)
              ·
                refine ⟨15346447288634973987707341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20461929718179965316943121 15346447288634973987707341)
                ·
                  refine ⟨5754917733238115245390253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15346447288634973987707341 5754917733238115245390253)
                  ·
                    refine ⟨2158094149964293217021345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5754917733238115245390253 2158094149964293217021345)
                    ·
                      refine ⟨1618570612473219912766009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158094149964293217021345 1618570612473219912766009)
                      ·
                        rfl

theorem cell23_3152155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 3, 2].length) (baseStart_3152155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152155 prefixEnd_3152155 := by exact prefixLift 3152155
  have htrace : WordTrace (prefixWord ++ tailWord_3152155) baseStart_3152155 baseEnd_3152155 := by
    simpa [prefixWord, tailWord_3152155, baseEnd_3152155] using wordTrace_append hprefix tailTrace_3152155
  have hstable : (prefixWord ++ tailWord_3152155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152155).length < 2 ^ (prefixWord ++ tailWord_3152155).sum := by decide
  have hdescent : baseEnd_3152155 < baseStart_3152155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152162 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_3152162 : Nat := 118140960795 + 3152162 * 2 ^ 59
def prefixEnd_3152162 : Nat := 4983230072969 + 3 ^ 40 * 3152162 * 2
def baseEnd_3152162 : Nat := 1618574206837801385378477

theorem tailTrace_3152162 : CollatzResearch.WordTrace tailWord_3152162 prefixEnd_3152162 1618574206837801385378477 := by
  unfold tailWord_3152162
  simp only [CollatzResearch.WordTrace]
  refine ⟨28742198301565723813690685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76645862137508596836508493 28742198301565723813690685)
  ·
    refine ⟨10778324363087146430134007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28742198301565723813690685 10778324363087146430134007)
    ·
      refine ⟨16167486544630719645201011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10778324363087146430134007 16167486544630719645201011)
      ·
        refine ⟨24251229816946079467801517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16167486544630719645201011 24251229816946079467801517)
        ·
          refine ⟨9094211181354779800425569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24251229816946079467801517 9094211181354779800425569)
          ·
            refine ⟨6820658386016084850319177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9094211181354779800425569 6820658386016084850319177)
            ·
              refine ⟨5115493789512063637739383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6820658386016084850319177 5115493789512063637739383)
              ·
                refine ⟨7673240684268095456609075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5115493789512063637739383 7673240684268095456609075)
                ·
                  refine ⟨11509861026402143184913613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7673240684268095456609075 11509861026402143184913613)
                  ·
                    refine ⟨4316197884900803694342605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11509861026402143184913613 4316197884900803694342605)
                    ·
                      refine ⟨1618574206837801385378477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4316197884900803694342605 1618574206837801385378477)
                      ·
                        rfl

theorem cell23_3152162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_3152162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152162 prefixEnd_3152162 := by exact prefixLift 3152162
  have htrace : WordTrace (prefixWord ++ tailWord_3152162) baseStart_3152162 baseEnd_3152162 := by
    simpa [prefixWord, tailWord_3152162, baseEnd_3152162] using wordTrace_append hprefix tailTrace_3152162
  have hstable : (prefixWord ++ tailWord_3152162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152162).length < 2 ^ (prefixWord ++ tailWord_3152162).sum := by decide
  have hdescent : baseEnd_3152162 < baseStart_3152162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152188 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_3152188 : Nat := 118140960795 + 3152188 * 2 ^ 59
def prefixEnd_3152188 : Nat := 4983230072969 + 3 ^ 40 * 3152188 * 2
def baseEnd_3152188 : Nat := 1618587557334818283653357

theorem tailTrace_3152188 : CollatzResearch.WordTrace tailWord_3152188 prefixEnd_3152188 1618587557334818283653357 := by
  unfold tailWord_3152188
  simp only [CollatzResearch.WordTrace]
  refine ⟨57484870752084350847604609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76646494336112467796806145 57484870752084350847604609)
  ·
    refine ⟨43113653064063263135703457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57484870752084350847604609 43113653064063263135703457)
    ·
      refine ⟨32335239798047447351777593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43113653064063263135703457 32335239798047447351777593)
      ·
        refine ⟨24251429848535585513833195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32335239798047447351777593 24251429848535585513833195)
        ·
          refine ⟨36377144772803378270749793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24251429848535585513833195 36377144772803378270749793)
          ·
            refine ⟨27282858579602533703062345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36377144772803378270749793 27282858579602533703062345)
            ·
              refine ⟨20462143934701900277296759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27282858579602533703062345 20462143934701900277296759)
              ·
                refine ⟨30693215902052850415945139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20462143934701900277296759 30693215902052850415945139)
                ·
                  refine ⟨46039823853079275623917709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30693215902052850415945139 46039823853079275623917709)
                  ·
                    refine ⟨17264933944904728358969141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46039823853079275623917709 17264933944904728358969141)
                    ·
                      refine ⟨1618587557334818283653357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17264933944904728358969141 1618587557334818283653357)
                      ·
                        rfl

theorem cell23_3152188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_3152188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152188 prefixEnd_3152188 := by exact prefixLift 3152188
  have htrace : WordTrace (prefixWord ++ tailWord_3152188) baseStart_3152188 baseEnd_3152188 := by
    simpa [prefixWord, tailWord_3152188, baseEnd_3152188] using wordTrace_append hprefix tailTrace_3152188
  have hstable : (prefixWord ++ tailWord_3152188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152188).length < 2 ^ (prefixWord ++ tailWord_3152188).sum := by decide
  have hdescent : baseEnd_3152188 < baseStart_3152188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152208 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 7]
def baseStart_3152208 : Nat := 118140960795 + 3152208 * 2 ^ 59
def prefixEnd_3152208 : Nat := 4983230072969 + 3 ^ 40 * 3152208 * 2
def baseEnd_3152208 : Nat := 179844202994212022822585

theorem tailTrace_3152208 : CollatzResearch.WordTrace tailWord_3152208 prefixEnd_3152208 179844202994212022822585 := by
  unfold tailWord_3152208
  simp only [CollatzResearch.WordTrace]
  refine ⟨57485235482048122555468639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76646980642730830073958185 57485235482048122555468639)
  ·
    refine ⟨86227853223072183833202959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57485235482048122555468639 86227853223072183833202959)
    ·
      refine ⟨129341779834608275749804439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86227853223072183833202959 129341779834608275749804439)
      ·
        refine ⟨194012669751912413624706659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129341779834608275749804439 194012669751912413624706659)
        ·
          refine ⟨291019004627868620437059989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194012669751912413624706659 291019004627868620437059989)
          ·
            refine ⟨13641515841931341582987187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 291019004627868620437059989 13641515841931341582987187)
            ·
              refine ⟨20462273762897012374480781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13641515841931341582987187 20462273762897012374480781)
              ·
                refine ⟨7673352661086379640430293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20462273762897012374480781 7673352661086379640430293)
                ·
                  refine ⟨179844202994212022822585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7673352661086379640430293 179844202994212022822585)
                  ·
                    rfl

theorem cell23_3152208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 7].length) (baseStart_3152208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152208 prefixEnd_3152208 := by exact prefixLift 3152208
  have htrace : WordTrace (prefixWord ++ tailWord_3152208) baseStart_3152208 baseEnd_3152208 := by
    simpa [prefixWord, tailWord_3152208, baseEnd_3152208] using wordTrace_append hprefix tailTrace_3152208
  have hstable : (prefixWord ++ tailWord_3152208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152208).length < 2 ^ (prefixWord ++ tailWord_3152208).sum := by decide
  have hdescent : baseEnd_3152208 < baseStart_3152208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152242 : List Nat := [3, 2, 1, 2, 1, 3, 3, 3, 5]
def baseStart_3152242 : Nat := 118140960795 + 3152242 * 2 ^ 59
def prefixEnd_3152242 : Nat := 4983230072969 + 3 ^ 40 * 3152242 * 2
def baseEnd_3152242 : Nat := 179846142810017896930901

theorem tailTrace_3152242 : CollatzResearch.WordTrace tailWord_3152242 prefixEnd_3152242 179846142810017896930901 := by
  unfold tailWord_3152242
  simp only [CollatzResearch.WordTrace]
  refine ⟨28742927761493267229418745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76647807363982045945116653 28742927761493267229418745)
  ·
    refine ⟨21557195821119950422064059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28742927761493267229418745 21557195821119950422064059)
    ·
      refine ⟨32335793731679925633096089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21557195821119950422064059 32335793731679925633096089)
      ·
        refine ⟨24251845298759944224822067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32335793731679925633096089 24251845298759944224822067)
        ·
          refine ⟨36377767948139916337233101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24251845298759944224822067 36377767948139916337233101)
          ·
            refine ⟨13641662980552468626462413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36377767948139916337233101 13641662980552468626462413)
            ·
              refine ⟨5115623617707175734923405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13641662980552468626462413 5115623617707175734923405)
              ·
                refine ⟨1918358856640190900596277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5115623617707175734923405 1918358856640190900596277)
                ·
                  refine ⟨179846142810017896930901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1918358856640190900596277 179846142810017896930901)
                  ·
                    rfl

theorem cell23_3152242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_3152242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152242 prefixEnd_3152242 := by exact prefixLift 3152242
  have htrace : WordTrace (prefixWord ++ tailWord_3152242) baseStart_3152242 baseEnd_3152242 := by
    simpa [prefixWord, tailWord_3152242, baseEnd_3152242] using wordTrace_append hprefix tailTrace_3152242
  have hstable : (prefixWord ++ tailWord_3152242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152242).length < 2 ^ (prefixWord ++ tailWord_3152242).sum := by decide
  have hdescent : baseEnd_3152242 < baseStart_3152242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152259 : List Nat := [1, 1, 1, 3, 6, 1, 3, 2, 5]
def baseStart_3152259 : Nat := 118140960795 + 3152259 * 2 ^ 59
def prefixEnd_3152259 : Nat := 4983230072969 + 3 ^ 40 * 3152259 * 2
def baseEnd_3152259 : Nat := 179847112717920833985059

theorem tailTrace_3152259 : CollatzResearch.WordTrace tailWord_3152259 prefixEnd_3152259 179847112717920833985059 := by
  unfold tailWord_3152259
  simp only [CollatzResearch.WordTrace]
  refine ⟨114972331086911480821043831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76648220724607653880695887 114972331086911480821043831)
  ·
    refine ⟨172458496630367221231565747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114972331086911480821043831 172458496630367221231565747)
    ·
      refine ⟨258687744945550831847348621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172458496630367221231565747 258687744945550831847348621)
      ·
        refine ⟨97007904354581561942755733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258687744945550831847348621 97007904354581561942755733)
        ·
          refine ⟨4547245516621010716066675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97007904354581561942755733 4547245516621010716066675)
          ·
            refine ⟨6820868274931516074100013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4547245516621010716066675 6820868274931516074100013)
            ·
              refine ⟨2557825603099318527787505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6820868274931516074100013 2557825603099318527787505)
              ·
                refine ⟨1918369202324488895840629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2557825603099318527787505 1918369202324488895840629)
                ·
                  refine ⟨179847112717920833985059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1918369202324488895840629 179847112717920833985059)
                  ·
                    rfl

theorem cell23_3152259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 5].length) (baseStart_3152259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152259 prefixEnd_3152259 := by exact prefixLift 3152259
  have htrace : WordTrace (prefixWord ++ tailWord_3152259) baseStart_3152259 baseEnd_3152259 := by
    simpa [prefixWord, tailWord_3152259, baseEnd_3152259] using wordTrace_append hprefix tailTrace_3152259
  have hstable : (prefixWord ++ tailWord_3152259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152259).length < 2 ^ (prefixWord ++ tailWord_3152259).sum := by decide
  have hdescent : baseEnd_3152259 < baseStart_3152259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152265 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 5]
def baseStart_3152265 : Nat := 118140960795 + 3152265 * 2 ^ 59
def prefixEnd_3152265 : Nat := 4983230072969 + 3 ^ 40 * 3152265 * 2
def baseEnd_3152265 : Nat := 1618627095345214482390503

theorem tailTrace_3152265 : CollatzResearch.WordTrace tailWord_3152265 prefixEnd_3152265 1618627095345214482390503 := by
  unfold tailWord_3152265
  simp only [CollatzResearch.WordTrace]
  refine ⟨114972549924889743845762249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76648366616593162563841499 114972549924889743845762249)
  ·
    refine ⟨86229412443667307884321687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114972549924889743845762249 86229412443667307884321687)
    ·
      refine ⟨129344118665500961826482531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86229412443667307884321687 129344118665500961826482531)
      ·
        refine ⟨194016177998251442739723797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129344118665500961826482531 194016177998251442739723797)
        ·
          refine ⟨9094508343668036378424553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 194016177998251442739723797 9094508343668036378424553)
          ·
            refine ⟨6820881257751027283818415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9094508343668036378424553 6820881257751027283818415)
            ·
              refine ⟨10231321886626540925727623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6820881257751027283818415 10231321886626540925727623)
              ·
                refine ⟨15346982829939811388591435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10231321886626540925727623 15346982829939811388591435)
                ·
                  refine ⟨23020474244909717082887153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15346982829939811388591435 23020474244909717082887153)
                  ·
                    refine ⟨17265355683682287812165365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23020474244909717082887153 17265355683682287812165365)
                    ·
                      refine ⟨1618627095345214482390503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17265355683682287812165365 1618627095345214482390503)
                      ·
                        rfl

theorem cell23_3152265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_3152265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152265 prefixEnd_3152265 := by exact prefixLift 3152265
  have htrace : WordTrace (prefixWord ++ tailWord_3152265) baseStart_3152265 baseEnd_3152265 := by
    simpa [prefixWord, tailWord_3152265, baseEnd_3152265] using wordTrace_append hprefix tailTrace_3152265
  have hstable : (prefixWord ++ tailWord_3152265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152265).length < 2 ^ (prefixWord ++ tailWord_3152265).sum := by decide
  have hdescent : baseEnd_3152265 < baseStart_3152265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152289 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 2, 5]
def baseStart_3152289 : Nat := 118140960795 + 3152289 * 2 ^ 59
def prefixEnd_3152289 : Nat := 4983230072969 + 3 ^ 40 * 3152289 * 2
def baseEnd_3152289 : Nat := 539546472960307462830131

theorem tailTrace_3152289 : CollatzResearch.WordTrace tailWord_3152289 prefixEnd_3152289 539546472960307462830131 := by
  unfold tailWord_3152289
  simp only [CollatzResearch.WordTrace]
  refine ⟨114973425276802795944635921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76648950184535197296423947 114973425276802795944635921)
  ·
    refine ⟨86230068957602096958476941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114973425276802795944635921 86230068957602096958476941)
    ·
      refine ⟨32336275859100786359428853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86230068957602096958476941 32336275859100786359428853)
      ·
        refine ⟨3031525861790698721196455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32336275859100786359428853 3031525861790698721196455)
        ·
          refine ⟨4547288792686048081794683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031525861790698721196455 4547288792686048081794683)
          ·
            refine ⟨6820933189029072122692025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4547288792686048081794683 6820933189029072122692025)
            ·
              refine ⟨5115699891771804092019019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6820933189029072122692025 5115699891771804092019019)
              ·
                refine ⟨7673549837657706138028529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5115699891771804092019019 7673549837657706138028529)
                ·
                  refine ⟨5755162378243279603521397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7673549837657706138028529 5755162378243279603521397)
                  ·
                    refine ⟨539546472960307462830131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5755162378243279603521397 539546472960307462830131)
                    ·
                      rfl

theorem cell23_3152289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_3152289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152289 prefixEnd_3152289 := by exact prefixLift 3152289
  have htrace : WordTrace (prefixWord ++ tailWord_3152289) baseStart_3152289 baseEnd_3152289 := by
    simpa [prefixWord, tailWord_3152289, baseEnd_3152289] using wordTrace_append hprefix tailTrace_3152289
  have hstable : (prefixWord ++ tailWord_3152289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152289).length < 2 ^ (prefixWord ++ tailWord_3152289).sum := by decide
  have hdescent : baseEnd_3152289 < baseStart_3152289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152345 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 3, 5]
def baseStart_3152345 : Nat := 118140960795 + 3152345 * 2 ^ 59
def prefixEnd_3152345 : Nat := 4983230072969 + 3 ^ 40 * 3152345 * 2
def baseEnd_3152345 : Nat := 539556057932524723130045

theorem tailTrace_3152345 : CollatzResearch.WordTrace tailWord_3152345 prefixEnd_3152345 539556057932524723130045 := by
  unfold tailWord_3152345
  simp only [CollatzResearch.WordTrace]
  refine ⟨114975467764599917508674489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76650311843066611672449659 114975467764599917508674489)
  ·
    refine ⟨86231600823449938131505867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114975467764599917508674489 86231600823449938131505867)
    ·
      refine ⟨129347401235174907197258801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86231600823449938131505867 129347401235174907197258801)
      ·
        refine ⟨97010550926381180397944101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129347401235174907197258801 97010550926381180397944101)
        ·
          refine ⟨18189478298696471324614519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97010550926381180397944101 18189478298696471324614519)
          ·
            refine ⟨27284217448044706986921779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18189478298696471324614519 27284217448044706986921779)
            ·
              refine ⟨40926326172067060480382669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27284217448044706986921779 40926326172067060480382669)
              ·
                refine ⟨15347372314525147680143501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40926326172067060480382669 15347372314525147680143501)
                ·
                  refine ⟨5755264617946930380053813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15347372314525147680143501 5755264617946930380053813)
                  ·
                    refine ⟨539556057932524723130045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5755264617946930380053813 539556057932524723130045)
                    ·
                      rfl

theorem cell23_3152345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_3152345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152345 prefixEnd_3152345 := by exact prefixLift 3152345
  have htrace : WordTrace (prefixWord ++ tailWord_3152345) baseStart_3152345 baseEnd_3152345 := by
    simpa [prefixWord, tailWord_3152345, baseEnd_3152345] using wordTrace_append hprefix tailTrace_3152345
  have hstable : (prefixWord ++ tailWord_3152345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152345).length < 2 ^ (prefixWord ++ tailWord_3152345).sum := by decide
  have hdescent : baseEnd_3152345 < baseStart_3152345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152352 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 1, 5, 2]
def baseStart_3152352 : Nat := 118140960795 + 3152352 * 2 ^ 59
def prefixEnd_3152352 : Nat := 4983230072969 + 3 ^ 40 * 3152352 * 2
def baseEnd_3152352 : Nat := 1618671768162155642002603

theorem tailTrace_3152352 : CollatzResearch.WordTrace tailWord_3152352 prefixEnd_3152352 1618671768162155642002603 := by
  unfold tailWord_3152352
  simp only [CollatzResearch.WordTrace]
  refine ⟨57487861537787278852089655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76650482050383038469452873 57487861537787278852089655)
  ·
    refine ⟨86231792306680918278134483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57487861537787278852089655 86231792306680918278134483)
    ·
      refine ⟨129347688460021377417201725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86231792306680918278134483 129347688460021377417201725)
      ·
        refine ⟨48505383172508016531450647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129347688460021377417201725 48505383172508016531450647)
        ·
          refine ⟨72758074758762024797175971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48505383172508016531450647 72758074758762024797175971)
          ·
            refine ⟨109137112138143037195763957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72758074758762024797175971 109137112138143037195763957)
            ·
              refine ⟨10231604262950909737102871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109137112138143037195763957 10231604262950909737102871)
              ·
                refine ⟨15347406394426364605654307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10231604262950909737102871 15347406394426364605654307)
                ·
                  refine ⟨23021109591639546908481461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15347406394426364605654307 23021109591639546908481461)
                  ·
                    refine ⟨2158229024216207522670137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23021109591639546908481461 2158229024216207522670137)
                    ·
                      refine ⟨1618671768162155642002603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158229024216207522670137 1618671768162155642002603)
                      ·
                        rfl

theorem cell23_3152352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_3152352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152352 prefixEnd_3152352 := by exact prefixLift 3152352
  have htrace : WordTrace (prefixWord ++ tailWord_3152352) baseStart_3152352 baseEnd_3152352 := by
    simpa [prefixWord, tailWord_3152352, baseEnd_3152352] using wordTrace_append hprefix tailTrace_3152352
  have hstable : (prefixWord ++ tailWord_3152352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152352).length < 2 ^ (prefixWord ++ tailWord_3152352).sum := by decide
  have hdescent : baseEnd_3152352 < baseStart_3152352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152405 : List Nat := [1, 3, 2, 1, 3, 1, 3, 9]
def baseStart_3152405 : Nat := 118140960795 + 3152405 * 2 ^ 59
def prefixEnd_3152405 : Nat := 4983230072969 + 3 ^ 40 * 3152405 * 2
def baseEnd_3152405 : Nat := 59951814171734960542217

theorem tailTrace_3152405 : CollatzResearch.WordTrace tailWord_3152405 prefixEnd_3152405 59951814171734960542217 := by
  unfold tailWord_3152405
  simp only [CollatzResearch.WordTrace]
  refine ⟨114977656144382547755858669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76651770762921698503905779 114977656144382547755858669)
  ·
    refine ⟨43116621054143455408447001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114977656144382547755858669 43116621054143455408447001)
    ·
      refine ⟨32337465790607591556335251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43116621054143455408447001 32337465790607591556335251)
      ·
        refine ⟨48506198685911387334502877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32337465790607591556335251 48506198685911387334502877)
        ·
          refine ⟨18189824507216770250438579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48506198685911387334502877 18189824507216770250438579)
          ·
            refine ⟨27284736760825155375657869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18189824507216770250438579 27284736760825155375657869)
            ·
              refine ⟨10231776285309433265871701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27284736760825155375657869 10231776285309433265871701)
              ·
                refine ⟨59951814171734960542217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10231776285309433265871701 59951814171734960542217)
                ·
                  rfl

theorem cell23_3152405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 9].length) (baseStart_3152405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152405 prefixEnd_3152405 := by exact prefixLift 3152405
  have htrace : WordTrace (prefixWord ++ tailWord_3152405) baseStart_3152405 baseEnd_3152405 := by
    simpa [prefixWord, tailWord_3152405, baseEnd_3152405] using wordTrace_append hprefix tailTrace_3152405
  have hstable : (prefixWord ++ tailWord_3152405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152405).length < 2 ^ (prefixWord ++ tailWord_3152405).sum := by decide
  have hdescent : baseEnd_3152405 < baseStart_3152405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152419 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 1, 2, 3]
def baseStart_3152419 : Nat := 118140960795 + 3152419 * 2 ^ 59
def prefixEnd_3152419 : Nat := 4983230072969 + 3 ^ 40 * 3152419 * 2
def baseEnd_3152419 : Nat := 1618706171366006879864795

theorem tailTrace_3152419 : CollatzResearch.WordTrace tailWord_3152419 prefixEnd_3152419 1618706171366006879864795 := by
  unfold tailWord_3152419
  simp only [CollatzResearch.WordTrace]
  refine ⟨114978166766331828146868311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76652111177554552097912207 114978166766331828146868311)
  ·
    refine ⟨172467250149497742220302467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114978166766331828146868311 172467250149497742220302467)
    ·
      refine ⟨258700875224246613330453701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172467250149497742220302467 258700875224246613330453701)
      ·
        refine ⟨48506414104546239999460069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258700875224246613330453701 48506414104546239999460069)
        ·
          refine ⟨9094952644602419999898763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48506414104546239999460069 9094952644602419999898763)
          ·
            refine ⟨13642428966903629999848145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9094952644602419999898763 13642428966903629999848145)
            ·
              refine ⟨10231821725177722499886109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13642428966903629999848145 10231821725177722499886109)
              ·
                refine ⟨3836933146941645937457291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10231821725177722499886109 3836933146941645937457291)
                ·
                  refine ⟨5755399720412468906185937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836933146941645937457291 5755399720412468906185937)
                  ·
                    refine ⟨4316549790309351679639453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5755399720412468906185937 4316549790309351679639453)
                    ·
                      refine ⟨1618706171366006879864795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4316549790309351679639453 1618706171366006879864795)
                      ·
                        rfl

theorem cell23_3152419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_3152419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152419 prefixEnd_3152419 := by exact prefixLift 3152419
  have htrace : WordTrace (prefixWord ++ tailWord_3152419) baseStart_3152419 baseEnd_3152419 := by
    simpa [prefixWord, tailWord_3152419, baseEnd_3152419] using wordTrace_append hprefix tailTrace_3152419
  have hstable : (prefixWord ++ tailWord_3152419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152419).length < 2 ^ (prefixWord ++ tailWord_3152419).sum := by decide
  have hdescent : baseEnd_3152419 < baseStart_3152419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152435 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 2, 7]
def baseStart_3152435 : Nat := 118140960795 + 3152435 * 2 ^ 59
def prefixEnd_3152435 : Nat := 4983230072969 + 3 ^ 40 * 3152435 * 2
def baseEnd_3152435 : Nat := 539571462352159605754907

theorem tailTrace_3152435 : CollatzResearch.WordTrace tailWord_3152435 prefixEnd_3152435 539571462352159605754907 := by
  unfold tailWord_3152435
  simp only [CollatzResearch.WordTrace]
  refine ⟨114978750334273862879450759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76652500222849241919633839 114978750334273862879450759)
  ·
    refine ⟨172468125501410794319176139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114978750334273862879450759 172468125501410794319176139)
    ·
      refine ⟨258702188252116191478764209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172468125501410794319176139 258702188252116191478764209)
      ·
        refine ⟨194026641189087143609073157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258702188252116191478764209 194026641189087143609073157)
        ·
          refine ⟨36379995222953839426701217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194026641189087143609073157 36379995222953839426701217)
          ·
            refine ⟨27284996417215379570025913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36379995222953839426701217 27284996417215379570025913)
            ·
              refine ⟨20463747312911534677519435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27284996417215379570025913 20463747312911534677519435)
              ·
                refine ⟨30695620969367302016279153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20463747312911534677519435 30695620969367302016279153)
                ·
                  refine ⟨23021715727025476512209365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30695620969367302016279153 23021715727025476512209365)
                  ·
                    refine ⟨539571462352159605754907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23021715727025476512209365 539571462352159605754907)
                    ·
                      rfl

theorem cell23_3152435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 7].length) (baseStart_3152435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152435 prefixEnd_3152435 := by exact prefixLift 3152435
  have htrace : WordTrace (prefixWord ++ tailWord_3152435) baseStart_3152435 baseEnd_3152435 := by
    simpa [prefixWord, tailWord_3152435, baseEnd_3152435] using wordTrace_append hprefix tailTrace_3152435
  have hstable : (prefixWord ++ tailWord_3152435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152435).length < 2 ^ (prefixWord ++ tailWord_3152435).sum := by decide
  have hdescent : baseEnd_3152435 < baseStart_3152435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152492 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 3]
def baseStart_3152492 : Nat := 118140960795 + 3152492 * 2 ^ 59
def prefixEnd_3152492 : Nat := 4983230072969 + 3 ^ 40 * 3152492 * 2
def baseEnd_3152492 : Nat := 1618743655453785094251959

theorem tailTrace_3152492 : CollatzResearch.WordTrace tailWord_3152492 prefixEnd_3152492 1618743655453785094251959 := by
  unfold tailWord_3152492
  simp only [CollatzResearch.WordTrace]
  refine ⟨57490414647533680807137865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76653886196711574409517153 57490414647533680807137865)
  ·
    refine ⟨43117810985650260605353399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57490414647533680807137865 43117810985650260605353399)
    ·
      refine ⟨64676716478475390908030099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43117810985650260605353399 64676716478475390908030099)
      ·
        refine ⟨97015074717713086362045149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64676716478475390908030099 97015074717713086362045149)
        ·
          refine ⟨36380653019142407385766931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97015074717713086362045149 36380653019142407385766931)
          ·
            refine ⟨54570979528713611078650397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36380653019142407385766931 54570979528713611078650397)
            ·
              refine ⟨20464117323267604154493899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54570979528713611078650397 20464117323267604154493899)
              ·
                refine ⟨30696175984901406231740849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20464117323267604154493899 30696175984901406231740849)
                ·
                  refine ⟨23022131988676054673805637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30696175984901406231740849 23022131988676054673805637)
                  ·
                    refine ⟨4316649747876760251338557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23022131988676054673805637 4316649747876760251338557)
                    ·
                      refine ⟨1618743655453785094251959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4316649747876760251338557 1618743655453785094251959)
                      ·
                        rfl

theorem cell23_3152492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_3152492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152492 prefixEnd_3152492 := by exact prefixLift 3152492
  have htrace : WordTrace (prefixWord ++ tailWord_3152492) baseStart_3152492 baseEnd_3152492 := by
    simpa [prefixWord, tailWord_3152492, baseEnd_3152492] using wordTrace_append hprefix tailTrace_3152492
  have hstable : (prefixWord ++ tailWord_3152492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152492).length < 2 ^ (prefixWord ++ tailWord_3152492).sum := by decide
  have hdescent : baseEnd_3152492 < baseStart_3152492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152512 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 7]
def baseStart_3152512 : Nat := 118140960795 + 3152512 * 2 ^ 59
def prefixEnd_3152512 : Nat := 4983230072969 + 3 ^ 40 * 3152512 * 2
def baseEnd_3152512 : Nat := 179861547229652779555763

theorem tailTrace_3152512 : CollatzResearch.WordTrace tailWord_3152512 prefixEnd_3152512 179861547229652779555763 := by
  unfold tailWord_3152512
  simp only [CollatzResearch.WordTrace]
  refine ⟨57490779377497452515001895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76654372503329936686669193 57490779377497452515001895)
  ·
    refine ⟨86236169066246178772502843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57490779377497452515001895 86236169066246178772502843)
    ·
      refine ⟨129354253599369268158754265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86236169066246178772502843 129354253599369268158754265)
      ·
        refine ⟨97015690199526951119065699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129354253599369268158754265 97015690199526951119065699)
        ·
          refine ⟨145523535299290426678598549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97015690199526951119065699 145523535299290426678598549)
          ·
            refine ⟨6821415717154238750559307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145523535299290426678598549 6821415717154238750559307)
            ·
              refine ⟨10232123575731358125838961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6821415717154238750559307 10232123575731358125838961)
              ·
                refine ⟨7674092681798518594379221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10232123575731358125838961 7674092681798518594379221)
                ·
                  refine ⟨179861547229652779555763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7674092681798518594379221 179861547229652779555763)
                  ·
                    rfl

theorem cell23_3152512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 7].length) (baseStart_3152512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152512 prefixEnd_3152512 := by exact prefixLift 3152512
  have htrace : WordTrace (prefixWord ++ tailWord_3152512) baseStart_3152512 baseEnd_3152512 := by
    simpa [prefixWord, tailWord_3152512, baseEnd_3152512] using wordTrace_append hprefix tailTrace_3152512
  have hstable : (prefixWord ++ tailWord_3152512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152512).length < 2 ^ (prefixWord ++ tailWord_3152512).sum := by decide
  have hdescent : baseEnd_3152512 < baseStart_3152512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152540 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_3152540 : Nat := 118140960795 + 3152540 * 2 ^ 59
def prefixEnd_3152540 : Nat := 4983230072969 + 3 ^ 40 * 3152540 * 2
def baseEnd_3152540 : Nat := 1618768302525200906451739

theorem tailTrace_3152540 : CollatzResearch.WordTrace tailWord_3152540 prefixEnd_3152540 1618768302525200906451739 := by
  unfold tailWord_3152540
  simp only [CollatzResearch.WordTrace]
  refine ⟨57491289999446732906011537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76655053332595643874682049 57491289999446732906011537)
  ·
    refine ⟨43118467499585049679508653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57491289999446732906011537 43118467499585049679508653)
    ·
      refine ⟨16169425312344393629815745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43118467499585049679508653 16169425312344393629815745)
      ·
        refine ⟨12127068984258295222361809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16169425312344393629815745 12127068984258295222361809)
        ·
          refine ⟨9095301738193721416771357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12127068984258295222361809 9095301738193721416771357)
          ·
            refine ⟨3410738151822645531289259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9095301738193721416771357 3410738151822645531289259)
            ·
              refine ⟨5116107227733968296933889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410738151822645531289259 5116107227733968296933889)
              ·
                refine ⟨3837080420800476222700417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5116107227733968296933889 3837080420800476222700417)
                ·
                  refine ⟨2877810315600357167025313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3837080420800476222700417 2877810315600357167025313)
                  ·
                    refine ⟨2158357736700267875268985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2877810315600357167025313 2158357736700267875268985)
                    ·
                      refine ⟨1618768302525200906451739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158357736700267875268985 1618768302525200906451739)
                      ·
                        rfl

theorem cell23_3152540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_3152540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152540 prefixEnd_3152540 := by exact prefixLift 3152540
  have htrace : WordTrace (prefixWord ++ tailWord_3152540) baseStart_3152540 baseEnd_3152540 := by
    simpa [prefixWord, tailWord_3152540, baseEnd_3152540] using wordTrace_append hprefix tailTrace_3152540
  have hstable : (prefixWord ++ tailWord_3152540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152540).length < 2 ^ (prefixWord ++ tailWord_3152540).sum := by decide
  have hdescent : baseEnd_3152540 < baseStart_3152540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152572 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_3152572 : Nat := 118140960795 + 3152572 * 2 ^ 59
def prefixEnd_3152572 : Nat := 4983230072969 + 3 ^ 40 * 3152572 * 2
def baseEnd_3152572 : Nat := 539594911302048260417197

theorem tailTrace_3152572 : CollatzResearch.WordTrace tailWord_3152572 prefixEnd_3152572 539594911302048260417197 := by
  unfold tailWord_3152572
  simp only [CollatzResearch.WordTrace]
  refine ⟨57491873567388767638593985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76655831423185023518125313 57491873567388767638593985)
  ·
    refine ⟨43118905175541575728945489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57491873567388767638593985 43118905175541575728945489)
    ·
      refine ⟨32339178881656181796709117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43118905175541575728945489 32339178881656181796709117)
      ·
        refine ⟨12127192080621068173765919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32339178881656181796709117 12127192080621068173765919)
        ·
          refine ⟨18190788120931602260648879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12127192080621068173765919 18190788120931602260648879)
          ·
            refine ⟨27286182181397403390973319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18190788120931602260648879 27286182181397403390973319)
            ·
              refine ⟨40929273272096105086459979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27286182181397403390973319 40929273272096105086459979)
              ·
                refine ⟨61393909908144157629689969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40929273272096105086459979 61393909908144157629689969)
                ·
                  refine ⟨46045432431108118222267477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61393909908144157629689969 46045432431108118222267477)
                  ·
                    refine ⟨539594911302048260417197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46045432431108118222267477 539594911302048260417197)
                    ·
                      rfl

theorem cell23_3152572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_3152572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152572 prefixEnd_3152572 := by exact prefixLift 3152572
  have htrace : WordTrace (prefixWord ++ tailWord_3152572) baseStart_3152572 baseEnd_3152572 := by
    simpa [prefixWord, tailWord_3152572, baseEnd_3152572] using wordTrace_append hprefix tailTrace_3152572
  have hstable : (prefixWord ++ tailWord_3152572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152572).length < 2 ^ (prefixWord ++ tailWord_3152572).sum := by decide
  have hdescent : baseEnd_3152572 < baseStart_3152572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152599 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 3]
def baseStart_3152599 : Nat := 118140960795 + 3152599 * 2 ^ 59
def prefixEnd_3152599 : Nat := 4983230072969 + 3 ^ 40 * 3152599 * 2
def baseEnd_3152599 : Nat := 1618798597883816175613967

theorem tailTrace_3152599 : CollatzResearch.WordTrace tailWord_3152599 prefixEnd_3152599 1618798597883816175613967 := by
  unfold tailWord_3152599
  simp only [CollatzResearch.WordTrace]
  refine ⟨114984731905679718888420851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76656487937119812592280567 114984731905679718888420851)
  ·
    refine ⟨172477097858519578332631277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114984731905679718888420851 172477097858519578332631277)
    ·
      refine ⟨64678911696944841874736729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172477097858519578332631277 64678911696944841874736729)
      ·
        refine ⟨48509183772708631406052547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64678911696944841874736729 48509183772708631406052547)
        ·
          refine ⟨72763775659062947109078821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48509183772708631406052547 72763775659062947109078821)
          ·
            refine ⟨13643207936074302582952279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72763775659062947109078821 13643207936074302582952279)
            ·
              refine ⟨20464811904111453874428419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13643207936074302582952279 20464811904111453874428419)
              ·
                refine ⟨30697217856167180811642629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20464811904111453874428419 30697217856167180811642629)
                ·
                  refine ⟨5755728348031346402182993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30697217856167180811642629 5755728348031346402182993)
                  ·
                    refine ⟨4316796261023509801637245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5755728348031346402182993 4316796261023509801637245)
                    ·
                      refine ⟨1618798597883816175613967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4316796261023509801637245 1618798597883816175613967)
                      ·
                        rfl

theorem cell23_3152599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_3152599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152599 prefixEnd_3152599 := by exact prefixLift 3152599
  have htrace : WordTrace (prefixWord ++ tailWord_3152599) baseStart_3152599 baseEnd_3152599 := by
    simpa [prefixWord, tailWord_3152599, baseEnd_3152599] using wordTrace_append hprefix tailTrace_3152599
  have hstable : (prefixWord ++ tailWord_3152599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152599).length < 2 ^ (prefixWord ++ tailWord_3152599).sum := by decide
  have hdescent : baseEnd_3152599 < baseStart_3152599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152602 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 8]
def baseStart_3152602 : Nat := 118140960795 + 3152602 * 2 ^ 59
def prefixEnd_3152602 : Nat := 4983230072969 + 3 ^ 40 * 3152602 * 2
def baseEnd_3152602 : Nat := 179866682036197740430717

theorem tailTrace_3152602 : CollatzResearch.WordTrace tailWord_3152602 prefixEnd_3152602 179866682036197740430717 := by
  unfold tailWord_3152602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28746210331167212600195015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76656560883112566933853373 28746210331167212600195015)
  ·
    refine ⟨43119315496750818900292523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28746210331167212600195015 43119315496750818900292523)
    ·
      refine ⟨64678973245126228350438785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43119315496750818900292523 64678973245126228350438785)
      ·
        refine ⟨48509229933844671262829089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64678973245126228350438785 48509229933844671262829089)
        ·
          refine ⟨36381922450383503447121817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48509229933844671262829089 36381922450383503447121817)
          ·
            refine ⟨27286441837787627585341363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36381922450383503447121817 27286441837787627585341363)
            ·
              refine ⟨40929662756681441378012045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27286441837787627585341363 40929662756681441378012045)
              ·
                refine ⟨15348623533755540516754517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40929662756681441378012045 15348623533755540516754517)
                ·
                  refine ⟨179866682036197740430717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15348623533755540516754517 179866682036197740430717)
                  ·
                    rfl

theorem cell23_3152602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_3152602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152602 prefixEnd_3152602 := by exact prefixLift 3152602
  have htrace : WordTrace (prefixWord ++ tailWord_3152602) baseStart_3152602 baseEnd_3152602 := by
    simpa [prefixWord, tailWord_3152602, baseEnd_3152602] using wordTrace_append hprefix tailTrace_3152602
  have hstable : (prefixWord ++ tailWord_3152602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152602).length < 2 ^ (prefixWord ++ tailWord_3152602).sum := by decide
  have hdescent : baseEnd_3152602 < baseStart_3152602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152649 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 1, 5]
def baseStart_3152649 : Nat := 118140960795 + 3152649 * 2 ^ 59
def prefixEnd_3152649 : Nat := 4983230072969 + 3 ^ 40 * 3152649 * 2
def baseEnd_3152649 : Nat := 539608090638846993329579

theorem tailTrace_3152649 : CollatzResearch.WordTrace tailWord_3152649 prefixEnd_3152649 539608090638846993329579 := by
  unfold tailWord_3152649
  simp only [CollatzResearch.WordTrace]
  refine ⟨114986555555498577427741001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76657703703665718285160667 114986555555498577427741001)
  ·
    refine ⟨86239916666623933070805751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114986555555498577427741001 86239916666623933070805751)
    ·
      refine ⟨129359874999935899606208627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86239916666623933070805751 129359874999935899606208627)
      ·
        refine ⟨194039812499903849409312941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129359874999935899606208627 194039812499903849409312941)
        ·
          refine ⟨72764929687463943528492353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194039812499903849409312941 72764929687463943528492353)
          ·
            refine ⟨54573697265597957646369265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72764929687463943528492353 54573697265597957646369265)
            ·
              refine ⟨40930272949198468234776949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54573697265597957646369265 40930272949198468234776949)
              ·
                refine ⟨3837213088987356397010339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40930272949198468234776949 3837213088987356397010339)
                ·
                  refine ⟨5755819633481034595515509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837213088987356397010339 5755819633481034595515509)
                  ·
                    refine ⟨539608090638846993329579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5755819633481034595515509 539608090638846993329579)
                    ·
                      rfl

theorem cell23_3152649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 5].length) (baseStart_3152649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152649 prefixEnd_3152649 := by exact prefixLift 3152649
  have htrace : WordTrace (prefixWord ++ tailWord_3152649) baseStart_3152649 baseEnd_3152649 := by
    simpa [prefixWord, tailWord_3152649, baseEnd_3152649] using wordTrace_append hprefix tailTrace_3152649
  have hstable : (prefixWord ++ tailWord_3152649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152649).length < 2 ^ (prefixWord ++ tailWord_3152649).sum := by decide
  have hdescent : baseEnd_3152649 < baseStart_3152649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152703 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 1, 1, 4]
def baseStart_3152703 : Nat := 118140960795 + 3152703 * 2 ^ 59
def prefixEnd_3152703 : Nat := 4983230072969 + 3 ^ 40 * 3152703 * 2
def baseEnd_3152703 : Nat := 1618851999871883768713489

theorem tailTrace_3152703 : CollatzResearch.WordTrace tailWord_3152703 prefixEnd_3152703 1618851999871883768713489 := by
  unfold tailWord_3152703
  simp only [CollatzResearch.WordTrace]
  refine ⟨114988525097302944650206763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76659016731535296433471175 114988525097302944650206763)
  ·
    refine ⟨172482787645954416975310145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114988525097302944650206763 172482787645954416975310145)
    ·
      refine ⟨129362090734465812731482609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172482787645954416975310145 129362090734465812731482609)
      ·
        refine ⟨97021568050849359548611957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129362090734465812731482609 97021568050849359548611957)
        ·
          refine ⟨9095772004767127457682371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97021568050849359548611957 9095772004767127457682371)
          ·
            refine ⟨13643658007150691186523557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9095772004767127457682371 13643658007150691186523557)
            ·
              refine ⟨2558185876340754597473167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13643658007150691186523557 2558185876340754597473167)
              ·
                refine ⟨3837278814511131896209751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558185876340754597473167 3837278814511131896209751)
                ·
                  refine ⟨5755918221766697844314627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837278814511131896209751 5755918221766697844314627)
                  ·
                    refine ⟨8633877332650046766471941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5755918221766697844314627 8633877332650046766471941)
                    ·
                      refine ⟨1618851999871883768713489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8633877332650046766471941 1618851999871883768713489)
                      ·
                        rfl

theorem cell23_3152703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 1, 4].length) (baseStart_3152703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152703 prefixEnd_3152703 := by exact prefixLift 3152703
  have htrace : WordTrace (prefixWord ++ tailWord_3152703) baseStart_3152703 baseEnd_3152703 := by
    simpa [prefixWord, tailWord_3152703, baseEnd_3152703] using wordTrace_append hprefix tailTrace_3152703
  have hstable : (prefixWord ++ tailWord_3152703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152703).length < 2 ^ (prefixWord ++ tailWord_3152703).sum := by decide
  have hdescent : baseEnd_3152703 < baseStart_3152703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152713 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 2, 4]
def baseStart_3152713 : Nat := 118140960795 + 3152713 * 2 ^ 59
def prefixEnd_3152713 : Nat := 4983230072969 + 3 ^ 40 * 3152713 * 2
def baseEnd_3152713 : Nat := 539619044892809576529481

theorem tailTrace_3152713 : CollatzResearch.WordTrace tailWord_3152713 prefixEnd_3152713 539619044892809576529481 := by
  unfold tailWord_3152713
  simp only [CollatzResearch.WordTrace]
  refine ⟨114988889827266716358070793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76659259884844477572047195 114988889827266716358070793)
  ·
    refine ⟨86241667370450037268553095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114988889827266716358070793 86241667370450037268553095)
    ·
      refine ⟨129362501055675055902829643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86241667370450037268553095 129362501055675055902829643)
      ·
        refine ⟨194043751583512583854244465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129362501055675055902829643 194043751583512583854244465)
        ·
          refine ⟨145532813687634437890683349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194043751583512583854244465 145532813687634437890683349)
          ·
            refine ⟨3410925320803932138062891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 145532813687634437890683349 3410925320803932138062891)
            ·
              refine ⟨5116387981205898207094337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410925320803932138062891 5116387981205898207094337)
              ·
                refine ⟨3837290985904423655320753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5116387981205898207094337 3837290985904423655320753)
                ·
                  refine ⟨2877968239428317741490565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3837290985904423655320753 2877968239428317741490565)
                  ·
                    refine ⟨539619044892809576529481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2877968239428317741490565 539619044892809576529481)
                    ·
                      rfl

theorem cell23_3152713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 4].length) (baseStart_3152713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152713 prefixEnd_3152713 := by exact prefixLift 3152713
  have htrace : WordTrace (prefixWord ++ tailWord_3152713) baseStart_3152713 baseEnd_3152713 := by
    simpa [prefixWord, tailWord_3152713, baseEnd_3152713] using wordTrace_append hprefix tailTrace_3152713
  have hstable : (prefixWord ++ tailWord_3152713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152713).length < 2 ^ (prefixWord ++ tailWord_3152713).sum := by decide
  have hdescent : baseEnd_3152713 < baseStart_3152713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152720 : List Nat := [2, 1, 1, 1, 1, 4, 4, 4, 1, 2, 2]
def baseStart_3152720 : Nat := 118140960795 + 3152720 * 2 ^ 59
def prefixEnd_3152720 : Nat := 4983230072969 + 3 ^ 40 * 3152720 * 2
def baseEnd_3152720 : Nat := 1618860729043010202200911

theorem tailTrace_3152720 : CollatzResearch.WordTrace tailWord_3152720 prefixEnd_3152720 1618860729043010202200911 := by
  unfold tailWord_3152720
  simp only [CollatzResearch.WordTrace]
  refine ⟨57494572569120678276787807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76659430092160904369050409 57494572569120678276787807)
  ·
    refine ⟨86241858853681017415181711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57494572569120678276787807 86241858853681017415181711)
    ·
      refine ⟨129362788280521526122772567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86241858853681017415181711 129362788280521526122772567)
      ·
        refine ⟨194044182420782289184158851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129362788280521526122772567 194044182420782289184158851)
        ·
          refine ⟨291066273631173433776238277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194044182420782289184158851 291066273631173433776238277)
          ·
            refine ⟨54574926305845018833044677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291066273631173433776238277 54574926305845018833044677)
            ·
              refine ⟨10232798682345941031195877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54574926305845018833044677 10232798682345941031195877)
              ·
                refine ⟨1918649752939863943349227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10232798682345941031195877 1918649752939863943349227)
                ·
                  refine ⟨2877974629409795915023841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918649752939863943349227 2877974629409795915023841)
                  ·
                    refine ⟨2158480972057346936267881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2877974629409795915023841 2158480972057346936267881)
                    ·
                      refine ⟨1618860729043010202200911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158480972057346936267881 1618860729043010202200911)
                      ·
                        rfl

theorem cell23_3152720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 1, 2, 2].length) (baseStart_3152720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152720 prefixEnd_3152720 := by exact prefixLift 3152720
  have htrace : WordTrace (prefixWord ++ tailWord_3152720) baseStart_3152720 baseEnd_3152720 := by
    simpa [prefixWord, tailWord_3152720, baseEnd_3152720] using wordTrace_append hprefix tailTrace_3152720
  have hstable : (prefixWord ++ tailWord_3152720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152720).length < 2 ^ (prefixWord ++ tailWord_3152720).sum := by decide
  have hdescent : baseEnd_3152720 < baseStart_3152720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152763 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 1, 3, 2]
def baseStart_3152763 : Nat := 118140960795 + 3152763 * 2 ^ 59
def prefixEnd_3152763 : Nat := 4983230072969 + 3 ^ 40 * 3152763 * 2
def baseEnd_3152763 : Nat := 1618882808711153533963213

theorem tailTrace_3152763 : CollatzResearch.WordTrace tailWord_3152763 prefixEnd_3152763 1618882808711153533963213 := by
  unfold tailWord_3152763
  simp only [CollatzResearch.WordTrace]
  refine ⟨114990713477085574897390943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76660475651390383264927295 114990713477085574897390943)
  ·
    refine ⟨172486070215628362346086415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114990713477085574897390943 172486070215628362346086415)
    ·
      refine ⟨258729105323442543519129623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172486070215628362346086415 258729105323442543519129623)
      ·
        refine ⟨388093657985163815278694435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258729105323442543519129623 388093657985163815278694435)
        ·
          refine ⟨582140486977745722918041653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388093657985163815278694435 582140486977745722918041653)
          ·
            refine ⟨54575670654163661523566405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 582140486977745722918041653 54575670654163661523566405)
            ·
              refine ⟨10232938247655686535668701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54575670654163661523566405 10232938247655686535668701)
              ·
                refine ⟨3837351842870882450875763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10232938247655686535668701 3837351842870882450875763)
                ·
                  refine ⟨5756027764306323676313645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837351842870882450875763 5756027764306323676313645)
                  ·
                    refine ⟨2158510411614871378617617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5756027764306323676313645 2158510411614871378617617)
                    ·
                      refine ⟨1618882808711153533963213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158510411614871378617617 1618882808711153533963213)
                      ·
                        rfl

theorem cell23_3152763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 3, 2].length) (baseStart_3152763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152763 prefixEnd_3152763 := by exact prefixLift 3152763
  have htrace : WordTrace (prefixWord ++ tailWord_3152763) baseStart_3152763 baseEnd_3152763 := by
    simpa [prefixWord, tailWord_3152763, baseEnd_3152763] using wordTrace_append hprefix tailTrace_3152763
  have hstable : (prefixWord ++ tailWord_3152763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152763).length < 2 ^ (prefixWord ++ tailWord_3152763).sum := by decide
  have hdescent : baseEnd_3152763 < baseStart_3152763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152822 : List Nat := [5, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_3152822 : Nat := 118140960795 + 3152822 * 2 ^ 59
def prefixEnd_3152822 : Nat := 4983230072969 + 3 ^ 40 * 3152822 * 2
def baseEnd_3152822 : Nat := 1618913104069768803125443

theorem tailTrace_3152822 : CollatzResearch.WordTrace tailWord_3152822 prefixEnd_3152822 1618913104069768803125443 := by
  unfold tailWord_3152822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187054086491989248361795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76661910255914551982525813 7187054086491989248361795)
  ·
    refine ⟨10780581129737983872542693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7187054086491989248361795 10780581129737983872542693)
    ·
      refine ⟨2021358961825871976101755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10780581129737983872542693 2021358961825871976101755)
      ·
        refine ⟨3032038442738807964152633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021358961825871976101755 3032038442738807964152633)
        ·
          refine ⟨2274028832054105973114475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3032038442738807964152633 2274028832054105973114475)
          ·
            refine ⟨3411043248081158959671713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274028832054105973114475 3411043248081158959671713)
            ·
              refine ⟨2558282436060869219753785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3411043248081158959671713 2558282436060869219753785)
              ·
                refine ⟨1918711827045651914815339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2558282436060869219753785 1918711827045651914815339)
                ·
                  refine ⟨2878067740568477872223009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918711827045651914815339 2878067740568477872223009)
                  ·
                    refine ⟨2158550805426358404167257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2878067740568477872223009 2158550805426358404167257)
                    ·
                      refine ⟨1618913104069768803125443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158550805426358404167257 1618913104069768803125443)
                      ·
                        rfl

theorem cell23_3152822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_3152822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152822 prefixEnd_3152822 := by exact prefixLift 3152822
  have htrace : WordTrace (prefixWord ++ tailWord_3152822) baseStart_3152822 baseEnd_3152822 := by
    simpa [prefixWord, tailWord_3152822, baseEnd_3152822] using wordTrace_append hprefix tailTrace_3152822
  have hstable : (prefixWord ++ tailWord_3152822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152822).length < 2 ^ (prefixWord ++ tailWord_3152822).sum := by decide
  have hdescent : baseEnd_3152822 < baseStart_3152822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152826 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3]
def baseStart_3152826 : Nat := 118140960795 + 3152826 * 2 ^ 59
def prefixEnd_3152826 : Nat := 4983230072969 + 3 ^ 40 * 3152826 * 2
def baseEnd_3152826 : Nat := 1618915157992386787475423

theorem tailTrace_3152826 : CollatzResearch.WordTrace tailWord_3152826 prefixEnd_3152826 1618915157992386787475423 := by
  unfold tailWord_3152826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28748252818964334164233583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76662007517238224437956221 28748252818964334164233583)
  ·
    refine ⟨43122379228446501246350375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28748252818964334164233583 43122379228446501246350375)
    ·
      refine ⟨64683568842669751869525563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43122379228446501246350375 64683568842669751869525563)
      ·
        refine ⟨97025353264004627804288345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64683568842669751869525563 97025353264004627804288345)
        ·
          refine ⟨72769014948003470853216259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97025353264004627804288345 72769014948003470853216259)
          ·
            refine ⟨109153522422005206279824389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72769014948003470853216259 109153522422005206279824389)
            ·
              refine ⟨20466285454125976177467073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109153522422005206279824389 20466285454125976177467073)
              ·
                refine ⟨15349714090594482133100305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20466285454125976177467073 15349714090594482133100305)
                ·
                  refine ⟨11512285567945861599825229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15349714090594482133100305 11512285567945861599825229)
                  ·
                    refine ⟨4317107087979698099934461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11512285567945861599825229 4317107087979698099934461)
                    ·
                      refine ⟨1618915157992386787475423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4317107087979698099934461 1618915157992386787475423)
                      ·
                        rfl

theorem cell23_3152826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_3152826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152826 prefixEnd_3152826 := by exact prefixLift 3152826
  have htrace : WordTrace (prefixWord ++ tailWord_3152826) baseStart_3152826 baseEnd_3152826 := by
    simpa [prefixWord, tailWord_3152826, baseEnd_3152826] using wordTrace_append hprefix tailTrace_3152826
  have hstable : (prefixWord ++ tailWord_3152826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152826).length < 2 ^ (prefixWord ++ tailWord_3152826).sum := by decide
  have hdescent : baseEnd_3152826 < baseStart_3152826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152884 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3152884 : Nat := 118140960795 + 3152884 * 2 ^ 59
def prefixEnd_3152884 : Nat := 4983230072969 + 3 ^ 40 * 3152884 * 2
def baseEnd_3152884 : Nat := 179882771096705284505573

theorem tailTrace_3152884 : CollatzResearch.WordTrace tailWord_3152884 prefixEnd_3152884 179882771096705284505573 := by
  unfold tailWord_3152884
  simp only [CollatzResearch.WordTrace]
  refine ⟨57497563354823606281272853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76663417806431475041697137 57497563354823606281272853)
  ·
    refine ⟨2695198282257356544434665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57497563354823606281272853 2695198282257356544434665)
    ·
      refine ⟨2021398711693017408325999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2695198282257356544434665 2021398711693017408325999)
      ·
        refine ⟨3032098067539526112488999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021398711693017408325999 3032098067539526112488999)
        ·
          refine ⟨4548147101309289168733499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3032098067539526112488999 4548147101309289168733499)
          ·
            refine ⟨6822220651963933753100249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4548147101309289168733499 6822220651963933753100249)
            ·
              refine ⟨5116665488972950314825187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6822220651963933753100249 5116665488972950314825187)
              ·
                refine ⟨7674998233459425472237781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116665488972950314825187 7674998233459425472237781)
                ·
                  refine ⟨179882771096705284505573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7674998233459425472237781 179882771096705284505573)
                  ·
                    rfl

theorem cell23_3152884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3152884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152884 prefixEnd_3152884 := by exact prefixLift 3152884
  have htrace : WordTrace (prefixWord ++ tailWord_3152884) baseStart_3152884 baseEnd_3152884 := by
    simpa [prefixWord, tailWord_3152884, baseEnd_3152884] using wordTrace_append hprefix tailTrace_3152884
  have hstable : (prefixWord ++ tailWord_3152884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152884).length < 2 ^ (prefixWord ++ tailWord_3152884).sum := by decide
  have hdescent : baseEnd_3152884 < baseStart_3152884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152927 : List Nat := [1, 1, 2, 4, 1, 5, 1, 3, 1, 4]
def baseStart_3152927 : Nat := 118140960795 + 3152927 * 2 ^ 59
def prefixEnd_3152927 : Nat := 4983230072969 + 3 ^ 40 * 3152927 * 2
def baseEnd_3152927 : Nat := 539655673179496964104153

theorem tailTrace_3152927 : CollatzResearch.WordTrace tailWord_3152927 prefixEnd_3152927 539655673179496964104153 := by
  unfold tailWord_3152927
  simp only [CollatzResearch.WordTrace]
  refine ⟨114996695048491430906361035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76664463365660953937574023 114996695048491430906361035)
  ·
    refine ⟨172495042572737146359541553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114996695048491430906361035 172495042572737146359541553)
    ·
      refine ⟨129371281929552859769656165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172495042572737146359541553 129371281929552859769656165)
      ·
        refine ⟨24257115361791161206810531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129371281929552859769656165 24257115361791161206810531)
        ·
          refine ⟨36385673042686741810215797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24257115361791161206810531 36385673042686741810215797)
          ·
            refine ⟨3411156847751882044707731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36385673042686741810215797 3411156847751882044707731)
            ·
              refine ⟨5116735271627823067061597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411156847751882044707731 5116735271627823067061597)
              ·
                refine ⟨1918775726860433650148099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5116735271627823067061597 1918775726860433650148099)
                ·
                  refine ⟨2878163590290650475222149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918775726860433650148099 2878163590290650475222149)
                  ·
                    refine ⟨539655673179496964104153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2878163590290650475222149 539655673179496964104153)
                    ·
                      rfl

theorem cell23_3152927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 1, 4].length) (baseStart_3152927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152927 prefixEnd_3152927 := by exact prefixLift 3152927
  have htrace : WordTrace (prefixWord ++ tailWord_3152927) baseStart_3152927 baseEnd_3152927 := by
    simpa [prefixWord, tailWord_3152927, baseEnd_3152927] using wordTrace_append hprefix tailTrace_3152927
  have hstable : (prefixWord ++ tailWord_3152927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152927).length < 2 ^ (prefixWord ++ tailWord_3152927).sum := by decide
  have hdescent : baseEnd_3152927 < baseStart_3152927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152976 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 5]
def baseStart_3152976 : Nat := 118140960795 + 3152976 * 2 ^ 59
def prefixEnd_3152976 : Nat := 4983230072969 + 3 ^ 40 * 3152976 * 2
def baseEnd_3152976 : Nat := 1618992180090561200599733

theorem tailTrace_3152976 : CollatzResearch.WordTrace tailWord_3152976 prefixEnd_3152976 1618992180090561200599733 := by
  unfold tailWord_3152976
  simp only [CollatzResearch.WordTrace]
  refine ⟨57499241112656956137447391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76665654816875941516596521 57499241112656956137447391)
  ·
    refine ⟨86248861668985434206171087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57499241112656956137447391 86248861668985434206171087)
    ·
      refine ⟨129373292503478151309256631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86248861668985434206171087 129373292503478151309256631)
      ·
        refine ⟨194059938755217226963884947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129373292503478151309256631 194059938755217226963884947)
        ·
          refine ⟨291089908132825840445827421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194059938755217226963884947 291089908132825840445827421)
          ·
            refine ⟨109158715549809690167185283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291089908132825840445827421 109158715549809690167185283)
            ·
              refine ⟨163738073324714535250777925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109158715549809690167185283 163738073324714535250777925)
              ·
                refine ⟨30700888748383975359520861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163738073324714535250777925 30700888748383975359520861)
                ·
                  refine ⟨11512833280643990759820323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30700888748383975359520861 11512833280643990759820323)
                  ·
                    refine ⟨17269249920965986139730485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11512833280643990759820323 17269249920965986139730485)
                    ·
                      refine ⟨1618992180090561200599733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17269249920965986139730485 1618992180090561200599733)
                      ·
                        rfl

theorem cell23_3152976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_3152976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152976 prefixEnd_3152976 := by exact prefixLift 3152976
  have htrace : WordTrace (prefixWord ++ tailWord_3152976) baseStart_3152976 baseEnd_3152976 := by
    simpa [prefixWord, tailWord_3152976, baseEnd_3152976] using wordTrace_append hprefix tailTrace_3152976
  have hstable : (prefixWord ++ tailWord_3152976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152976).length < 2 ^ (prefixWord ++ tailWord_3152976).sum := by decide
  have hdescent : baseEnd_3152976 < baseStart_3152976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152986 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_3152986 : Nat := 118140960795 + 3152986 * 2 ^ 59
def prefixEnd_3152986 : Nat := 4983230072969 + 3 ^ 40 * 3152986 * 2
def baseEnd_3152986 : Nat := 1618997314897106161474687

theorem tailTrace_3152986 : CollatzResearch.WordTrace tailWord_3152986 prefixEnd_3152986 1618997314897106161474687 := by
  unfold tailWord_3152986
  simp only [CollatzResearch.WordTrace]
  refine ⟨28749711738819420995689703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76665897970185122655172541 28749711738819420995689703)
  ·
    refine ⟨43124567608229131493534555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28749711738819420995689703 43124567608229131493534555)
    ·
      refine ⟨64686851412343697240301833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43124567608229131493534555 64686851412343697240301833)
      ·
        refine ⟨48515138559257772930226375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64686851412343697240301833 48515138559257772930226375)
        ·
          refine ⟨72772707838886659395339563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48515138559257772930226375 72772707838886659395339563)
          ·
            refine ⟨109159061758329989093009345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72772707838886659395339563 109159061758329989093009345)
            ·
              refine ⟨81869296318747491819757009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109159061758329989093009345 81869296318747491819757009)
              ·
                refine ⟨61401972239060618864817757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81869296318747491819757009 61401972239060618864817757)
                ·
                  refine ⟨23025739589647732074306659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61401972239060618864817757 23025739589647732074306659)
                  ·
                    refine ⟨34538609384471598111459989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23025739589647732074306659 34538609384471598111459989)
                    ·
                      refine ⟨1618997314897106161474687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34538609384471598111459989 1618997314897106161474687)
                      ·
                        rfl

theorem cell23_3152986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_3152986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152986 prefixEnd_3152986 := by exact prefixLift 3152986
  have htrace : WordTrace (prefixWord ++ tailWord_3152986) baseStart_3152986 baseEnd_3152986 := by
    simpa [prefixWord, tailWord_3152986, baseEnd_3152986] using wordTrace_append hprefix tailTrace_3152986
  have hstable : (prefixWord ++ tailWord_3152986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152986).length < 2 ^ (prefixWord ++ tailWord_3152986).sum := by decide
  have hdescent : baseEnd_3152986 < baseStart_3152986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152993 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_3152993 : Nat := 118140960795 + 3152993 * 2 ^ 59
def prefixEnd_3152993 : Nat := 4983230072969 + 3 ^ 40 * 3152993 * 2
def baseEnd_3152993 : Nat := 1619000909261687634087155

theorem tailTrace_3152993 : CollatzResearch.WordTrace tailWord_3152993 prefixEnd_3152993 1619000909261687634087155 := by
  unfold tailWord_3152993
  simp only [CollatzResearch.WordTrace]
  refine ⟨114999102266252324178263633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76666068177501549452175755 114999102266252324178263633)
  ·
    refine ⟨86249326699689243133697725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114999102266252324178263633 86249326699689243133697725)
    ·
      refine ⟨32343497512383466175136647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86249326699689243133697725 32343497512383466175136647)
      ·
        refine ⟨48515246268575199262704971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32343497512383466175136647 48515246268575199262704971)
        ·
          refine ⟨72772869402862798894057457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48515246268575199262704971 72772869402862798894057457)
          ·
            refine ⟨54579652052147099170543093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72772869402862798894057457 54579652052147099170543093)
            ·
              refine ⟨5116842379888790547238415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54579652052147099170543093 5116842379888790547238415)
              ·
                refine ⟨7675263569833185820857623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116842379888790547238415 7675263569833185820857623)
                ·
                  refine ⟨11512895354749778731286435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7675263569833185820857623 11512895354749778731286435)
                  ·
                    refine ⟨17269343032124668096929653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11512895354749778731286435 17269343032124668096929653)
                    ·
                      refine ⟨1619000909261687634087155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17269343032124668096929653 1619000909261687634087155)
                      ·
                        rfl

theorem cell23_3152993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_3152993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3152993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3152993 prefixEnd_3152993 := by exact prefixLift 3152993
  have htrace : WordTrace (prefixWord ++ tailWord_3152993) baseStart_3152993 baseEnd_3152993 := by
    simpa [prefixWord, tailWord_3152993, baseEnd_3152993] using wordTrace_append hprefix tailTrace_3152993
  have hstable : (prefixWord ++ tailWord_3152993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152993).length < 2 ^ (prefixWord ++ tailWord_3152993).sum := by decide
  have hdescent : baseEnd_3152993 < baseStart_3152993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153016 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_3153016 : Nat := 118140960795 + 3153016 * 2 ^ 59
def prefixEnd_3153016 : Nat := 4983230072969 + 3 ^ 40 * 3153016 * 2
def baseEnd_3153016 : Nat := 1619012719316741044099549

theorem tailTrace_3153016 : CollatzResearch.WordTrace tailWord_3153016 prefixEnd_3153016 1619012719316741044099549 := by
  unfold tailWord_3153016
  simp only [CollatzResearch.WordTrace]
  refine ⟨57499970572584499553175451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76666627430112666070900601 57499970572584499553175451)
  ·
    refine ⟨86249955858876749329763177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57499970572584499553175451 86249955858876749329763177)
    ·
      refine ⟨64687466894157561997322383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86249955858876749329763177 64687466894157561997322383)
      ·
        refine ⟨97031200341236342995983575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64687466894157561997322383 97031200341236342995983575)
        ·
          refine ⟨145546800511854514493975363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97031200341236342995983575 145546800511854514493975363)
          ·
            refine ⟨218320200767781771740963045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145546800511854514493975363 218320200767781771740963045)
            ·
              refine ⟨40935037643959082201430571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218320200767781771740963045 40935037643959082201430571)
              ·
                refine ⟨61402556465938623302145857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40935037643959082201430571 61402556465938623302145857)
                ·
                  refine ⟨46051917349453967476609393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61402556465938623302145857 46051917349453967476609393)
                  ·
                    refine ⟨34538938012090475607457045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46051917349453967476609393 34538938012090475607457045)
                    ·
                      refine ⟨1619012719316741044099549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34538938012090475607457045 1619012719316741044099549)
                      ·
                        rfl

theorem cell23_3153016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_3153016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153016 prefixEnd_3153016 := by exact prefixLift 3153016
  have htrace : WordTrace (prefixWord ++ tailWord_3153016) baseStart_3153016 baseEnd_3153016 := by
    simpa [prefixWord, tailWord_3153016, baseEnd_3153016] using wordTrace_append hprefix tailTrace_3153016
  have hstable : (prefixWord ++ tailWord_3153016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153016).length < 2 ^ (prefixWord ++ tailWord_3153016).sum := by decide
  have hdescent : baseEnd_3153016 < baseStart_3153016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153074 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3]
def baseStart_3153074 : Nat := 118140960795 + 3153074 * 2 ^ 59
def prefixEnd_3153074 : Nat := 4983230072969 + 3 ^ 40 * 3153074 * 2
def baseEnd_3153074 : Nat := 1619042501194701817174283

theorem tailTrace_3153074 : CollatzResearch.WordTrace tailWord_3153074 prefixEnd_3153074 1619042501194701817174283 := by
  unfold tailWord_3153074
  simp only [CollatzResearch.WordTrace]
  refine ⟨28750514144739718752990569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76668037719305916674641517 28750514144739718752990569)
  ·
    refine ⟨21562885608554789064742927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28750514144739718752990569 21562885608554789064742927)
    ·
      refine ⟨32344328412832183597114391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21562885608554789064742927 32344328412832183597114391)
      ·
        refine ⟨48516492619248275395671587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32344328412832183597114391 48516492619248275395671587)
        ·
          refine ⟨72774738928872413093507381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48516492619248275395671587 72774738928872413093507381)
          ·
            refine ⟨6822631774581788727516317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72774738928872413093507381 6822631774581788727516317)
            ·
              refine ⟨2558486915468170772818619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6822631774581788727516317 2558486915468170772818619)
              ·
                refine ⟨3837730373202256159227929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558486915468170772818619 3837730373202256159227929)
                ·
                  refine ⟨2878297779901692119420947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3837730373202256159227929 2878297779901692119420947)
                  ·
                    refine ⟨4317446669852538179131421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2878297779901692119420947 4317446669852538179131421)
                    ·
                      refine ⟨1619042501194701817174283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4317446669852538179131421 1619042501194701817174283)
                      ·
                        rfl

theorem cell23_3153074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_3153074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153074 prefixEnd_3153074 := by exact prefixLift 3153074
  have htrace : WordTrace (prefixWord ++ tailWord_3153074) baseStart_3153074 baseEnd_3153074 := by
    simpa [prefixWord, tailWord_3153074, baseEnd_3153074] using wordTrace_append hprefix tailTrace_3153074
  have hstable : (prefixWord ++ tailWord_3153074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153074).length < 2 ^ (prefixWord ++ tailWord_3153074).sum := by decide
  have hdescent : baseEnd_3153074 < baseStart_3153074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153080 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 1, 4, 2]
def baseStart_3153080 : Nat := 118140960795 + 3153080 * 2 ^ 59
def prefixEnd_3153080 : Nat := 4983230072969 + 3 ^ 40 * 3153080 * 2
def baseEnd_3153080 : Nat := 1619045582078628793699255

theorem tailTrace_3153080 : CollatzResearch.WordTrace tailWord_3153080 prefixEnd_3153080 1619045582078628793699255 := by
  unfold tailWord_3153080
  simp only [CollatzResearch.WordTrace]
  refine ⟨57501137708468569018340347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76668183611291425357787129 57501137708468569018340347)
  ·
    refine ⟨86251706562702853527510521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57501137708468569018340347 86251706562702853527510521)
    ·
      refine ⟨64688779922027140145632891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86251706562702853527510521 64688779922027140145632891)
      ·
        refine ⟨97033169883040710218449337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64688779922027140145632891 97033169883040710218449337)
        ·
          refine ⟨72774877412280532663837003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97033169883040710218449337 72774877412280532663837003)
          ·
            refine ⟨109162316118420798995755505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72774877412280532663837003 109162316118420798995755505)
            ·
              refine ⟨81871737088815599246816629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109162316118420798995755505 81871737088815599246816629)
              ·
                refine ⟨7675475352076462429389059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81871737088815599246816629 7675475352076462429389059)
                ·
                  refine ⟨11513213028114693644083589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7675475352076462429389059 11513213028114693644083589)
                  ·
                    refine ⟨2158727442771505058265673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11513213028114693644083589 2158727442771505058265673)
                    ·
                      refine ⟨1619045582078628793699255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158727442771505058265673 1619045582078628793699255)
                      ·
                        rfl

theorem cell23_3153080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 4, 2].length) (baseStart_3153080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153080 prefixEnd_3153080 := by exact prefixLift 3153080
  have htrace : WordTrace (prefixWord ++ tailWord_3153080) baseStart_3153080 baseEnd_3153080 := by
    simpa [prefixWord, tailWord_3153080, baseEnd_3153080] using wordTrace_append hprefix tailTrace_3153080
  have hstable : (prefixWord ++ tailWord_3153080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153080).length < 2 ^ (prefixWord ++ tailWord_3153080).sum := by decide
  have hdescent : baseEnd_3153080 < baseStart_3153080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153084 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 1, 3, 2]
def baseStart_3153084 : Nat := 118140960795 + 3153084 * 2 ^ 59
def prefixEnd_3153084 : Nat := 4983230072969 + 3 ^ 40 * 3153084 * 2
def baseEnd_3153084 : Nat := 1619047636001246778049237

theorem tailTrace_3153084 : CollatzResearch.WordTrace tailWord_3153084 prefixEnd_3153084 1619047636001246778049237 := by
  unfold tailWord_3153084
  simp only [CollatzResearch.WordTrace]
  refine ⟨57501210654461323359913153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76668280872615097813217537 57501210654461323359913153)
  ·
    refine ⟨43125907990845992519934865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57501210654461323359913153 43125907990845992519934865)
    ·
      refine ⟨32344430993134494389951149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43125907990845992519934865 32344430993134494389951149)
      ·
        refine ⟨12129161622425435396231681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32344430993134494389951149 12129161622425435396231681)
        ·
          refine ⟨9096871216819076547173761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12129161622425435396231681 9096871216819076547173761)
          ·
            refine ⟨6822653412614307410380321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9096871216819076547173761 6822653412614307410380321)
            ·
              refine ⟨5116990059460730557785241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6822653412614307410380321 5116990059460730557785241)
              ·
                refine ⟨3837742544595547918338931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5116990059460730557785241 3837742544595547918338931)
                ·
                  refine ⟨5756613816893321877508397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837742544595547918338931 5756613816893321877508397)
                  ·
                    refine ⟨2158730181334995704065649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5756613816893321877508397 2158730181334995704065649)
                    ·
                      refine ⟨1619047636001246778049237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158730181334995704065649 1619047636001246778049237)
                      ·
                        rfl

theorem cell23_3153084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_3153084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153084 prefixEnd_3153084 := by exact prefixLift 3153084
  have htrace : WordTrace (prefixWord ++ tailWord_3153084) baseStart_3153084 baseEnd_3153084 := by
    simpa [prefixWord, tailWord_3153084, baseEnd_3153084] using wordTrace_append hprefix tailTrace_3153084
  have hstable : (prefixWord ++ tailWord_3153084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153084).length < 2 ^ (prefixWord ++ tailWord_3153084).sum := by decide
  have hdescent : baseEnd_3153084 < baseStart_3153084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153120 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 7]
def baseStart_3153120 : Nat := 118140960795 + 3153120 * 2 ^ 59
def prefixEnd_3153120 : Nat := 4983230072969 + 3 ^ 40 * 3153120 * 2
def baseEnd_3153120 : Nat := 179896235700534293022119

theorem tailTrace_3153120 : CollatzResearch.WordTrace tailWord_3153120 prefixEnd_3153120 179896235700534293022119 := by
  unfold tailWord_3153120
  simp only [CollatzResearch.WordTrace]
  refine ⟨57501867168396112434068407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76669156224528149912091209 57501867168396112434068407)
  ·
    refine ⟨86252800752594168651102611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57501867168396112434068407 86252800752594168651102611)
    ·
      refine ⟨129379201128891252976653917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86252800752594168651102611 129379201128891252976653917)
      ·
        refine ⟨48517200423334219866245219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129379201128891252976653917 48517200423334219866245219)
        ·
          refine ⟨72775800635001329799367829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48517200423334219866245219 72775800635001329799367829)
          ·
            refine ⟨3411365654765687334345367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72775800635001329799367829 3411365654765687334345367)
            ·
              refine ⟨5117048482148531001518051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411365654765687334345367 5117048482148531001518051)
              ·
                refine ⟨7675572723222796502277077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117048482148531001518051 7675572723222796502277077)
                ·
                  refine ⟨179896235700534293022119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7675572723222796502277077 179896235700534293022119)
                  ·
                    rfl

theorem cell23_3153120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 7].length) (baseStart_3153120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153120 prefixEnd_3153120 := by exact prefixLift 3153120
  have htrace : WordTrace (prefixWord ++ tailWord_3153120) baseStart_3153120 baseEnd_3153120 := by
    simpa [prefixWord, tailWord_3153120, baseEnd_3153120] using wordTrace_append hprefix tailTrace_3153120
  have hstable : (prefixWord ++ tailWord_3153120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153120).length < 2 ^ (prefixWord ++ tailWord_3153120).sum := by decide
  have hdescent : baseEnd_3153120 < baseStart_3153120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153131 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 2, 2, 2]
def baseStart_3153131 : Nat := 118140960795 + 3153131 * 2 ^ 59
def prefixEnd_3153131 : Nat := 4983230072969 + 3 ^ 40 * 3153131 * 2
def baseEnd_3153131 : Nat := 1619071769592008094161521

theorem tailTrace_3153131 : CollatzResearch.WordTrace tailWord_3153131 prefixEnd_3153131 1619071769592008094161521 := by
  unfold tailWord_3153131
  simp only [CollatzResearch.WordTrace]
  refine ⟨115004135539752373746787247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76669423693168249164524831 115004135539752373746787247)
  ·
    refine ⟨172506203309628560620180871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115004135539752373746787247 172506203309628560620180871)
    ·
      refine ⟨258759304964442840930271307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172506203309628560620180871 258759304964442840930271307)
      ·
        refine ⟨388138957446664261395406961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258759304964442840930271307 388138957446664261395406961)
        ·
          refine ⟨291104218084998196046555221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388138957446664261395406961 291104218084998196046555221)
          ·
            refine ⟨3411377555683572609920569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 291104218084998196046555221 3411377555683572609920569)
            ·
              refine ⟨2558533166762679457440427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3411377555683572609920569 2558533166762679457440427)
              ·
                refine ⟨3837799750144019186160641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558533166762679457440427 3837799750144019186160641)
                ·
                  refine ⟨2878349812608014389620481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3837799750144019186160641 2878349812608014389620481)
                  ·
                    refine ⟨2158762359456010792215361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2878349812608014389620481 2158762359456010792215361)
                    ·
                      refine ⟨1619071769592008094161521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158762359456010792215361 1619071769592008094161521)
                      ·
                        rfl

theorem cell23_3153131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 2, 2, 2].length) (baseStart_3153131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153131 prefixEnd_3153131 := by exact prefixLift 3153131
  have htrace : WordTrace (prefixWord ++ tailWord_3153131) baseStart_3153131 baseEnd_3153131 := by
    simpa [prefixWord, tailWord_3153131, baseEnd_3153131] using wordTrace_append hprefix tailTrace_3153131
  have hstable : (prefixWord ++ tailWord_3153131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153131).length < 2 ^ (prefixWord ++ tailWord_3153131).sum := by decide
  have hdescent : baseEnd_3153131 < baseStart_3153131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153173 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_3153173 : Nat := 118140960795 + 3153173 * 2 ^ 59
def prefixEnd_3153173 : Nat := 4983230072969 + 3 ^ 40 * 3153173 * 2
def baseEnd_3153173 : Nat := 1619093335779496929836327

theorem tailTrace_3153173 : CollatzResearch.WordTrace tailWord_3153173 prefixEnd_3153173 1619093335779496929836327 := by
  unfold tailWord_3153173
  simp only [CollatzResearch.WordTrace]
  refine ⟨115005667405600214919816173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76670444937066809946544115 115005667405600214919816173)
  ·
    refine ⟨43127125277100080594931065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115005667405600214919816173 43127125277100080594931065)
    ·
      refine ⟨32345343957825060446198299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43127125277100080594931065 32345343957825060446198299)
      ·
        refine ⟨48518015936737590669297449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32345343957825060446198299 48518015936737590669297449)
        ·
          refine ⟨36388511952553193001973087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48518015936737590669297449 36388511952553193001973087)
          ·
            refine ⟨54582767928829789502959631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36388511952553193001973087 54582767928829789502959631)
            ·
              refine ⟨81874151893244684254439447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54582767928829789502959631 81874151893244684254439447)
              ·
                refine ⟨122811227839867026381659171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81874151893244684254439447 122811227839867026381659171)
                ·
                  refine ⟨184216841759800539572488757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122811227839867026381659171 184216841759800539572488757)
                  ·
                    refine ⟨17270328914981300584920821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 184216841759800539572488757 17270328914981300584920821)
                    ·
                      refine ⟨1619093335779496929836327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17270328914981300584920821 1619093335779496929836327)
                      ·
                        rfl

theorem cell23_3153173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_3153173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153173 prefixEnd_3153173 := by exact prefixLift 3153173
  have htrace : WordTrace (prefixWord ++ tailWord_3153173) baseStart_3153173 baseEnd_3153173 := by
    simpa [prefixWord, tailWord_3153173, baseEnd_3153173] using wordTrace_append hprefix tailTrace_3153173
  have hstable : (prefixWord ++ tailWord_3153173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153173).length < 2 ^ (prefixWord ++ tailWord_3153173).sum := by decide
  have hdescent : baseEnd_3153173 < baseStart_3153173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153187 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 2, 4, 2]
def baseStart_3153187 : Nat := 118140960795 + 3153187 * 2 ^ 59
def prefixEnd_3153187 : Nat := 4983230072969 + 3 ^ 40 * 3153187 * 2
def baseEnd_3153187 : Nat := 1619100524508659875061263

theorem tailTrace_3153187 : CollatzResearch.WordTrace tailWord_3153187 prefixEnd_3153187 1619100524508659875061263 := by
  unfold tailWord_3153187
  simp only [CollatzResearch.WordTrace]
  refine ⟨115006178027549495310825815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76670785351699663540550543 115006178027549495310825815)
  ·
    refine ⟨172509267041324242966238723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115006178027549495310825815 172509267041324242966238723)
    ·
      refine ⟨258763900561986364449358085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172509267041324242966238723 258763900561986364449358085)
      ·
        refine ⟨48518231355372443334254641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258763900561986364449358085 48518231355372443334254641)
        ·
          refine ⟨36388673516529332500690981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48518231355372443334254641 36388673516529332500690981)
          ·
            refine ⟨6822876284349249843879559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36388673516529332500690981 6822876284349249843879559)
            ·
              refine ⟨10234314426523874765819339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6822876284349249843879559 10234314426523874765819339)
              ·
                refine ⟨15351471639785812148729009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10234314426523874765819339 15351471639785812148729009)
                ·
                  refine ⟨11513603729839359111546757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15351471639785812148729009 11513603729839359111546757)
                  ·
                    refine ⟨2158800699344879833415017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11513603729839359111546757 2158800699344879833415017)
                    ·
                      refine ⟨1619100524508659875061263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158800699344879833415017 1619100524508659875061263)
                      ·
                        rfl

theorem cell23_3153187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_3153187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153187 prefixEnd_3153187 := by exact prefixLift 3153187
  have htrace : WordTrace (prefixWord ++ tailWord_3153187) baseStart_3153187 baseEnd_3153187 := by
    simpa [prefixWord, tailWord_3153187, baseEnd_3153187] using wordTrace_append hprefix tailTrace_3153187
  have hstable : (prefixWord ++ tailWord_3153187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153187).length < 2 ^ (prefixWord ++ tailWord_3153187).sum := by decide
  have hdescent : baseEnd_3153187 < baseStart_3153187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153277 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_3153277 : Nat := 118140960795 + 3153277 * 2 ^ 59
def prefixEnd_3153277 : Nat := 4983230072969 + 3 ^ 40 * 3153277 * 2
def baseEnd_3153277 : Nat := 1619146737767564522935849

theorem tailTrace_3153277 : CollatzResearch.WordTrace tailWord_3153277 prefixEnd_3153277 1619146737767564522935849 := by
  unfold tailWord_3153277
  simp only [CollatzResearch.WordTrace]
  refine ⟨115009460597223440681602085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76672973731482293787734723 115009460597223440681602085)
  ·
    refine ⟨21564273861979395127800391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115009460597223440681602085 21564273861979395127800391)
    ·
      refine ⟨32346410792969092691700587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21564273861979395127800391 32346410792969092691700587)
      ·
        refine ⟨48519616189453639037550881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32346410792969092691700587 48519616189453639037550881)
        ·
          refine ⟨36389712142090229278163161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48519616189453639037550881 36389712142090229278163161)
          ·
            refine ⟨27292284106567671958622371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36389712142090229278163161 27292284106567671958622371)
            ·
              refine ⟨40938426159851507937933557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27292284106567671958622371 40938426159851507937933557)
              ·
                refine ⟨3837977452486078869181271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40938426159851507937933557 3837977452486078869181271)
                ·
                  refine ⟨5756966178729118303771907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837977452486078869181271 5756966178729118303771907)
                  ·
                    refine ⟨8635449268093677455657861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5756966178729118303771907 8635449268093677455657861)
                    ·
                      refine ⟨1619146737767564522935849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8635449268093677455657861 1619146737767564522935849)
                      ·
                        rfl

theorem cell23_3153277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_3153277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153277 prefixEnd_3153277 := by exact prefixLift 3153277
  have htrace : WordTrace (prefixWord ++ tailWord_3153277) baseStart_3153277 baseEnd_3153277 := by
    simpa [prefixWord, tailWord_3153277, baseEnd_3153277] using wordTrace_append hprefix tailTrace_3153277
  have hstable : (prefixWord ++ tailWord_3153277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153277).length < 2 ^ (prefixWord ++ tailWord_3153277).sum := by decide
  have hdescent : baseEnd_3153277 < baseStart_3153277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153281 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_3153281 : Nat := 118140960795 + 3153281 * 2 ^ 59
def prefixEnd_3153281 : Nat := 4983230072969 + 3 ^ 40 * 3153281 * 2
def baseEnd_3153281 : Nat := 1619148791690182507285831

theorem tailTrace_3153281 : CollatzResearch.WordTrace tailWord_3153281 prefixEnd_3153281 1619148791690182507285831 := by
  unfold tailWord_3153281
  simp only [CollatzResearch.WordTrace]
  refine ⟨115009606489208949364747697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76673070992805966243165131 115009606489208949364747697)
  ·
    refine ⟨86257204866906712023560773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115009606489208949364747697 86257204866906712023560773)
    ·
      refine ⟨16173225912545008504417645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86257204866906712023560773 16173225912545008504417645)
      ·
        refine ⟨6064959717204378189156617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16173225912545008504417645 6064959717204378189156617)
        ·
          refine ⟨4548719787903283641867463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6064959717204378189156617 4548719787903283641867463)
          ·
            refine ⟨6823079681854925462801195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4548719787903283641867463 6823079681854925462801195)
            ·
              refine ⟨10234619522782388194201793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6823079681854925462801195 10234619522782388194201793)
              ·
                refine ⟨7675964642086791145651345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10234619522782388194201793 7675964642086791145651345)
                ·
                  refine ⟨5756973481565093359238509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7675964642086791145651345 5756973481565093359238509)
                  ·
                    refine ⟨2158865055586910009714441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5756973481565093359238509 2158865055586910009714441)
                    ·
                      refine ⟨1619148791690182507285831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158865055586910009714441 1619148791690182507285831)
                      ·
                        rfl

theorem cell23_3153281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_3153281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153281 prefixEnd_3153281 := by exact prefixLift 3153281
  have htrace : WordTrace (prefixWord ++ tailWord_3153281) baseStart_3153281 baseEnd_3153281 := by
    simpa [prefixWord, tailWord_3153281, baseEnd_3153281] using wordTrace_append hprefix tailTrace_3153281
  have hstable : (prefixWord ++ tailWord_3153281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153281).length < 2 ^ (prefixWord ++ tailWord_3153281).sum := by decide
  have hdescent : baseEnd_3153281 < baseStart_3153281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153287 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 4, 4]
def baseStart_3153287 : Nat := 118140960795 + 3153287 * 2 ^ 59
def prefixEnd_3153287 : Nat := 4983230072969 + 3 ^ 40 * 3153287 * 2
def baseEnd_3153287 : Nat := 539717290858036494603601

theorem tailTrace_3153287 : CollatzResearch.WordTrace tailWord_3153287 prefixEnd_3153287 539717290858036494603601 := by
  unfold tailWord_3153287
  simp only [CollatzResearch.WordTrace]
  refine ⟨115009825327187212389466115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76673216884791474926310743 115009825327187212389466115)
  ·
    refine ⟨172514737990780818584199173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115009825327187212389466115 172514737990780818584199173)
    ·
      refine ⟨32346513373271403484537345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172514737990780818584199173 32346513373271403484537345)
      ·
        refine ⟨24259885029953552613403009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32346513373271403484537345 24259885029953552613403009)
        ·
          refine ⟨18194913772465164460052257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24259885029953552613403009 18194913772465164460052257)
          ·
            refine ⟨13646185329348873345039193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18194913772465164460052257 13646185329348873345039193)
            ·
              refine ⟨10234638997011655008779395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13646185329348873345039193 10234638997011655008779395)
              ·
                refine ⟨15351958495517482513169093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10234638997011655008779395 15351958495517482513169093)
                ·
                  refine ⟨2878492217909527971219205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15351958495517482513169093 2878492217909527971219205)
                  ·
                    refine ⟨539717290858036494603601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2878492217909527971219205 539717290858036494603601)
                    ·
                      rfl

theorem cell23_3153287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_3153287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153287 prefixEnd_3153287 := by exact prefixLift 3153287
  have htrace : WordTrace (prefixWord ++ tailWord_3153287) baseStart_3153287 baseEnd_3153287 := by
    simpa [prefixWord, tailWord_3153287, baseEnd_3153287] using wordTrace_append hprefix tailTrace_3153287
  have hstable : (prefixWord ++ tailWord_3153287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153287).length < 2 ^ (prefixWord ++ tailWord_3153287).sum := by decide
  have hdescent : baseEnd_3153287 < baseStart_3153287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153288 : List Nat := [2, 1, 3, 3, 1, 3, 3, 2, 1, 1, 3]
def baseStart_3153288 : Nat := 118140960795 + 3153288 * 2 ^ 59
def prefixEnd_3153288 : Nat := 4983230072969 + 3 ^ 40 * 3153288 * 2
def baseEnd_3153288 : Nat := 1619152386054763979898299

theorem tailTrace_3153288 : CollatzResearch.WordTrace tailWord_3153288 prefixEnd_3153288 1619152386054763979898299 := by
  unfold tailWord_3153288
  simp only [CollatzResearch.WordTrace]
  refine ⟨57504930900091794780126259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76673241200122393040168345 57504930900091794780126259)
  ·
    refine ⟨86257396350137692170189389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57504930900091794780126259 86257396350137692170189389)
    ·
      refine ⟨32346523631301634563821021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86257396350137692170189389 32346523631301634563821021)
      ·
        refine ⟨12129946361738112961432883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32346523631301634563821021 12129946361738112961432883)
        ·
          refine ⟨18194919542607169442149325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12129946361738112961432883 18194919542607169442149325)
          ·
            refine ⟨6823094828477688540805997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18194919542607169442149325 6823094828477688540805997)
            ·
              refine ⟨2558660560679133202802249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6823094828477688540805997 2558660560679133202802249)
              ·
                refine ⟨1918995420509349902101687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2558660560679133202802249 1918995420509349902101687)
                ·
                  refine ⟨2878493130764024853152531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918995420509349902101687 2878493130764024853152531)
                  ·
                    refine ⟨4317739696146037279728797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2878493130764024853152531 4317739696146037279728797)
                    ·
                      refine ⟨1619152386054763979898299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4317739696146037279728797 1619152386054763979898299)
                      ·
                        rfl

theorem cell23_3153288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_3153288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153288 prefixEnd_3153288 := by exact prefixLift 3153288
  have htrace : WordTrace (prefixWord ++ tailWord_3153288) baseStart_3153288 baseEnd_3153288 := by
    simpa [prefixWord, tailWord_3153288, baseEnd_3153288] using wordTrace_append hprefix tailTrace_3153288
  have hstable : (prefixWord ++ tailWord_3153288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153288).length < 2 ^ (prefixWord ++ tailWord_3153288).sum := by decide
  have hdescent : baseEnd_3153288 < baseStart_3153288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153308 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 1, 5]
def baseStart_3153308 : Nat := 118140960795 + 3153308 * 2 ^ 59
def prefixEnd_3153308 : Nat := 4983230072969 + 3 ^ 40 * 3153308 * 2
def baseEnd_3153308 : Nat := 539720885222617967216069

theorem tailTrace_3153308 : CollatzResearch.WordTrace tailWord_3153308 prefixEnd_3153308 539720885222617967216069 := by
  unfold tailWord_3153308
  simp only [CollatzResearch.WordTrace]
  refine ⟨57505295630055566487990289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76673727506740755317320385 57505295630055566487990289)
  ·
    refine ⟨43128971722541674865992717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57505295630055566487990289 43128971722541674865992717)
    ·
      refine ⟨16173364395953128074747269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43128971722541674865992717 16173364395953128074747269)
      ·
        refine ⟨3032505824241211514015113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16173364395953128074747269 3032505824241211514015113)
        ·
          refine ⟨2274379368180908635511335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3032505824241211514015113 2274379368180908635511335)
          ·
            refine ⟨3411569052271362953267003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274379368180908635511335 3411569052271362953267003)
            ·
              refine ⟨5117353578407044429900505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411569052271362953267003 5117353578407044429900505)
              ·
                refine ⟨3838015183805283322425379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5117353578407044429900505 3838015183805283322425379)
                ·
                  refine ⟨5757022775707924983638069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838015183805283322425379 5757022775707924983638069)
                  ·
                    refine ⟨539720885222617967216069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5757022775707924983638069 539720885222617967216069)
                    ·
                      rfl

theorem cell23_3153308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_3153308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153308 prefixEnd_3153308 := by exact prefixLift 3153308
  have htrace : WordTrace (prefixWord ++ tailWord_3153308) baseStart_3153308 baseEnd_3153308 := by
    simpa [prefixWord, tailWord_3153308, baseEnd_3153308] using wordTrace_append hprefix tailTrace_3153308
  have hstable : (prefixWord ++ tailWord_3153308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153308).length < 2 ^ (prefixWord ++ tailWord_3153308).sum := by decide
  have hdescent : baseEnd_3153308 < baseStart_3153308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153314 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_3153314 : Nat := 118140960795 + 3153314 * 2 ^ 59
def prefixEnd_3153314 : Nat := 4983230072969 + 3 ^ 40 * 3153314 * 2
def baseEnd_3153314 : Nat := 1619165736551780878173179

theorem tailTrace_3153314 : CollatzResearch.WordTrace tailWord_3153314 prefixEnd_3153314 1619165736551780878173179 := by
  unfold tailWord_3153314
  simp only [CollatzResearch.WordTrace]
  refine ⟨28752702524522349000174749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76673873398726264000465997 28752702524522349000174749)
  ·
    refine ⟨10782263446695880875065531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28752702524522349000174749 10782263446695880875065531)
    ·
      refine ⟨16173395170043821312598297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10782263446695880875065531 16173395170043821312598297)
      ·
        refine ⟨12130046377532865984448723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16173395170043821312598297 12130046377532865984448723)
        ·
          refine ⟨18195069566299298976673085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12130046377532865984448723 18195069566299298976673085)
          ·
            refine ⟨6823151087362237116252407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18195069566299298976673085 6823151087362237116252407)
            ·
              refine ⟨10234726631043355674378611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6823151087362237116252407 10234726631043355674378611)
              ·
                refine ⟨15352089946565033511567917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10234726631043355674378611 15352089946565033511567917)
                ·
                  refine ⟨5757033729961887566837969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15352089946565033511567917 5757033729961887566837969)
                  ·
                    refine ⟨4317775297471415675128477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5757033729961887566837969 4317775297471415675128477)
                    ·
                      refine ⟨1619165736551780878173179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4317775297471415675128477 1619165736551780878173179)
                      ·
                        rfl

theorem cell23_3153314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_3153314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153314 prefixEnd_3153314 := by exact prefixLift 3153314
  have htrace : WordTrace (prefixWord ++ tailWord_3153314) baseStart_3153314 baseEnd_3153314 := by
    simpa [prefixWord, tailWord_3153314, baseEnd_3153314] using wordTrace_append hprefix tailTrace_3153314
  have hstable : (prefixWord ++ tailWord_3153314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153314).length < 2 ^ (prefixWord ++ tailWord_3153314).sum := by decide
  have hdescent : baseEnd_3153314 < baseStart_3153314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153327 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 6, 1, 3]
def baseStart_3153327 : Nat := 118140960795 + 3153327 * 2 ^ 59
def prefixEnd_3153327 : Nat := 4983230072969 + 3 ^ 40 * 3153327 * 2
def baseEnd_3153327 : Nat := 1619172411800289327310619

theorem tailTrace_3153327 : CollatzResearch.WordTrace tailWord_3153327 prefixEnd_3153327 1619172411800289327310619 := by
  unfold tailWord_3153327
  simp only [CollatzResearch.WordTrace]
  refine ⟨115011284247042299220922235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76674189498028199480614823 115011284247042299220922235)
  ·
    refine ⟨172516926370563448831383353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115011284247042299220922235 172516926370563448831383353)
    ·
      refine ⟨129387694777922586623537515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172516926370563448831383353 129387694777922586623537515)
      ·
        refine ⟨194081542166883879935306273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129387694777922586623537515 194081542166883879935306273)
        ·
          refine ⟨145561156625162909951479705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194081542166883879935306273 145561156625162909951479705)
          ·
            refine ⟨109170867468872182463609779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145561156625162909951479705 109170867468872182463609779)
            ·
              refine ⟨163756301203308273695414669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109170867468872182463609779 163756301203308273695414669)
              ·
                refine ⟨61408612951240602635780501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163756301203308273695414669 61408612951240602635780501)
                ·
                  refine ⟨2878528732089403248552211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61408612951240602635780501 2878528732089403248552211)
                  ·
                    refine ⟨4317793098134104872828317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2878528732089403248552211 4317793098134104872828317)
                    ·
                      refine ⟨1619172411800289327310619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4317793098134104872828317 1619172411800289327310619)
                      ·
                        rfl

theorem cell23_3153327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 1, 3].length) (baseStart_3153327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153327 prefixEnd_3153327 := by exact prefixLift 3153327
  have htrace : WordTrace (prefixWord ++ tailWord_3153327) baseStart_3153327 baseEnd_3153327 := by
    simpa [prefixWord, tailWord_3153327, baseEnd_3153327] using wordTrace_append hprefix tailTrace_3153327
  have hstable : (prefixWord ++ tailWord_3153327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153327).length < 2 ^ (prefixWord ++ tailWord_3153327).sum := by decide
  have hdescent : baseEnd_3153327 < baseStart_3153327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153344 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 2, 1, 3]
def baseStart_3153344 : Nat := 118140960795 + 3153344 * 2 ^ 59
def prefixEnd_3153344 : Nat := 4983230072969 + 3 ^ 40 * 3153344 * 2
def baseEnd_3153344 : Nat := 1619181140971415760798041

theorem tailTrace_3153344 : CollatzResearch.WordTrace tailWord_3153344 prefixEnd_3153344 1619181140971415760798041 := by
  unfold tailWord_3153344
  simp only [CollatzResearch.WordTrace]
  refine ⟨57505952143990355562145543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76674602858653807416194057 57505952143990355562145543)
  ·
    refine ⟨86258928215985533343218315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57505952143990355562145543 86258928215985533343218315)
    ·
      refine ⟨129388392323978300014827473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86258928215985533343218315 129388392323978300014827473)
      ·
        refine ⟨97041294242983725011120605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129388392323978300014827473 97041294242983725011120605)
        ·
          refine ⟨36390485341118896879170227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97041294242983725011120605 36390485341118896879170227)
          ·
            refine ⟨54585728011678345318755341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36390485341118896879170227 54585728011678345318755341)
            ·
              refine ⟨20469648004379379494533253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54585728011678345318755341 20469648004379379494533253)
              ·
                refine ⟨3838059000821133655224985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20469648004379379494533253 3838059000821133655224985)
                ·
                  refine ⟨2878544250615850241418739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3838059000821133655224985 2878544250615850241418739)
                  ·
                    refine ⟨4317816375923775362128109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2878544250615850241418739 4317816375923775362128109)
                    ·
                      refine ⟨1619181140971415760798041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4317816375923775362128109 1619181140971415760798041)
                      ·
                        rfl

theorem cell23_3153344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_3153344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153344 prefixEnd_3153344 := by exact prefixLift 3153344
  have htrace : WordTrace (prefixWord ++ tailWord_3153344) baseStart_3153344 baseEnd_3153344 := by
    simpa [prefixWord, tailWord_3153344, baseEnd_3153344] using wordTrace_append hprefix tailTrace_3153344
  have hstable : (prefixWord ++ tailWord_3153344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153344).length < 2 ^ (prefixWord ++ tailWord_3153344).sum := by decide
  have hdescent : baseEnd_3153344 < baseStart_3153344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153354 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2]
def baseStart_3153354 : Nat := 118140960795 + 3153354 * 2 ^ 59
def prefixEnd_3153354 : Nat := 4983230072969 + 3 ^ 40 * 3153354 * 2
def baseEnd_3153354 : Nat := 1619186275777960721672995

theorem tailTrace_3153354 : CollatzResearch.WordTrace tailWord_3153354 prefixEnd_3153354 1619186275777960721672995 := by
  unfold tailWord_3153354
  simp only [CollatzResearch.WordTrace]
  refine ⟨28753067254486120708038779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76674846011962988554770077 28753067254486120708038779)
  ·
    refine ⟨43129600881729181062058169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28753067254486120708038779 43129600881729181062058169)
    ·
      refine ⟨32347200661296885796543627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43129600881729181062058169 32347200661296885796543627)
      ·
        refine ⟨48520800991945328694815441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32347200661296885796543627 48520800991945328694815441)
        ·
          refine ⟨36390600743958996521111581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48520800991945328694815441 36390600743958996521111581)
          ·
            refine ⟨13646475278984623695416843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36390600743958996521111581 13646475278984623695416843)
            ·
              refine ⟨20469712918476935543125265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13646475278984623695416843 20469712918476935543125265)
              ·
                refine ⟨15352284688857701657343949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20469712918476935543125265 15352284688857701657343949)
                ·
                  refine ⟨5757106758321638121503981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15352284688857701657343949 5757106758321638121503981)
                  ·
                    refine ⟨2158915034370614295563993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5757106758321638121503981 2158915034370614295563993)
                    ·
                      refine ⟨1619186275777960721672995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158915034370614295563993 1619186275777960721672995)
                      ·
                        rfl

theorem cell23_3153354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_3153354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153354 prefixEnd_3153354 := by exact prefixLift 3153354
  have htrace : WordTrace (prefixWord ++ tailWord_3153354) baseStart_3153354 baseEnd_3153354 := by
    simpa [prefixWord, tailWord_3153354, baseEnd_3153354] using wordTrace_append hprefix tailTrace_3153354
  have hstable : (prefixWord ++ tailWord_3153354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153354).length < 2 ^ (prefixWord ++ tailWord_3153354).sum := by decide
  have hdescent : baseEnd_3153354 < baseStart_3153354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153360 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 2, 6]
def baseStart_3153360 : Nat := 118140960795 + 3153360 * 2 ^ 59
def prefixEnd_3153360 : Nat := 4983230072969 + 3 ^ 40 * 3153360 * 2
def baseEnd_3153360 : Nat := 539729785553962566065989

theorem tailTrace_3153360 : CollatzResearch.WordTrace tailWord_3153360 prefixEnd_3153360 539729785553962566065989 := by
  unfold tailWord_3153360
  simp only [CollatzResearch.WordTrace]
  refine ⟨57506243927961372928436767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76674991903948497237915689 57506243927961372928436767)
  ·
    refine ⟨86259365891942059392655151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57506243927961372928436767 86259365891942059392655151)
    ·
      refine ⟨129389048837913089088982727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86259365891942059392655151 129389048837913089088982727)
      ·
        refine ⟨194083573256869633633474091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129389048837913089088982727 194083573256869633633474091)
        ·
          refine ⟨291125359885304450450211137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194083573256869633633474091 291125359885304450450211137)
          ·
            refine ⟨218344019913978337837658353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291125359885304450450211137 218344019913978337837658353)
            ·
              refine ⟨163758014935483753378243765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218344019913978337837658353 163758014935483753378243765)
              ·
                refine ⟨15352313900201601879210353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163758014935483753378243765 15352313900201601879210353)
                ·
                  refine ⟨11514235425151201409407765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15352313900201601879210353 11514235425151201409407765)
                  ·
                    refine ⟨539729785553962566065989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11514235425151201409407765 539729785553962566065989)
                    ·
                      rfl

theorem cell23_3153360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_3153360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153360 prefixEnd_3153360 := by exact prefixLift 3153360
  have htrace : WordTrace (prefixWord ++ tailWord_3153360) baseStart_3153360 baseEnd_3153360 := by
    simpa [prefixWord, tailWord_3153360, baseEnd_3153360] using wordTrace_append hprefix tailTrace_3153360
  have hstable : (prefixWord ++ tailWord_3153360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153360).length < 2 ^ (prefixWord ++ tailWord_3153360).sum := by decide
  have hdescent : baseEnd_3153360 < baseStart_3153360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153384 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_3153384 : Nat := 118140960795 + 3153384 * 2 ^ 59
def prefixEnd_3153384 : Nat := 4983230072969 + 3 ^ 40 * 3153384 * 2
def baseEnd_3153384 : Nat := 1619201680197595604297857

theorem tailTrace_3153384 : CollatzResearch.WordTrace tailWord_3153384 prefixEnd_3153384 1619201680197595604297857 := by
  unfold tailWord_3153384
  simp only [CollatzResearch.WordTrace]
  refine ⟨57506681603917898977873603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76675575471890531970498137 57506681603917898977873603)
  ·
    refine ⟨86260022405876848466810405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57506681603917898977873603 86260022405876848466810405)
    ·
      refine ⟨16173754201101909087526951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86260022405876848466810405 16173754201101909087526951)
      ·
        refine ⟨24260631301652863631290427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16173754201101909087526951 24260631301652863631290427)
        ·
          refine ⟨36390946952479295446935641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24260631301652863631290427 36390946952479295446935641)
          ·
            refine ⟨27293210214359471585201731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36390946952479295446935641 27293210214359471585201731)
            ·
              refine ⟨40939815321539207377802597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27293210214359471585201731 40939815321539207377802597)
              ·
                refine ⟨7676215372788601383337987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40939815321539207377802597 7676215372788601383337987)
                ·
                  refine ⟨11514323059182902075006981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7676215372788601383337987 11514323059182902075006981)
                  ·
                    refine ⟨2158935573596794139063809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11514323059182902075006981 2158935573596794139063809)
                    ·
                      refine ⟨1619201680197595604297857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2158935573596794139063809 1619201680197595604297857)
                      ·
                        rfl

theorem cell23_3153384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_3153384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153384 prefixEnd_3153384 := by exact prefixLift 3153384
  have htrace : WordTrace (prefixWord ++ tailWord_3153384) baseStart_3153384 baseEnd_3153384 := by
    simpa [prefixWord, tailWord_3153384, baseEnd_3153384] using wordTrace_append hprefix tailTrace_3153384
  have hstable : (prefixWord ++ tailWord_3153384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153384).length < 2 ^ (prefixWord ++ tailWord_3153384).sum := by decide
  have hdescent : baseEnd_3153384 < baseStart_3153384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153417 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 2, 3, 3]
def baseStart_3153417 : Nat := 118140960795 + 3153417 * 2 ^ 59
def prefixEnd_3153417 : Nat := 4983230072969 + 3 ^ 40 * 3153417 * 2
def baseEnd_3153417 : Nat := 1619218625059193975185205

theorem tailTrace_3153417 : CollatzResearch.WordTrace tailWord_3153417 prefixEnd_3153417 1619218625059193975185205 := by
  unfold tailWord_3153417
  simp only [CollatzResearch.WordTrace]
  refine ⟨115014566816716244591698505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76676377877810829727799003 115014566816716244591698505)
  ·
    refine ⟨86260925112537183443773879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115014566816716244591698505 86260925112537183443773879)
    ·
      refine ⟨129391387668805775165660819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86260925112537183443773879 129391387668805775165660819)
      ·
        refine ⟨194087081503208662748491229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129391387668805775165660819 194087081503208662748491229)
        ·
          refine ⟨72782655563703248530684211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194087081503208662748491229 72782655563703248530684211)
          ·
            refine ⟨109173983345554872796026317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72782655563703248530684211 109173983345554872796026317)
            ·
              refine ⟨40940243754583077298509869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109173983345554872796026317 40940243754583077298509869)
              ·
                refine ⟨15352591407968653986941201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40940243754583077298509869 15352591407968653986941201)
                ·
                  refine ⟨11514443555976490490205901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15352591407968653986941201 11514443555976490490205901)
                  ·
                    refine ⟨4317916333491183933827213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11514443555976490490205901 4317916333491183933827213)
                    ·
                      refine ⟨1619218625059193975185205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4317916333491183933827213 1619218625059193975185205)
                      ·
                        rfl

theorem cell23_3153417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3, 3].length) (baseStart_3153417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153417 prefixEnd_3153417 := by exact prefixLift 3153417
  have htrace : WordTrace (prefixWord ++ tailWord_3153417) baseStart_3153417 baseEnd_3153417 := by
    simpa [prefixWord, tailWord_3153417, baseEnd_3153417] using wordTrace_append hprefix tailTrace_3153417
  have hstable : (prefixWord ++ tailWord_3153417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153417).length < 2 ^ (prefixWord ++ tailWord_3153417).sum := by decide
  have hdescent : baseEnd_3153417 < baseStart_3153417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153437 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_3153437 : Nat := 118140960795 + 3153437 * 2 ^ 59
def prefixEnd_3153437 : Nat := 4983230072969 + 3 ^ 40 * 3153437 * 2
def baseEnd_3153437 : Nat := 539742964890761298978371

theorem tailTrace_3153437 : CollatzResearch.WordTrace tailWord_3153437 prefixEnd_3153437 539742964890761298978371 := by
  unfold tailWord_3153437
  simp only [CollatzResearch.WordTrace]
  refine ⟨115015296276643788007426565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76676864184429192004951043 115015296276643788007426565)
  ·
    refine ⟨21565368051870710251392481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115015296276643788007426565 21565368051870710251392481)
    ·
      refine ⟨16174026038903032688544361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21565368051870710251392481 16174026038903032688544361)
      ·
        refine ⟨12130519529177274516408271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16174026038903032688544361 12130519529177274516408271)
        ·
          refine ⟨18195779293765911774612407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12130519529177274516408271 18195779293765911774612407)
          ·
            refine ⟨27293668940648867661918611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18195779293765911774612407 27293668940648867661918611)
            ·
              refine ⟨40940503410973301492877917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27293668940648867661918611 40940503410973301492877917)
              ·
                refine ⟨15352688779114988059829219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40940503410973301492877917 15352688779114988059829219)
                ·
                  refine ⟨23029033168672482089743829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15352688779114988059829219 23029033168672482089743829)
                  ·
                    refine ⟨539742964890761298978371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23029033168672482089743829 539742964890761298978371)
                    ·
                      rfl

theorem cell23_3153437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_3153437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153437 prefixEnd_3153437 := by exact prefixLift 3153437
  have htrace : WordTrace (prefixWord ++ tailWord_3153437) baseStart_3153437 baseEnd_3153437 := by
    simpa [prefixWord, tailWord_3153437, baseEnd_3153437] using wordTrace_append hprefix tailTrace_3153437
  have hstable : (prefixWord ++ tailWord_3153437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153437).length < 2 ^ (prefixWord ++ tailWord_3153437).sum := by decide
  have hdescent : baseEnd_3153437 < baseStart_3153437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153441 : List Nat := [1, 2, 3, 2, 2, 4, 1, 3, 5]
def baseStart_3153441 : Nat := 118140960795 + 3153441 * 2 ^ 59
def prefixEnd_3153441 : Nat := 4983230072969 + 3 ^ 40 * 3153441 * 2
def baseEnd_3153441 : Nat := 179914549843877986809455

theorem tailTrace_3153441 : CollatzResearch.WordTrace tailWord_3153441 prefixEnd_3153441 179914549843877986809455 := by
  unfold tailWord_3153441
  simp only [CollatzResearch.WordTrace]
  refine ⟨115015442168629296690572177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76676961445752864460381451 115015442168629296690572177)
  ·
    refine ⟨86261581626471972517929133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115015442168629296690572177 86261581626471972517929133)
    ·
      refine ⟨32348093109926989694223425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86261581626471972517929133 32348093109926989694223425)
      ·
        refine ⟨24261069832445242270667569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32348093109926989694223425 24261069832445242270667569)
        ·
          refine ⟨18195802374333931703000677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24261069832445242270667569 18195802374333931703000677)
          ·
            refine ⟨3411712945187612194312627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18195802374333931703000677 3411712945187612194312627)
            ·
              refine ⟨5117569417781418291468941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411712945187612194312627 5117569417781418291468941)
              ·
                refine ⟨1919088531668031859300853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5117569417781418291468941 1919088531668031859300853)
                ·
                  refine ⟨179914549843877986809455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1919088531668031859300853 179914549843877986809455)
                  ·
                    rfl

theorem cell23_3153441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 5].length) (baseStart_3153441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153441 prefixEnd_3153441 := by exact prefixLift 3153441
  have htrace : WordTrace (prefixWord ++ tailWord_3153441) baseStart_3153441 baseEnd_3153441 := by
    simpa [prefixWord, tailWord_3153441, baseEnd_3153441] using wordTrace_append hprefix tailTrace_3153441
  have hstable : (prefixWord ++ tailWord_3153441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153441).length < 2 ^ (prefixWord ++ tailWord_3153441).sum := by decide
  have hdescent : baseEnd_3153441 < baseStart_3153441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153454 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3153454 : Nat := 118140960795 + 3153454 * 2 ^ 59
def prefixEnd_3153454 : Nat := 4983230072969 + 3 ^ 40 * 3153454 * 2
def baseEnd_3153454 : Nat := 539745874614470110140845

theorem tailTrace_3153454 : CollatzResearch.WordTrace tailWord_3153454 prefixEnd_3153454 539745874614470110140845 := by
  unfold tailWord_3153454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14376989539697774988849427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76677277545054799940530277 14376989539697774988849427)
  ·
    refine ⟨21565484309546662483274141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14376989539697774988849427 21565484309546662483274141)
    ·
      refine ⟨8087056616079998431227803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21565484309546662483274141 8087056616079998431227803)
      ·
        refine ⟨12130584924119997646841705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8087056616079998431227803 12130584924119997646841705)
        ·
          refine ⟨9097938693089998235131279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12130584924119997646841705 9097938693089998235131279)
          ·
            refine ⟨13646908039634997352696919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9097938693089998235131279 13646908039634997352696919)
            ·
              refine ⟨20470362059452496029045379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13646908039634997352696919 20470362059452496029045379)
              ·
                refine ⟨30705543089178744043568069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20470362059452496029045379 30705543089178744043568069)
                ·
                  refine ⟨5757289329221014508169013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30705543089178744043568069 5757289329221014508169013)
                  ·
                    refine ⟨539745874614470110140845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5757289329221014508169013 539745874614470110140845)
                    ·
                      rfl

theorem cell23_3153454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3153454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153454 prefixEnd_3153454 := by exact prefixLift 3153454
  have htrace : WordTrace (prefixWord ++ tailWord_3153454) baseStart_3153454 baseEnd_3153454 := by
    simpa [prefixWord, tailWord_3153454, baseEnd_3153454] using wordTrace_append hprefix tailTrace_3153454
  have hstable : (prefixWord ++ tailWord_3153454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153454).length < 2 ^ (prefixWord ++ tailWord_3153454).sum := by decide
  have hdescent : baseEnd_3153454 < baseStart_3153454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153514 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 6]
def baseStart_3153514 : Nat := 118140960795 + 3153514 * 2 ^ 59
def prefixEnd_3153514 : Nat := 4983230072969 + 3 ^ 40 * 3153514 * 2
def baseEnd_3153514 : Nat := 179918714742520010630251

theorem tailTrace_3153514 : CollatzResearch.WordTrace tailWord_3153514 prefixEnd_3153514 179918714742520010630251 := by
  unfold tailWord_3153514
  simp only [CollatzResearch.WordTrace]
  refine ⟨28754526174341207539494899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76678736464909886771986397 28754526174341207539494899)
  ·
    refine ⟨43131789261511811309242349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28754526174341207539494899 43131789261511811309242349)
    ·
      refine ⟨16174420973066929240965881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43131789261511811309242349 16174420973066929240965881)
      ·
        refine ⟨12130815729800196930724411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16174420973066929240965881 12130815729800196930724411)
        ·
          refine ⟨18196223594700295396086617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12130815729800196930724411 18196223594700295396086617)
          ·
            refine ⟨13647167696025221547064963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18196223594700295396086617 13647167696025221547064963)
            ·
              refine ⟨20470751544037832320597445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13647167696025221547064963 20470751544037832320597445)
              ·
                refine ⟨3838265914507093560112021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20470751544037832320597445 3838265914507093560112021)
                ·
                  refine ⟨179918714742520010630251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3838265914507093560112021 179918714742520010630251)
                  ·
                    rfl

theorem cell23_3153514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_3153514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153514 prefixEnd_3153514 := by exact prefixLift 3153514
  have htrace : WordTrace (prefixWord ++ tailWord_3153514) baseStart_3153514 baseEnd_3153514 := by
    simpa [prefixWord, tailWord_3153514, baseEnd_3153514] using wordTrace_append hprefix tailTrace_3153514
  have hstable : (prefixWord ++ tailWord_3153514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153514).length < 2 ^ (prefixWord ++ tailWord_3153514).sum := by decide
  have hdescent : baseEnd_3153514 < baseStart_3153514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153541 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 3, 1, 3]
def baseStart_3153541 : Nat := 118140960795 + 3153541 * 2 ^ 59
def prefixEnd_3153541 : Nat := 4983230072969 + 3 ^ 40 * 3153541 * 2
def baseEnd_3153541 : Nat := 1619282296660351490034635

theorem tailTrace_3153541 : CollatzResearch.WordTrace tailWord_3153541 prefixEnd_3153541 1619282296660351490034635 := by
  unfold tailWord_3153541
  simp only [CollatzResearch.WordTrace]
  refine ⟨115019089468267013769212477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76679392978844675846141651 115019089468267013769212477)
  ·
    refine ⟨43132158550600130163454679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115019089468267013769212477 43132158550600130163454679)
    ·
      refine ⟨64698237825900195245182019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43132158550600130163454679 64698237825900195245182019)
      ·
        refine ⟨97047356738850292867773029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64698237825900195245182019 97047356738850292867773029)
        ·
          refine ⟨18196379388534429912707443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97047356738850292867773029 18196379388534429912707443)
          ·
            refine ⟨27294569082801644869061165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18196379388534429912707443 27294569082801644869061165)
            ·
              refine ⟨10235463406050616825897937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27294569082801644869061165 10235463406050616825897937)
              ·
                refine ⟨7676597554537962619423453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10235463406050616825897937 7676597554537962619423453)
                ·
                  refine ⟨2878724082951735982283795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7676597554537962619423453 2878724082951735982283795)
                  ·
                    refine ⟨4318086124427603973425693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2878724082951735982283795 4318086124427603973425693)
                    ·
                      refine ⟨1619282296660351490034635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4318086124427603973425693 1619282296660351490034635)
                      ·
                        rfl

theorem cell23_3153541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_3153541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153541 prefixEnd_3153541 := by exact prefixLift 3153541
  have htrace : WordTrace (prefixWord ++ tailWord_3153541) baseStart_3153541 baseEnd_3153541 := by
    simpa [prefixWord, tailWord_3153541, baseEnd_3153541] using wordTrace_append hprefix tailTrace_3153541
  have hstable : (prefixWord ++ tailWord_3153541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153541).length < 2 ^ (prefixWord ++ tailWord_3153541).sum := by decide
  have hdescent : baseEnd_3153541 < baseStart_3153541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153584 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 3]
def baseStart_3153584 : Nat := 118140960795 + 3153584 * 2 ^ 59
def prefixEnd_3153584 : Nat := 4983230072969 + 3 ^ 40 * 3153584 * 2
def baseEnd_3153584 : Nat := 1619304376328494821796937

theorem tailTrace_3153584 : CollatzResearch.WordTrace tailWord_3153584 prefixEnd_3153584 1619304376328494821796937 := by
  unfold tailWord_3153584
  simp only [CollatzResearch.WordTrace]
  refine ⟨57510328903555616056513903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76680438538074154742018537 57510328903555616056513903)
  ·
    refine ⟨86265493355333424084770855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57510328903555616056513903 86265493355333424084770855)
    ·
      refine ⟨129398240033000136127156283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86265493355333424084770855 129398240033000136127156283)
      ·
        refine ⟨194097360049500204190734425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129398240033000136127156283 194097360049500204190734425)
        ·
          refine ⟨145573020037125153143050819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194097360049500204190734425 145573020037125153143050819)
          ·
            refine ⟨218359530055687729714576229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145573020037125153143050819 218359530055687729714576229)
            ·
              refine ⟨40942411885441449321483043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218359530055687729714576229 40942411885441449321483043)
              ·
                refine ⟨61413617828162173982224565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40942411885441449321483043 61413617828162173982224565)
                ·
                  refine ⟨5757526671390203810833553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61413617828162173982224565 5757526671390203810833553)
                  ·
                    refine ⟨4318145003542652858125165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5757526671390203810833553 4318145003542652858125165)
                    ·
                      refine ⟨1619304376328494821796937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4318145003542652858125165 1619304376328494821796937)
                      ·
                        rfl

theorem cell23_3153584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 3].length) (baseStart_3153584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153584 prefixEnd_3153584 := by exact prefixLift 3153584
  have htrace : WordTrace (prefixWord ++ tailWord_3153584) baseStart_3153584 baseEnd_3153584 := by
    simpa [prefixWord, tailWord_3153584, baseEnd_3153584] using wordTrace_append hprefix tailTrace_3153584
  have hstable : (prefixWord ++ tailWord_3153584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153584).length < 2 ^ (prefixWord ++ tailWord_3153584).sum := by decide
  have hdescent : baseEnd_3153584 < baseStart_3153584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153587 : List Nat := [1, 1, 1, 2, 3, 3, 2, 10]
def baseStart_3153587 : Nat := 118140960795 + 3153587 * 2 ^ 59
def prefixEnd_3153587 : Nat := 4983230072969 + 3 ^ 40 * 3153587 * 2
def baseEnd_3153587 : Nat := 59974293213720678150349

theorem tailTrace_3153587 : CollatzResearch.WordTrace tailWord_3153587 prefixEnd_3153587 59974293213720678150349 := by
  unfold tailWord_3153587
  simp only [CollatzResearch.WordTrace]
  refine ⟨115020767226100363625387015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76680511484066909083591343 115020767226100363625387015)
  ·
    refine ⟨172531150839150545438080523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115020767226100363625387015 172531150839150545438080523)
    ·
      refine ⟨258796726258725818157120785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172531150839150545438080523 258796726258725818157120785)
      ·
        refine ⟨194097544694044363617840589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258796726258725818157120785 194097544694044363617840589)
        ·
          refine ⟨72786579260266636356690221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194097544694044363617840589 72786579260266636356690221)
          ·
            refine ⟨27294967222599988633758833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72786579260266636356690221 27294967222599988633758833)
            ·
              refine ⟨20471225416949991475319125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27294967222599988633758833 20471225416949991475319125)
              ·
                refine ⟨59974293213720678150349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20471225416949991475319125 59974293213720678150349)
                ·
                  rfl

theorem cell23_3153587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 10].length) (baseStart_3153587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153587 prefixEnd_3153587 := by exact prefixLift 3153587
  have htrace : WordTrace (prefixWord ++ tailWord_3153587) baseStart_3153587 baseEnd_3153587 := by
    simpa [prefixWord, tailWord_3153587, baseEnd_3153587] using wordTrace_append hprefix tailTrace_3153587
  have hstable : (prefixWord ++ tailWord_3153587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153587).length < 2 ^ (prefixWord ++ tailWord_3153587).sum := by decide
  have hdescent : baseEnd_3153587 < baseStart_3153587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153591 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 1, 6]
def baseStart_3153591 : Nat := 118140960795 + 3153591 * 2 ^ 59
def prefixEnd_3153591 : Nat := 4983230072969 + 3 ^ 40 * 3153591 * 2
def baseEnd_3153591 : Nat := 539769323564358764803135

theorem tailTrace_3153591 : CollatzResearch.WordTrace tailWord_3153591 prefixEnd_3153591 539769323564358764803135 := by
  unfold tailWord_3153591
  simp only [CollatzResearch.WordTrace]
  refine ⟨115020913118085872308532627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76680608745390581539021751 115020913118085872308532627)
  ·
    refine ⟨172531369677128808462798941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115020913118085872308532627 172531369677128808462798941)
    ·
      refine ⟨64699263628923303173549603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172531369677128808462798941 64699263628923303173549603)
      ·
        refine ⟨97048895443384954760324405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64699263628923303173549603 97048895443384954760324405)
        ·
          refine ⟨9098333947817339508780413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97048895443384954760324405 9098333947817339508780413)
          ·
            refine ⟨3411875230431502315792655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9098333947817339508780413 3411875230431502315792655)
            ·
              refine ⟨5117812845647253473688983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411875230431502315792655 5117812845647253473688983)
              ·
                refine ⟨7676719268470880210533475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117812845647253473688983 7676719268470880210533475)
                ·
                  refine ⟨11515078902706320315800213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7676719268470880210533475 11515078902706320315800213)
                  ·
                    refine ⟨539769323564358764803135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11515078902706320315800213 539769323564358764803135)
                    ·
                      rfl

theorem cell23_3153591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_3153591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153591 prefixEnd_3153591 := by exact prefixLift 3153591
  have htrace : WordTrace (prefixWord ++ tailWord_3153591) baseStart_3153591 baseEnd_3153591 := by
    simpa [prefixWord, tailWord_3153591, baseEnd_3153591] using wordTrace_append hprefix tailTrace_3153591
  have hstable : (prefixWord ++ tailWord_3153591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153591).length < 2 ^ (prefixWord ++ tailWord_3153591).sum := by decide
  have hdescent : baseEnd_3153591 < baseStart_3153591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153594 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_3153594 : Nat := 118140960795 + 3153594 * 2 ^ 59
def prefixEnd_3153594 : Nat := 4983230072969 + 3 ^ 40 * 3153594 * 2
def baseEnd_3153594 : Nat := 1619309511135039782671891

theorem tailTrace_3153594 : CollatzResearch.WordTrace tailWord_3153594 prefixEnd_3153594 1619309511135039782671891 := by
  unfold tailWord_3153594
  simp only [CollatzResearch.WordTrace]
  refine ⟨28755255634268750955222959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76680681691383335880594557 28755255634268750955222959)
  ·
    refine ⟨43132883451403126432834439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28755255634268750955222959 43132883451403126432834439)
    ·
      refine ⟨64699325177104689649251659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43132883451403126432834439 64699325177104689649251659)
      ·
        refine ⟨97048987765657034473877489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64699325177104689649251659 97048987765657034473877489)
        ·
          refine ⟨72786740824242775855408117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97048987765657034473877489 72786740824242775855408117)
          ·
            refine ⟨6823756952272760236444511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72786740824242775855408117 6823756952272760236444511)
            ·
              refine ⟨10235635428409140354666767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6823756952272760236444511 10235635428409140354666767)
              ·
                refine ⟨15353453142613710532000151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10235635428409140354666767 15353453142613710532000151)
                ·
                  refine ⟨23030179713920565798000227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15353453142613710532000151 23030179713920565798000227)
                  ·
                    refine ⟨34545269570880848697000341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23030179713920565798000227 34545269570880848697000341)
                    ·
                      refine ⟨1619309511135039782671891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34545269570880848697000341 1619309511135039782671891)
                      ·
                        rfl

theorem cell23_3153594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_3153594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153594 prefixEnd_3153594 := by exact prefixLift 3153594
  have htrace : WordTrace (prefixWord ++ tailWord_3153594) baseStart_3153594 baseEnd_3153594 := by
    simpa [prefixWord, tailWord_3153594, baseEnd_3153594] using wordTrace_append hprefix tailTrace_3153594
  have hstable : (prefixWord ++ tailWord_3153594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153594).length < 2 ^ (prefixWord ++ tailWord_3153594).sum := by decide
  have hdescent : baseEnd_3153594 < baseStart_3153594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153598 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_3153598 : Nat := 118140960795 + 3153598 * 2 ^ 59
def prefixEnd_3153598 : Nat := 4983230072969 + 3 ^ 40 * 3153598 * 2
def baseEnd_3153598 : Nat := 1619311565057657767021873

theorem tailTrace_3153598 : CollatzResearch.WordTrace tailWord_3153598 prefixEnd_3153598 1619311565057657767021873 := by
  unfold tailWord_3153598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14377646053632564063004681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76680778952707008336024965 14377646053632564063004681)
  ·
    refine ⟨10783234540224423047253511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14377646053632564063004681 10783234540224423047253511)
    ·
      refine ⟨16174851810336634570880267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10783234540224423047253511 16174851810336634570880267)
      ·
        refine ⟨24262277715504951856320401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16174851810336634570880267 24262277715504951856320401)
        ·
          refine ⟨18196708286628713892240301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24262277715504951856320401 18196708286628713892240301)
          ·
            refine ⟨6823765607485767709590113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18196708286628713892240301 6823765607485767709590113)
            ·
              refine ⟨5117824205614325782192585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6823765607485767709590113 5117824205614325782192585)
              ·
                refine ⟨3838368154210744336644439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5117824205614325782192585 3838368154210744336644439)
                ·
                  refine ⟨5757552231316116504966659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838368154210744336644439 5757552231316116504966659)
                  ·
                    refine ⟨8636328346974174757449989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5757552231316116504966659 8636328346974174757449989)
                    ·
                      refine ⟨1619311565057657767021873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8636328346974174757449989 1619311565057657767021873)
                      ·
                        rfl

theorem cell23_3153598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_3153598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153598 prefixEnd_3153598 := by exact prefixLift 3153598
  have htrace : WordTrace (prefixWord ++ tailWord_3153598) baseStart_3153598 baseEnd_3153598 := by
    simpa [prefixWord, tailWord_3153598, baseEnd_3153598] using wordTrace_append hprefix tailTrace_3153598
  have hstable : (prefixWord ++ tailWord_3153598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153598).length < 2 ^ (prefixWord ++ tailWord_3153598).sum := by decide
  have hdescent : baseEnd_3153598 < baseStart_3153598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153604 : List Nat := [2, 3, 3, 1, 1, 1, 3, 9]
def baseStart_3153604 : Nat := 118140960795 + 3153604 * 2 ^ 59
def prefixEnd_3153604 : Nat := 4983230072969 + 3 ^ 40 * 3153604 * 2
def baseEnd_3153604 : Nat := 59974616516354990501735

theorem tailTrace_3153604 : CollatzResearch.WordTrace tailWord_3153604 prefixEnd_3153604 59974616516354990501735 := by
  unfold tailWord_3153604
  simp only [CollatzResearch.WordTrace]
  refine ⟨57510693633519387764377933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76680924844692517019170577 57510693633519387764377933)
  ·
    refine ⟨21566510112569770411641725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57510693633519387764377933 21566510112569770411641725)
    ·
      refine ⟨8087441292213663904365647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21566510112569770411641725 8087441292213663904365647)
      ·
        refine ⟨12131161938320495856548471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8087441292213663904365647 12131161938320495856548471)
        ·
          refine ⟨18196742907480743784822707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12131161938320495856548471 18196742907480743784822707)
          ·
            refine ⟨27295114361221115677234061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18196742907480743784822707 27295114361221115677234061)
            ·
              refine ⟨10235667885457918378962773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27295114361221115677234061 10235667885457918378962773)
              ·
                refine ⟨59974616516354990501735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10235667885457918378962773 59974616516354990501735)
                ·
                  rfl

theorem cell23_3153604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 9].length) (baseStart_3153604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153604 prefixEnd_3153604 := by exact prefixLift 3153604
  have htrace : WordTrace (prefixWord ++ tailWord_3153604) baseStart_3153604 baseEnd_3153604 := by
    simpa [prefixWord, tailWord_3153604, baseEnd_3153604] using wordTrace_append hprefix tailTrace_3153604
  have hstable : (prefixWord ++ tailWord_3153604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153604).length < 2 ^ (prefixWord ++ tailWord_3153604).sum := by decide
  have hdescent : baseEnd_3153604 < baseStart_3153604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153618 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_3153618 : Nat := 118140960795 + 3153618 * 2 ^ 59
def prefixEnd_3153618 : Nat := 4983230072969 + 3 ^ 40 * 3153618 * 2
def baseEnd_3153618 : Nat := 1619321834670747688771781

theorem tailTrace_3153618 : CollatzResearch.WordTrace tailWord_3153618 prefixEnd_3153618 1619321834670747688771781 := by
  unfold tailWord_3153618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28755474472247013979941377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76681265259325370613177005 28755474472247013979941377)
  ·
    refine ⟨21566605854185260484956033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28755474472247013979941377 21566605854185260484956033)
    ·
      refine ⟨16174954390638945363717025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21566605854185260484956033 16174954390638945363717025)
      ·
        refine ⟨12131215792979209022787769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16174954390638945363717025 12131215792979209022787769)
        ·
          refine ⟨9098411844734406767090827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12131215792979209022787769 9098411844734406767090827)
          ·
            refine ⟨13647617767101610150636241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9098411844734406767090827 13647617767101610150636241)
            ·
              refine ⟨10235713325326207612977181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13647617767101610150636241 10235713325326207612977181)
              ·
                refine ⟨3838392496997327854866443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10235713325326207612977181 3838392496997327854866443)
                ·
                  refine ⟨5757588745495991782299665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838392496997327854866443 5757588745495991782299665)
                  ·
                    refine ⟨4318191559121993836724749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5757588745495991782299665 4318191559121993836724749)
                    ·
                      refine ⟨1619321834670747688771781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4318191559121993836724749 1619321834670747688771781)
                      ·
                        rfl

theorem cell23_3153618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_3153618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153618 prefixEnd_3153618 := by exact prefixLift 3153618
  have htrace : WordTrace (prefixWord ++ tailWord_3153618) baseStart_3153618 baseEnd_3153618 := by
    simpa [prefixWord, tailWord_3153618, baseEnd_3153618] using wordTrace_append hprefix tailTrace_3153618
  have hstable : (prefixWord ++ tailWord_3153618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153618).length < 2 ^ (prefixWord ++ tailWord_3153618).sum := by decide
  have hdescent : baseEnd_3153618 < baseStart_3153618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153627 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 7]
def baseStart_3153627 : Nat := 118140960795 + 3153627 * 2 ^ 59
def prefixEnd_3153627 : Nat := 4983230072969 + 3 ^ 40 * 3153627 * 2
def baseEnd_3153627 : Nat := 1619326455996638153559239

theorem tailTrace_3153627 : CollatzResearch.WordTrace tailWord_3153627 prefixEnd_3153627 1619326455996638153559239 := by
  unfold tailWord_3153627
  simp only [CollatzResearch.WordTrace]
  refine ⟨115022226145955450456843135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76681484097303633637895423 115022226145955450456843135)
  ·
    refine ⟨172533339218933175685264703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115022226145955450456843135 172533339218933175685264703)
    ·
      refine ⟨258800008828399763527897055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172533339218933175685264703 258800008828399763527897055)
      ·
        refine ⟨388200013242599645291845583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258800008828399763527897055 388200013242599645291845583)
        ·
          refine ⟨582300019863899467937768375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388200013242599645291845583 582300019863899467937768375)
          ·
            refine ⟨873450029795849201906652563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582300019863899467937768375 873450029795849201906652563)
            ·
              refine ⟨1310175044693773802859978845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873450029795849201906652563 1310175044693773802859978845)
              ·
                refine ⟨491315641760165176072492067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1310175044693773802859978845 491315641760165176072492067)
                ·
                  refine ⟨736973462640247764108738101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491315641760165176072492067 736973462640247764108738101)
                  ·
                    refine ⟨69091262122523227885194197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 736973462640247764108738101 69091262122523227885194197)
                    ·
                      refine ⟨1619326455996638153559239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69091262122523227885194197 1619326455996638153559239)
                      ·
                        rfl

theorem cell23_3153627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_3153627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153627 prefixEnd_3153627 := by exact prefixLift 3153627
  have htrace : WordTrace (prefixWord ++ tailWord_3153627) baseStart_3153627 baseEnd_3153627 := by
    simpa [prefixWord, tailWord_3153627, baseEnd_3153627] using wordTrace_append hprefix tailTrace_3153627
  have hstable : (prefixWord ++ tailWord_3153627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153627).length < 2 ^ (prefixWord ++ tailWord_3153627).sum := by decide
  have hdescent : baseEnd_3153627 < baseStart_3153627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153631 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 4, 1, 3]
def baseStart_3153631 : Nat := 118140960795 + 3153631 * 2 ^ 59
def prefixEnd_3153631 : Nat := 4983230072969 + 3 ^ 40 * 3153631 * 2
def baseEnd_3153631 : Nat := 1619328509919256137909221

theorem tailTrace_3153631 : CollatzResearch.WordTrace tailWord_3153631 prefixEnd_3153631 1619328509919256137909221 := by
  unfold tailWord_3153631
  simp only [CollatzResearch.WordTrace]
  refine ⟨115022372037940959139988747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76681581358627306093325831 115022372037940959139988747)
  ·
    refine ⟨172533558056911438709983121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115022372037940959139988747 172533558056911438709983121)
    ·
      refine ⟨129400168542683579032487341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172533558056911438709983121 129400168542683579032487341)
      ·
        refine ⟨48525063203506342137182753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129400168542683579032487341 48525063203506342137182753)
        ·
          refine ⟨36393797402629756602887065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48525063203506342137182753 36393797402629756602887065)
          ·
            refine ⟨27295348051972317452165299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36393797402629756602887065 27295348051972317452165299)
            ·
              refine ⟨40943022077958476178247949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27295348051972317452165299 40943022077958476178247949)
              ·
                refine ⟨15353633279234428566842981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40943022077958476178247949 15353633279234428566842981)
                ·
                  refine ⟨2878806239856455356283059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15353633279234428566842981 2878806239856455356283059)
                  ·
                    refine ⟨4318209359784683034424589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2878806239856455356283059 4318209359784683034424589)
                    ·
                      refine ⟨1619328509919256137909221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4318209359784683034424589 1619328509919256137909221)
                      ·
                        rfl

theorem cell23_3153631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_3153631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153631 prefixEnd_3153631 := by exact prefixLift 3153631
  have htrace : WordTrace (prefixWord ++ tailWord_3153631) baseStart_3153631 baseEnd_3153631 := by
    simpa [prefixWord, tailWord_3153631, baseEnd_3153631] using wordTrace_append hprefix tailTrace_3153631
  have hstable : (prefixWord ++ tailWord_3153631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153631).length < 2 ^ (prefixWord ++ tailWord_3153631).sum := by decide
  have hdescent : baseEnd_3153631 < baseStart_3153631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153641 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 3, 3, 2]
def baseStart_3153641 : Nat := 118140960795 + 3153641 * 2 ^ 59
def prefixEnd_3153641 : Nat := 4983230072969 + 3 ^ 40 * 3153641 * 2
def baseEnd_3153641 : Nat := 1619333644725801098784175

theorem tailTrace_3153641 : CollatzResearch.WordTrace tailWord_3153641 prefixEnd_3153641 1619333644725801098784175 := by
  unfold tailWord_3153641
  simp only [CollatzResearch.WordTrace]
  refine ⟨115022736767904730847852777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76681824511936487231901851 115022736767904730847852777)
  ·
    refine ⟨86267052575928548135889583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115022736767904730847852777 86267052575928548135889583)
    ·
      refine ⟨129400578863892822203834375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86267052575928548135889583 129400578863892822203834375)
      ·
        refine ⟨194100868295839233305751563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129400578863892822203834375 194100868295839233305751563)
        ·
          refine ⟨291151302443758849958627345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194100868295839233305751563 291151302443758849958627345)
          ·
            refine ⟨218363476832819137468970509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291151302443758849958627345 218363476832819137468970509)
            ·
              refine ⟨81886303812307176550863941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218363476832819137468970509 81886303812307176550863941)
              ·
                refine ⟨15353681964807595603286989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81886303812307176550863941 15353681964807595603286989)
                ·
                  refine ⟨5757630736802848351232621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15353681964807595603286989 5757630736802848351232621)
                  ·
                    refine ⟨2159111526301068131712233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5757630736802848351232621 2159111526301068131712233)
                    ·
                      refine ⟨1619333644725801098784175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2159111526301068131712233 1619333644725801098784175)
                      ·
                        rfl

theorem cell23_3153641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 3, 2].length) (baseStart_3153641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153641 prefixEnd_3153641 := by exact prefixLift 3153641
  have htrace : WordTrace (prefixWord ++ tailWord_3153641) baseStart_3153641 baseEnd_3153641 := by
    simpa [prefixWord, tailWord_3153641, baseEnd_3153641] using wordTrace_append hprefix tailTrace_3153641
  have hstable : (prefixWord ++ tailWord_3153641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153641).length < 2 ^ (prefixWord ++ tailWord_3153641).sum := by decide
  have hdescent : baseEnd_3153641 < baseStart_3153641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153652 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3153652 : Nat := 118140960795 + 3153652 * 2 ^ 59
def prefixEnd_3153652 : Nat := 4983230072969 + 3 ^ 40 * 3153652 * 2
def baseEnd_3153652 : Nat := 1619339293013000555746625

theorem tailTrace_3153652 : CollatzResearch.WordTrace tailWord_3153652 prefixEnd_3153652 1619339293013000555746625 := by
  unfold tailWord_3153652
  simp only [CollatzResearch.WordTrace]
  refine ⟨57511568985432439863251605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76682091980576586484335473 57511568985432439863251605)
  ·
    refine ⟨2695854796192145618589919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57511568985432439863251605 2695854796192145618589919)
    ·
      refine ⟨4043782194288218427884879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2695854796192145618589919 4043782194288218427884879)
      ·
        refine ⟨6065673291432327641827319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043782194288218427884879 6065673291432327641827319)
        ·
          refine ⟨9098509937148491462740979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6065673291432327641827319 9098509937148491462740979)
          ·
            refine ⟨13647764905722737194111469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9098509937148491462740979 13647764905722737194111469)
            ·
              refine ⟨5117911839646026447791801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13647764905722737194111469 5117911839646026447791801)
              ·
                refine ⟨3838433879734519835843851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5117911839646026447791801 3838433879734519835843851)
                ·
                  refine ⟨5757650819601779753765777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838433879734519835843851 5757650819601779753765777)
                  ·
                    refine ⟨4318238114701334815324333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5757650819601779753765777 4318238114701334815324333)
                    ·
                      refine ⟨1619339293013000555746625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4318238114701334815324333 1619339293013000555746625)
                      ·
                        rfl

theorem cell23_3153652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3153652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153652 prefixEnd_3153652 := by exact prefixLift 3153652
  have htrace : WordTrace (prefixWord ++ tailWord_3153652) baseStart_3153652 baseEnd_3153652 := by
    simpa [prefixWord, tailWord_3153652, baseEnd_3153652] using wordTrace_append hprefix tailTrace_3153652
  have hstable : (prefixWord ++ tailWord_3153652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153652).length < 2 ^ (prefixWord ++ tailWord_3153652).sum := by decide
  have hdescent : baseEnd_3153652 < baseStart_3153652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153682 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3153682 : Nat := 118140960795 + 3153682 * 2 ^ 59
def prefixEnd_3153682 : Nat := 4983230072969 + 3 ^ 40 * 3153682 * 2
def baseEnd_3153682 : Nat := 1619354697432635438371487

theorem tailTrace_3153682 : CollatzResearch.WordTrace tailWord_3153682 prefixEnd_3153682 1619354697432635438371487 := by
  unfold tailWord_3153682
  simp only [CollatzResearch.WordTrace]
  refine ⟨28756058040189048712523825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76682821440504129900063533 28756058040189048712523825)
  ·
    refine ⟨21567043530141786534392869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28756058040189048712523825 21567043530141786534392869)
    ·
      refine ⟨4043820661901584975198663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21567043530141786534392869 4043820661901584975198663)
      ·
        refine ⟨6065730992852377462797995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043820661901584975198663 6065730992852377462797995)
        ·
          refine ⟨9098596489278566194196993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6065730992852377462797995 9098596489278566194196993)
          ·
            refine ⟨6823947366958924645647745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9098596489278566194196993 6823947366958924645647745)
            ·
              refine ⟨5117960525219193484235809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6823947366958924645647745 5117960525219193484235809)
              ·
                refine ⟨3838470393914395113176857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5117960525219193484235809 3838470393914395113176857)
                ·
                  refine ⟨2878852795435796334882643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3838470393914395113176857 2878852795435796334882643)
                  ·
                    refine ⟨4318279193153694502323965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2878852795435796334882643 4318279193153694502323965)
                    ·
                      refine ⟨1619354697432635438371487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4318279193153694502323965 1619354697432635438371487)
                      ·
                        rfl

theorem cell23_3153682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3153682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153682 prefixEnd_3153682 := by exact prefixLift 3153682
  have htrace : WordTrace (prefixWord ++ tailWord_3153682) baseStart_3153682 baseEnd_3153682 := by
    simpa [prefixWord, tailWord_3153682, baseEnd_3153682] using wordTrace_append hprefix tailTrace_3153682
  have hstable : (prefixWord ++ tailWord_3153682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153682).length < 2 ^ (prefixWord ++ tailWord_3153682).sum := by decide
  have hdescent : baseEnd_3153682 < baseStart_3153682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153688 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 4, 2, 2]
def baseStart_3153688 : Nat := 118140960795 + 3153688 * 2 ^ 59
def prefixEnd_3153688 : Nat := 4983230072969 + 3 ^ 40 * 3153688 * 2
def baseEnd_3153688 : Nat := 1619357778316562414896459

theorem tailTrace_3153688 : CollatzResearch.WordTrace tailWord_3153688 prefixEnd_3153688 1619357778316562414896459 := by
  unfold tailWord_3153688
  simp only [CollatzResearch.WordTrace]
  refine ⟨57512225499367228937406859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76682967332489638583209145 57512225499367228937406859)
  ·
    refine ⟨86268338249050843406110289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57512225499367228937406859 86268338249050843406110289)
    ·
      refine ⟨64701253686788132554582717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86268338249050843406110289 64701253686788132554582717)
      ·
        refine ⟨24262970132545549707968519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64701253686788132554582717 24262970132545549707968519)
        ·
          refine ⟨36394455198818324561952779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24262970132545549707968519 36394455198818324561952779)
          ·
            refine ⟨54591682798227486842929169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36394455198818324561952779 54591682798227486842929169)
            ·
              refine ⟨40943762098670615132196877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54591682798227486842929169 40943762098670615132196877)
              ·
                refine ⟨15353910787001480674573829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40943762098670615132196877 15353910787001480674573829)
                ·
                  refine ⟨2878858272562777626482593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15353910787001480674573829 2878858272562777626482593)
                  ·
                    refine ⟨2159143704422083219861945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2878858272562777626482593 2159143704422083219861945)
                    ·
                      refine ⟨1619357778316562414896459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2159143704422083219861945 1619357778316562414896459)
                      ·
                        rfl

theorem cell23_3153688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_3153688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153688 prefixEnd_3153688 := by exact prefixLift 3153688
  have htrace : WordTrace (prefixWord ++ tailWord_3153688) baseStart_3153688 baseEnd_3153688 := by
    simpa [prefixWord, tailWord_3153688, baseEnd_3153688] using wordTrace_append hprefix tailTrace_3153688
  have hstable : (prefixWord ++ tailWord_3153688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153688).length < 2 ^ (prefixWord ++ tailWord_3153688).sum := by decide
  have hdescent : baseEnd_3153688 < baseStart_3153688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153701 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_3153701 : Nat := 118140960795 + 3153701 * 2 ^ 59
def prefixEnd_3153701 : Nat := 4983230072969 + 3 ^ 40 * 3153701 * 2
def baseEnd_3153701 : Nat := 1619364453565070864033899

theorem tailTrace_3153701 : CollatzResearch.WordTrace tailWord_3153701 prefixEnd_3153701 1619364453565070864033899 := by
  unfold tailWord_3153701
  simp only [CollatzResearch.WordTrace]
  refine ⟨115024925147687361095036957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76683283431791574063357971 115024925147687361095036957)
  ·
    refine ⟨43134346930382760410638859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115024925147687361095036957 43134346930382760410638859)
    ·
      refine ⟨64701520395574140615958289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43134346930382760410638859 64701520395574140615958289)
      ·
        refine ⟨48526140296680605461968717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64701520395574140615958289 48526140296680605461968717)
        ·
          refine ⟨18197302611255227048238269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48526140296680605461968717 18197302611255227048238269)
          ·
            refine ⟨6823988479220710143089351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18197302611255227048238269 6823988479220710143089351)
            ·
              refine ⟨10235982718831065214634027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6823988479220710143089351 10235982718831065214634027)
              ·
                refine ⟨15353974078246597821951041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10235982718831065214634027 15353974078246597821951041)
                ·
                  refine ⟨11515480558684948366463281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15353974078246597821951041 11515480558684948366463281)
                  ·
                    refine ⟨8636610419013711274847461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11515480558684948366463281 8636610419013711274847461)
                    ·
                      refine ⟨1619364453565070864033899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8636610419013711274847461 1619364453565070864033899)
                      ·
                        rfl

theorem cell23_3153701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_3153701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153701 prefixEnd_3153701 := by exact prefixLift 3153701
  have htrace : WordTrace (prefixWord ++ tailWord_3153701) baseStart_3153701 baseEnd_3153701 := by
    simpa [prefixWord, tailWord_3153701, baseEnd_3153701] using wordTrace_append hprefix tailTrace_3153701
  have hstable : (prefixWord ++ tailWord_3153701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153701).length < 2 ^ (prefixWord ++ tailWord_3153701).sum := by decide
  have hdescent : baseEnd_3153701 < baseStart_3153701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153801 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 6]
def baseStart_3153801 : Nat := 118140960795 + 3153801 * 2 ^ 59
def prefixEnd_3153801 : Nat := 4983230072969 + 3 ^ 40 * 3153801 * 2
def baseEnd_3153801 : Nat := 179935089070057830309271

theorem tailTrace_3153801 : CollatzResearch.WordTrace tailWord_3153801 prefixEnd_3153801 179935089070057830309271 := by
  unfold tailWord_3153801
  simp only [CollatzResearch.WordTrace]
  refine ⟨115028572447325078173677257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76685714964883385449118171 115028572447325078173677257)
  ·
    refine ⟨86271429335493808630257943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115028572447325078173677257 86271429335493808630257943)
    ·
      refine ⟨129407144003240712945386915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86271429335493808630257943 129407144003240712945386915)
      ·
        refine ⟨194110716004861069418080373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129407144003240712945386915 194110716004861069418080373)
        ·
          refine ⟨18197879625455725257945035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194110716004861069418080373 18197879625455725257945035)
          ·
            refine ⟨27296819438183587886917553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18197879625455725257945035 27296819438183587886917553)
            ·
              refine ⟨20472614578637690915188165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27296819438183587886917553 20472614578637690915188165)
              ·
                refine ⟨3838615233494567046597781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20472614578637690915188165 3838615233494567046597781)
                ·
                  refine ⟨179935089070057830309271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3838615233494567046597781 179935089070057830309271)
                  ·
                    rfl

theorem cell23_3153801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 6].length) (baseStart_3153801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153801 prefixEnd_3153801 := by exact prefixLift 3153801
  have htrace : WordTrace (prefixWord ++ tailWord_3153801) baseStart_3153801 baseEnd_3153801 := by
    simpa [prefixWord, tailWord_3153801, baseEnd_3153801] using wordTrace_append hprefix tailTrace_3153801
  have hstable : (prefixWord ++ tailWord_3153801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153801).length < 2 ^ (prefixWord ++ tailWord_3153801).sum := by decide
  have hdescent : baseEnd_3153801 < baseStart_3153801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153818 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 6]
def baseStart_3153818 : Nat := 118140960795 + 3153818 * 2 ^ 59
def prefixEnd_3153818 : Nat := 4983230072969 + 3 ^ 40 * 3153818 * 2
def baseEnd_3153818 : Nat := 179936058977960767363429

theorem tailTrace_3153818 : CollatzResearch.WordTrace tailWord_3153818 prefixEnd_3153818 179936058977960767363429 := by
  unfold tailWord_3153818
  simp only [CollatzResearch.WordTrace]
  refine ⟨28757298122065872519261527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76686128325508993384697405 28757298122065872519261527)
  ·
    refine ⟨43135947183098808778892291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28757298122065872519261527 43135947183098808778892291)
    ·
      refine ⟨64703920774648213168338437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43135947183098808778892291 64703920774648213168338437)
      ·
        refine ⟨12131985145246539969063457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64703920774648213168338437 12131985145246539969063457)
        ·
          refine ⟨9098988858934904976797593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12131985145246539969063457 9098988858934904976797593)
          ·
            refine ⟨6824241644201178732598195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9098988858934904976797593 6824241644201178732598195)
            ·
              refine ⟨10236362466301768098897293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6824241644201178732598195 10236362466301768098897293)
              ·
                refine ⟨3838635924863163037086485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10236362466301768098897293 3838635924863163037086485)
                ·
                  refine ⟨179936058977960767363429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3838635924863163037086485 179936058977960767363429)
                  ·
                    rfl

theorem cell23_3153818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_3153818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153818 prefixEnd_3153818 := by exact prefixLift 3153818
  have htrace : WordTrace (prefixWord ++ tailWord_3153818) baseStart_3153818 baseEnd_3153818 := by
    simpa [prefixWord, tailWord_3153818, baseEnd_3153818] using wordTrace_append hprefix tailTrace_3153818
  have hstable : (prefixWord ++ tailWord_3153818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153818).length < 2 ^ (prefixWord ++ tailWord_3153818).sum := by decide
  have hdescent : baseEnd_3153818 < baseStart_3153818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153851 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 4]
def baseStart_3153851 : Nat := 118140960795 + 3153851 * 2 ^ 59
def prefixEnd_3153851 : Nat := 4983230072969 + 3 ^ 40 * 3153851 * 2
def baseEnd_3153851 : Nat := 1619441475663245277158209

theorem tailTrace_3153851 : CollatzResearch.WordTrace tailWord_3153851 prefixEnd_3153851 1619441475663245277158209 := by
  unfold tailWord_3153851
  simp only [CollatzResearch.WordTrace]
  refine ⟨115030396097143936712997407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76686930731429291141998271 115030396097143936712997407)
  ·
    refine ⟨172545594145715905069496111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115030396097143936712997407 172545594145715905069496111)
    ·
      refine ⟨258818391218573857604244167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172545594145715905069496111 258818391218573857604244167)
      ·
        refine ⟨388227586827860786406366251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258818391218573857604244167 388227586827860786406366251)
        ·
          refine ⟨582341380241791179609549377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388227586827860786406366251 582341380241791179609549377)
          ·
            refine ⟨436756035181343384707162033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582341380241791179609549377 436756035181343384707162033)
            ·
              refine ⟨327567026386007538530371525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436756035181343384707162033 327567026386007538530371525)
              ·
                refine ⟨61418817447376413474444661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327567026386007538530371525 61418817447376413474444661)
                ·
                  refine ⟨5758014135691538763229187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61418817447376413474444661 5758014135691538763229187)
                  ·
                    refine ⟨8637021203537308144843781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5758014135691538763229187 8637021203537308144843781)
                    ·
                      refine ⟨1619441475663245277158209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8637021203537308144843781 1619441475663245277158209)
                      ·
                        rfl

theorem cell23_3153851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 4].length) (baseStart_3153851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153851 prefixEnd_3153851 := by exact prefixLift 3153851
  have htrace : WordTrace (prefixWord ++ tailWord_3153851) baseStart_3153851 baseEnd_3153851 := by
    simpa [prefixWord, tailWord_3153851, baseEnd_3153851] using wordTrace_append hprefix tailTrace_3153851
  have hstable : (prefixWord ++ tailWord_3153851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153851).length < 2 ^ (prefixWord ++ tailWord_3153851).sum := by decide
  have hdescent : baseEnd_3153851 < baseStart_3153851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153868 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3153868 : Nat := 118140960795 + 3153868 * 2 ^ 59
def prefixEnd_3153868 : Nat := 4983230072969 + 3 ^ 40 * 3153868 * 2
def baseEnd_3153868 : Nat := 1619450204834371710645631

theorem tailTrace_3153868 : CollatzResearch.WordTrace tailWord_3153868 prefixEnd_3153868 1619450204834371710645631 := by
  unfold tailWord_3153868
  simp only [CollatzResearch.WordTrace]
  refine ⟨57515508069041174308183129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76687344092054899077577505 57515508069041174308183129)
  ·
    refine ⟨43136631051780880731137347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57515508069041174308183129 43136631051780880731137347)
    ·
      refine ⟨64704946577671321096706021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43136631051780880731137347 64704946577671321096706021)
      ·
        refine ⟨12132177483313372705632379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64704946577671321096706021 12132177483313372705632379)
        ·
          refine ⟨18198266224970059058448569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12132177483313372705632379 18198266224970059058448569)
          ·
            refine ⟨13648699668727544293836427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18198266224970059058448569 13648699668727544293836427)
            ·
              refine ⟨20473049503091316440754641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13648699668727544293836427 20473049503091316440754641)
              ·
                refine ⟨15354787127318487330565981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20473049503091316440754641 15354787127318487330565981)
                ·
                  refine ⟨5758045172744432748962243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15354787127318487330565981 5758045172744432748962243)
                  ·
                    refine ⟨8637067759116649123443365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5758045172744432748962243 8637067759116649123443365)
                    ·
                      refine ⟨1619450204834371710645631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8637067759116649123443365 1619450204834371710645631)
                      ·
                        rfl

theorem cell23_3153868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3153868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153868 prefixEnd_3153868 := by exact prefixLift 3153868
  have htrace : WordTrace (prefixWord ++ tailWord_3153868) baseStart_3153868 baseEnd_3153868 := by
    simpa [prefixWord, tailWord_3153868, baseEnd_3153868] using wordTrace_append hprefix tailTrace_3153868
  have hstable : (prefixWord ++ tailWord_3153868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153868).length < 2 ^ (prefixWord ++ tailWord_3153868).sum := by decide
  have hdescent : baseEnd_3153868 < baseStart_3153868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153871 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 5]
def baseStart_3153871 : Nat := 118140960795 + 3153871 * 2 ^ 59
def prefixEnd_3153871 : Nat := 4983230072969 + 3 ^ 40 * 3153871 * 2
def baseEnd_3153871 : Nat := 1619451745276335198908117

theorem tailTrace_3153871 : CollatzResearch.WordTrace tailWord_3153871 prefixEnd_3153871 1619451745276335198908117 := by
  unfold tailWord_3153871
  simp only [CollatzResearch.WordTrace]
  refine ⟨115031125557071480128725467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76687417038047653419150311 115031125557071480128725467)
  ·
    refine ⟨172546688335607220193088201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115031125557071480128725467 172546688335607220193088201)
    ·
      refine ⟨129410016251705415144816151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172546688335607220193088201 129410016251705415144816151)
      ·
        refine ⟨194115024377558122717224227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129410016251705415144816151 194115024377558122717224227)
        ·
          refine ⟨291172536566337184075836341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194115024377558122717224227 291172536566337184075836341)
          ·
            refine ⟨27297425303094111007109657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291172536566337184075836341 27297425303094111007109657)
            ·
              refine ⟨20473068977320583255332243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27297425303094111007109657 20473068977320583255332243)
              ·
                refine ⟨30709603465980874882998365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20473068977320583255332243 30709603465980874882998365)
                ·
                  refine ⟨11516101299742828081124387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30709603465980874882998365 11516101299742828081124387)
                  ·
                    refine ⟨17274151949614242121686581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11516101299742828081124387 17274151949614242121686581)
                    ·
                      refine ⟨1619451745276335198908117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17274151949614242121686581 1619451745276335198908117)
                      ·
                        rfl

theorem cell23_3153871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_3153871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153871 prefixEnd_3153871 := by exact prefixLift 3153871
  have htrace : WordTrace (prefixWord ++ tailWord_3153871) baseStart_3153871 baseEnd_3153871 := by
    simpa [prefixWord, tailWord_3153871, baseEnd_3153871] using wordTrace_append hprefix tailTrace_3153871
  have hstable : (prefixWord ++ tailWord_3153871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153871).length < 2 ^ (prefixWord ++ tailWord_3153871).sum := by decide
  have hdescent : baseEnd_3153871 < baseStart_3153871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153898 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_3153898 : Nat := 118140960795 + 3153898 * 2 ^ 59
def prefixEnd_3153898 : Nat := 4983230072969 + 3 ^ 40 * 3153898 * 2
def baseEnd_3153898 : Nat := 1619465609254006593270493

theorem tailTrace_3153898 : CollatzResearch.WordTrace tailWord_3153898 prefixEnd_3153898 1619465609254006593270493 := by
  unfold tailWord_3153898
  simp only [CollatzResearch.WordTrace]
  refine ⟨28758027581993415934989587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76688073551982442493305565 28758027581993415934989587)
  ·
    refine ⟨43137041372990123902484381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28758027581993415934989587 43137041372990123902484381)
    ·
      refine ⟨16176390514871296463431643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43137041372990123902484381 16176390514871296463431643)
      ·
        refine ⟨24264585772306944695147465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16176390514871296463431643 24264585772306944695147465)
        ·
          refine ⟨18198439329230208521360599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24264585772306944695147465 18198439329230208521360599)
          ·
            refine ⟨27297658993845312782040899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18198439329230208521360599 27297658993845312782040899)
            ·
              refine ⟨40946488490767969173061349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27297658993845312782040899 40946488490767969173061349)
              ·
                refine ⟨7677466592018994219949003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40946488490767969173061349 7677466592018994219949003)
                ·
                  refine ⟨11516199888028491329923505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7677466592018994219949003 11516199888028491329923505)
                  ·
                    refine ⟨8637149916021368497442629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11516199888028491329923505 8637149916021368497442629)
                    ·
                      refine ⟨1619465609254006593270493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8637149916021368497442629 1619465609254006593270493)
                      ·
                        rfl

theorem cell23_3153898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_3153898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153898 prefixEnd_3153898 := by exact prefixLift 3153898
  have htrace : WordTrace (prefixWord ++ tailWord_3153898) baseStart_3153898 baseEnd_3153898 := by
    simpa [prefixWord, tailWord_3153898, baseEnd_3153898] using wordTrace_append hprefix tailTrace_3153898
  have hstable : (prefixWord ++ tailWord_3153898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153898).length < 2 ^ (prefixWord ++ tailWord_3153898).sum := by decide
  have hdescent : baseEnd_3153898 < baseStart_3153898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153902 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_3153902 : Nat := 118140960795 + 3153902 * 2 ^ 59
def prefixEnd_3153902 : Nat := 4983230072969 + 3 ^ 40 * 3153902 * 2
def baseEnd_3153902 : Nat := 1619467663176624577620475

theorem tailTrace_3153902 : CollatzResearch.WordTrace tailWord_3153902 prefixEnd_3153902 1619467663176624577620475 := by
  unfold tailWord_3153902
  simp only [CollatzResearch.WordTrace]
  refine ⟨14379032027494896552887995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76688170813306114948735973 14379032027494896552887995)
  ·
    refine ⟨21568548041242344829331993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14379032027494896552887995 21568548041242344829331993)
    ·
      refine ⟨16176411030931758621998995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21568548041242344829331993 16176411030931758621998995)
      ·
        refine ⟨24264616546397637932998493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16176411030931758621998995 24264616546397637932998493)
        ·
          refine ⟨9099231204899114224874435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24264616546397637932998493 9099231204899114224874435)
          ·
            refine ⟨13648846807348671337311653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9099231204899114224874435 13648846807348671337311653)
            ·
              refine ⟨2559158776377875875745935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13648846807348671337311653 2559158776377875875745935)
              ·
                refine ⟨3838738164566813813618903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2559158776377875875745935 3838738164566813813618903)
                ·
                  refine ⟨5758107246850220720428355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838738164566813813618903 5758107246850220720428355)
                  ·
                    refine ⟨8637160870275331080642533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5758107246850220720428355 8637160870275331080642533)
                    ·
                      refine ⟨1619467663176624577620475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8637160870275331080642533 1619467663176624577620475)
                      ·
                        rfl

theorem cell23_3153902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_3153902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153902 prefixEnd_3153902 := by exact prefixLift 3153902
  have htrace : WordTrace (prefixWord ++ tailWord_3153902) baseStart_3153902 baseEnd_3153902 := by
    simpa [prefixWord, tailWord_3153902, baseEnd_3153902] using wordTrace_append hprefix tailTrace_3153902
  have hstable : (prefixWord ++ tailWord_3153902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153902).length < 2 ^ (prefixWord ++ tailWord_3153902).sum := by decide
  have hdescent : baseEnd_3153902 < baseStart_3153902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153948 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3153948 : Nat := 118140960795 + 3153948 * 2 ^ 59
def prefixEnd_3153948 : Nat := 4983230072969 + 3 ^ 40 * 3153948 * 2
def baseEnd_3153948 : Nat := 1619491283286731397645263

theorem tailTrace_3153948 : CollatzResearch.WordTrace tailWord_3153948 prefixEnd_3153948 1619491283286731397645263 := by
  unfold tailWord_3153948
  simp only [CollatzResearch.WordTrace]
  refine ⟨57516966988896261139639249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76689289318528348186185665 57516966988896261139639249)
  ·
    refine ⟨43137725241672195854729437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57516966988896261139639249 43137725241672195854729437)
    ·
      refine ⟨16176646965627073445523539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43137725241672195854729437 16176646965627073445523539)
      ·
        refine ⟨24264970448440610168285309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16176646965627073445523539 24264970448440610168285309)
        ·
          refine ⟨9099363918165228813106991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24264970448440610168285309 9099363918165228813106991)
          ·
            refine ⟨13649045877247843219660487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9099363918165228813106991 13649045877247843219660487)
            ·
              refine ⟨20473568815871764829490731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13649045877247843219660487 20473568815871764829490731)
              ·
                refine ⟨30710353223807647244236097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20473568815871764829490731 30710353223807647244236097)
                ·
                  refine ⟨23032764917855735433177073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30710353223807647244236097 23032764917855735433177073)
                  ·
                    refine ⟨17274573688391801574882805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23032764917855735433177073 17274573688391801574882805)
                    ·
                      refine ⟨1619491283286731397645263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17274573688391801574882805 1619491283286731397645263)
                      ·
                        rfl

theorem cell23_3153948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3153948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153948 prefixEnd_3153948 := by exact prefixLift 3153948
  have htrace : WordTrace (prefixWord ++ tailWord_3153948) baseStart_3153948 baseEnd_3153948 := by
    simpa [prefixWord, tailWord_3153948, baseEnd_3153948] using wordTrace_append hprefix tailTrace_3153948
  have hstable : (prefixWord ++ tailWord_3153948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153948).length < 2 ^ (prefixWord ++ tailWord_3153948).sum := by decide
  have hdescent : baseEnd_3153948 < baseStart_3153948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153953 : List Nat := [1, 2, 3, 2, 5, 1, 1, 3, 1, 2, 2]
def baseStart_3153953 : Nat := 118140960795 + 3153953 * 2 ^ 59
def prefixEnd_3153953 : Nat := 4983230072969 + 3 ^ 40 * 3153953 * 2
def baseEnd_3153953 : Nat := 1619493850690003878082741

theorem tailTrace_3153953 : CollatzResearch.WordTrace tailWord_3153953 prefixEnd_3153953 1619493850690003878082741 := by
  unfold tailWord_3153953
  simp only [CollatzResearch.WordTrace]
  refine ⟨115034116342774408133210513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76689410895182938755473675 115034116342774408133210513)
  ·
    refine ⟨86275587257080806099907885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115034116342774408133210513 86275587257080806099907885)
    ·
      refine ⟨32353345221405302287465457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86275587257080806099907885 32353345221405302287465457)
      ·
        refine ⟨24265008916053976715599093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32353345221405302287465457 24265008916053976715599093)
        ·
          refine ⟨2274844585880060317087415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24265008916053976715599093 2274844585880060317087415)
          ·
            refine ⟨3412266878820090475631123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274844585880060317087415 3412266878820090475631123)
            ·
              refine ⟨5118400318230135713446685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412266878820090475631123 5118400318230135713446685)
              ·
                refine ⟨1919400119336300892542507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5118400318230135713446685 1919400119336300892542507)
                ·
                  refine ⟨2879100179004451338813761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919400119336300892542507 2879100179004451338813761)
                  ·
                    refine ⟨2159325134253338504110321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2879100179004451338813761 2159325134253338504110321)
                    ·
                      refine ⟨1619493850690003878082741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2159325134253338504110321 1619493850690003878082741)
                      ·
                        rfl

theorem cell23_3153953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_3153953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153953 prefixEnd_3153953 := by exact prefixLift 3153953
  have htrace : WordTrace (prefixWord ++ tailWord_3153953) baseStart_3153953 baseEnd_3153953 := by
    simpa [prefixWord, tailWord_3153953, baseEnd_3153953] using wordTrace_append hprefix tailTrace_3153953
  have hstable : (prefixWord ++ tailWord_3153953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153953).length < 2 ^ (prefixWord ++ tailWord_3153953).sum := by decide
  have hdescent : baseEnd_3153953 < baseStart_3153953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153978 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3]
def baseStart_3153978 : Nat := 118140960795 + 3153978 * 2 ^ 59
def prefixEnd_3153978 : Nat := 4983230072969 + 3 ^ 40 * 3153978 * 2
def baseEnd_3153978 : Nat := 1619506687706366280270125

theorem tailTrace_3153978 : CollatzResearch.WordTrace tailWord_3153978 prefixEnd_3153978 1619506687706366280270125 := by
  unfold tailWord_3153978
  simp only [CollatzResearch.WordTrace]
  refine ⟨28758757041920959350717647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76690018778455891601913725 28758757041920959350717647)
  ·
    refine ⟨43138135562881439026076471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28758757041920959350717647 43138135562881439026076471)
    ·
      refine ⟨64707203344322158539114707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43138135562881439026076471 64707203344322158539114707)
      ·
        refine ⟨97060805016483237808672061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64707203344322158539114707 97060805016483237808672061)
        ·
          refine ⟨36397801881181214178252023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97060805016483237808672061 36397801881181214178252023)
          ·
            refine ⟨54596702821771821267378035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36397801881181214178252023 54596702821771821267378035)
            ·
              refine ⟨81895054232657731901067053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54596702821771821267378035 81895054232657731901067053)
              ·
                refine ⟨30710645337246649462900145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81895054232657731901067053 30710645337246649462900145)
                ·
                  refine ⟨23032984002934987097175109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30710645337246649462900145 23032984002934987097175109)
                  ·
                    refine ⟨4318684500550310080720333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23032984002934987097175109 4318684500550310080720333)
                    ·
                      refine ⟨1619506687706366280270125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4318684500550310080720333 1619506687706366280270125)
                      ·
                        rfl

theorem cell23_3153978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_3153978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3153978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3153978 prefixEnd_3153978 := by exact prefixLift 3153978
  have htrace : WordTrace (prefixWord ++ tailWord_3153978) baseStart_3153978 baseEnd_3153978 := by
    simpa [prefixWord, tailWord_3153978, baseEnd_3153978] using wordTrace_append hprefix tailTrace_3153978
  have hstable : (prefixWord ++ tailWord_3153978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153978).length < 2 ^ (prefixWord ++ tailWord_3153978).sum := by decide
  have hdescent : baseEnd_3153978 < baseStart_3153978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154026 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_3154026 : Nat := 118140960795 + 3154026 * 2 ^ 59
def prefixEnd_3154026 : Nat := 4983230072969 + 3 ^ 40 * 3154026 * 2
def baseEnd_3154026 : Nat := 1619531334777782092469905

theorem tailTrace_3154026 : CollatzResearch.WordTrace tailWord_3154026 prefixEnd_3154026 1619531334777782092469905 := by
  unfold tailWord_3154026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28759194717877485400154483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76691185914339961067078621 28759194717877485400154483)
  ·
    refine ⟨43138792076816228100231725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28759194717877485400154483 43138792076816228100231725)
    ·
      refine ⟨16177047028806085537586897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43138792076816228100231725 16177047028806085537586897)
      ·
        refine ⟨12132785271604564153190173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16177047028806085537586897 12132785271604564153190173)
        ·
          refine ⟨4549794476851711557446315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12132785271604564153190173 4549794476851711557446315)
          ·
            refine ⟨6824691715277567336169473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4549794476851711557446315 6824691715277567336169473)
            ·
              refine ⟨5118518786458175502127105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6824691715277567336169473 5118518786458175502127105)
              ·
                refine ⟨3838889089843631626595329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5118518786458175502127105 3838889089843631626595329)
                ·
                  refine ⟨2879166817382723719946497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3838889089843631626595329 2879166817382723719946497)
                  ·
                    refine ⟨2159375113037042789959873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2879166817382723719946497 2159375113037042789959873)
                    ·
                      refine ⟨1619531334777782092469905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2159375113037042789959873 1619531334777782092469905)
                      ·
                        rfl

theorem cell23_3154026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_3154026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154026 prefixEnd_3154026 := by exact prefixLift 3154026
  have htrace : WordTrace (prefixWord ++ tailWord_3154026) baseStart_3154026 baseEnd_3154026 := by
    simpa [prefixWord, tailWord_3154026, baseEnd_3154026] using wordTrace_append hprefix tailTrace_3154026
  have hstable : (prefixWord ++ tailWord_3154026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154026).length < 2 ^ (prefixWord ++ tailWord_3154026).sum := by decide
  have hdescent : baseEnd_3154026 < baseStart_3154026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154032 : List Nat := [2, 1, 1, 1, 5, 2, 4, 2, 5]
def baseStart_3154032 : Nat := 118140960795 + 3154032 * 2 ^ 59
def prefixEnd_3154032 : Nat := 4983230072969 + 3 ^ 40 * 3154032 * 2
def baseEnd_3154032 : Nat := 179948268406856563221653

theorem tailTrace_3154032 : CollatzResearch.WordTrace tailWord_3154032 prefixEnd_3154032 179948268406856563221653 := by
  unfold tailWord_3154032
  simp only [CollatzResearch.WordTrace]
  refine ⟨57518498854744102312668175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76691331806325469750224233 57518498854744102312668175)
  ·
    refine ⟨86277748282116153469002263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57518498854744102312668175 86277748282116153469002263)
    ·
      refine ⟨129416622423174230203503395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86277748282116153469002263 129416622423174230203503395)
      ·
        refine ⟨194124933634761345305255093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129416622423174230203503395 194124933634761345305255093)
        ·
          refine ⟨18199212528258876122367665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194124933634761345305255093 18199212528258876122367665)
          ·
            refine ⟨13649409396194157091775749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18199212528258876122367665 13649409396194157091775749)
            ·
              refine ⟨2559264261786404454707953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13649409396194157091775749 2559264261786404454707953)
              ·
                refine ⟨1919448196339803341030965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559264261786404454707953 1919448196339803341030965)
                ·
                  refine ⟨179948268406856563221653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1919448196339803341030965 179948268406856563221653)
                  ·
                    rfl

theorem cell23_3154032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 5].length) (baseStart_3154032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154032 prefixEnd_3154032 := by exact prefixLift 3154032
  have htrace : WordTrace (prefixWord ++ tailWord_3154032) baseStart_3154032 baseEnd_3154032 := by
    simpa [prefixWord, tailWord_3154032, baseEnd_3154032] using wordTrace_append hprefix tailTrace_3154032
  have hstable : (prefixWord ++ tailWord_3154032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154032).length < 2 ^ (prefixWord ++ tailWord_3154032).sum := by decide
  have hdescent : baseEnd_3154032 < baseStart_3154032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154048 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 4]
def baseStart_3154048 : Nat := 118140960795 + 3154048 * 2 ^ 59
def prefixEnd_3154048 : Nat := 4983230072969 + 3 ^ 40 * 3154048 * 2
def baseEnd_3154048 : Nat := 1619542631352181006394803

theorem tailTrace_3154048 : CollatzResearch.WordTrace tailWord_3154048 prefixEnd_3154048 1619542631352181006394803 := by
  unfold tailWord_3154048
  simp only [CollatzResearch.WordTrace]
  refine ⟨57518790638715119678959399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76691720851620159571945865 57518790638715119678959399)
  ·
    refine ⟨86278185958072679518439099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57518790638715119678959399 86278185958072679518439099)
    ·
      refine ⟨129417278937109019277658649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86278185958072679518439099 129417278937109019277658649)
      ·
        refine ⟨97062959202831764458243987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129417278937109019277658649 97062959202831764458243987)
        ·
          refine ⟨145594438804247646687365981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97062959202831764458243987 145594438804247646687365981)
          ·
            refine ⟨54597914551592867507762243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145594438804247646687365981 54597914551592867507762243)
            ·
              refine ⟨81896871827389301261643365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54597914551592867507762243 81896871827389301261643365)
              ·
                refine ⟨15355663467635493986558131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81896871827389301261643365 15355663467635493986558131)
                ·
                  refine ⟨23033495201453240979837197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15355663467635493986558131 23033495201453240979837197)
                  ·
                    refine ⟨8637560700544965367438949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23033495201453240979837197 8637560700544965367438949)
                    ·
                      refine ⟨1619542631352181006394803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8637560700544965367438949 1619542631352181006394803)
                      ·
                        rfl

theorem cell23_3154048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_3154048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154048 prefixEnd_3154048 := by exact prefixLift 3154048
  have htrace : WordTrace (prefixWord ++ tailWord_3154048) baseStart_3154048 baseEnd_3154048 := by
    simpa [prefixWord, tailWord_3154048, baseEnd_3154048] using wordTrace_append hprefix tailTrace_3154048
  have hstable : (prefixWord ++ tailWord_3154048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154048).length < 2 ^ (prefixWord ++ tailWord_3154048).sum := by decide
  have hdescent : baseEnd_3154048 < baseStart_3154048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154085 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 4, 2, 3]
def baseStart_3154085 : Nat := 118140960795 + 3154085 * 2 ^ 59
def prefixEnd_3154085 : Nat := 4983230072969 + 3 ^ 40 * 3154085 * 2
def baseEnd_3154085 : Nat := 1619561630136397361632133

theorem tailTrace_3154085 : CollatzResearch.WordTrace tailWord_3154085 prefixEnd_3154085 1619561630136397361632133 := by
  unfold tailWord_3154085
  simp only [CollatzResearch.WordTrace]
  refine ⟨115038930778296194677015709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76692620518864129784677139 115038930778296194677015709)
  ·
    refine ⟨43139599041861073003880891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115038930778296194677015709 43139599041861073003880891)
    ·
      refine ⟨64709398562791609505821337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43139599041861073003880891 64709398562791609505821337)
      ·
        refine ⟨48532048922093707129366003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64709398562791609505821337 48532048922093707129366003)
        ·
          refine ⟨72798073383140560694049005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48532048922093707129366003 72798073383140560694049005)
          ·
            refine ⟨27299277518677710260268377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72798073383140560694049005 27299277518677710260268377)
            ·
              refine ⟨20474458139008282695201283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27299277518677710260268377 20474458139008282695201283)
              ·
                refine ⟨30711687208512424042801925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20474458139008282695201283 30711687208512424042801925)
                ·
                  refine ⟨5758441351596079508025361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30711687208512424042801925 5758441351596079508025361)
                  ·
                    refine ⟨4318831013697059631019021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5758441351596079508025361 4318831013697059631019021)
                    ·
                      refine ⟨1619561630136397361632133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4318831013697059631019021 1619561630136397361632133)
                      ·
                        rfl

theorem cell23_3154085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_3154085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154085 prefixEnd_3154085 := by exact prefixLift 3154085
  have htrace : WordTrace (prefixWord ++ tailWord_3154085) baseStart_3154085 baseEnd_3154085 := by
    simpa [prefixWord, tailWord_3154085, baseEnd_3154085] using wordTrace_append hprefix tailTrace_3154085
  have hstable : (prefixWord ++ tailWord_3154085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154085).length < 2 ^ (prefixWord ++ tailWord_3154085).sum := by decide
  have hdescent : baseEnd_3154085 < baseStart_3154085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154126 : List Nat := [4, 1, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_3154126 : Nat := 118140960795 + 3154126 * 2 ^ 59
def prefixEnd_3154126 : Nat := 4983230072969 + 3 ^ 40 * 3154126 * 2
def baseEnd_3154126 : Nat := 539860894281077233739815

theorem tailTrace_3154126 : CollatzResearch.WordTrace tailWord_3154126 prefixEnd_3154126 539860894281077233739815 := by
  unfold tailWord_3154126
  simp only [CollatzResearch.WordTrace]
  refine ⟨14380053271393457334907279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76693617447431772452838821 14380053271393457334907279)
  ·
    refine ⟨21570079907090186002360919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14380053271393457334907279 21570079907090186002360919)
    ·
      refine ⟨32355119860635279003541379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21570079907090186002360919 32355119860635279003541379)
      ·
        refine ⟨48532679790952918505312069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32355119860635279003541379 48532679790952918505312069)
        ·
          refine ⟨9099877460803672219746013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48532679790952918505312069 9099877460803672219746013)
          ·
            refine ⟨3412454047801377082404755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9099877460803672219746013 3412454047801377082404755)
            ·
              refine ⟨5118681071702065623607133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412454047801377082404755 5118681071702065623607133)
              ·
                refine ⟨1919505401888274608852675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5118681071702065623607133 1919505401888274608852675)
                ·
                  refine ⟨2879258102832411913279013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919505401888274608852675 2879258102832411913279013)
                  ·
                    refine ⟨539860894281077233739815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2879258102832411913279013 539860894281077233739815)
                    ·
                      rfl

theorem cell23_3154126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_3154126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154126 prefixEnd_3154126 := by exact prefixLift 3154126
  have htrace : WordTrace (prefixWord ++ tailWord_3154126) baseStart_3154126 baseEnd_3154126 := by
    simpa [prefixWord, tailWord_3154126, baseEnd_3154126] using wordTrace_append hprefix tailTrace_3154126
  have hstable : (prefixWord ++ tailWord_3154126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154126).length < 2 ^ (prefixWord ++ tailWord_3154126).sum := by decide
  have hdescent : baseEnd_3154126 < baseStart_3154126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154149 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 3, 1, 3]
def baseStart_3154149 : Nat := 118140960795 + 3154149 * 2 ^ 59
def prefixEnd_3154149 : Nat := 4983230072969 + 3 ^ 40 * 3154149 * 2
def baseEnd_3154149 : Nat := 1619594492898285111231839

theorem tailTrace_3154149 : CollatzResearch.WordTrace tailWord_3154149 prefixEnd_3154149 1619594492898285111231839 := by
  unfold tailWord_3154149
  simp only [CollatzResearch.WordTrace]
  refine ⟨115041265050064333607345501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76694176700042889071563667 115041265050064333607345501)
  ·
    refine ⟨43140474393774125102754563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115041265050064333607345501 43140474393774125102754563)
    ·
      refine ⟨64710711590661187654131845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43140474393774125102754563 64710711590661187654131845)
      ·
        refine ⟨12133258423248972685149721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64710711590661187654131845 12133258423248972685149721)
        ·
          refine ⟨9099943817436729513862291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12133258423248972685149721 9099943817436729513862291)
          ·
            refine ⟨13649915726155094270793437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9099943817436729513862291 13649915726155094270793437)
            ·
              refine ⟨5118718397308160351547539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13649915726155094270793437 5118718397308160351547539)
              ·
                refine ⟨7678077595962240527321309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5118718397308160351547539 7678077595962240527321309)
                ·
                  refine ⟨2879279098485840197745491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7678077595962240527321309 2879279098485840197745491)
                  ·
                    refine ⟨4318918647728760296618237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2879279098485840197745491 4318918647728760296618237)
                    ·
                      refine ⟨1619594492898285111231839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4318918647728760296618237 1619594492898285111231839)
                      ·
                        rfl

theorem cell23_3154149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_3154149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154149 prefixEnd_3154149 := by exact prefixLift 3154149
  have htrace : WordTrace (prefixWord ++ tailWord_3154149) baseStart_3154149 baseEnd_3154149 := by
    simpa [prefixWord, tailWord_3154149, baseEnd_3154149] using wordTrace_append hprefix tailTrace_3154149
  have hstable : (prefixWord ++ tailWord_3154149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154149).length < 2 ^ (prefixWord ++ tailWord_3154149).sum := by decide
  have hdescent : baseEnd_3154149 < baseStart_3154149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154155 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 4]
def baseStart_3154155 : Nat := 118140960795 + 3154155 * 2 ^ 59
def prefixEnd_3154155 : Nat := 4983230072969 + 3 ^ 40 * 3154155 * 2
def baseEnd_3154155 : Nat := 1619597573782212087756811

theorem tailTrace_3154155 : CollatzResearch.WordTrace tailWord_3154155 prefixEnd_3154155 1619597573782212087756811 := by
  unfold tailWord_3154155
  simp only [CollatzResearch.WordTrace]
  refine ⟨115041483888042596632063919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76694322592028397754709279 115041483888042596632063919)
  ·
    refine ⟨172562225832063894948095879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115041483888042596632063919 172562225832063894948095879)
    ·
      refine ⟨258843338748095842422143819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172562225832063894948095879 258843338748095842422143819)
      ·
        refine ⟨388265008122143763633215729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258843338748095842422143819 388265008122143763633215729)
        ·
          refine ⟨291198756091607822724911797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388265008122143763633215729 291198756091607822724911797)
          ·
            refine ⟨27299883383588233380460481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291198756091607822724911797 27299883383588233380460481)
            ·
              refine ⟨20474912537691175035345361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27299883383588233380460481 20474912537691175035345361)
              ·
                refine ⟨15356184403268381276509021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20474912537691175035345361 15356184403268381276509021)
                ·
                  refine ⟨5758569151225642978690883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15356184403268381276509021 5758569151225642978690883)
                  ·
                    refine ⟨8637853726838464468036325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5758569151225642978690883 8637853726838464468036325)
                    ·
                      refine ⟨1619597573782212087756811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8637853726838464468036325 1619597573782212087756811)
                      ·
                        rfl

theorem cell23_3154155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 4].length) (baseStart_3154155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154155 prefixEnd_3154155 := by exact prefixLift 3154155
  have htrace : WordTrace (prefixWord ++ tailWord_3154155) baseStart_3154155 baseEnd_3154155 := by
    simpa [prefixWord, tailWord_3154155, baseEnd_3154155] using wordTrace_append hprefix tailTrace_3154155
  have hstable : (prefixWord ++ tailWord_3154155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154155).length < 2 ^ (prefixWord ++ tailWord_3154155).sum := by decide
  have hdescent : baseEnd_3154155 < baseStart_3154155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154172 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_3154172 : Nat := 118140960795 + 3154172 * 2 ^ 59
def prefixEnd_3154172 : Nat := 4983230072969 + 3 ^ 40 * 3154172 * 2
def baseEnd_3154172 : Nat := 1619606302953338521244233

theorem tailTrace_3154172 : CollatzResearch.WordTrace tailWord_3154172 prefixEnd_3154172 1619606302953338521244233 := by
  unfold tailWord_3154172
  simp only [CollatzResearch.WordTrace]
  refine ⟨57521051964490504267716385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76694735952654005690288513 57521051964490504267716385)
  ·
    refine ⟨43140788973367878200787289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57521051964490504267716385 43140788973367878200787289)
    ·
      refine ⟨32355591730025908650590467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43140788973367878200787289 32355591730025908650590467)
      ·
        refine ⟨48533387595038862975885701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32355591730025908650590467 48533387595038862975885701)
        ·
          refine ⟨9100010174069786807978569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48533387595038862975885701 9100010174069786807978569)
          ·
            refine ⟨6825007630552340105983927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9100010174069786807978569 6825007630552340105983927)
            ·
              refine ⟨10237511445828510158975891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825007630552340105983927 10237511445828510158975891)
              ·
                refine ⟨15356267168742765238463837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10237511445828510158975891 15356267168742765238463837)
                ·
                  refine ⟨5758600188278536964423939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15356267168742765238463837 5758600188278536964423939)
                  ·
                    refine ⟨8637900282417805446635909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5758600188278536964423939 8637900282417805446635909)
                    ·
                      refine ⟨1619606302953338521244233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8637900282417805446635909 1619606302953338521244233)
                      ·
                        rfl

theorem cell23_3154172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_3154172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154172 prefixEnd_3154172 := by exact prefixLift 3154172
  have htrace : WordTrace (prefixWord ++ tailWord_3154172) baseStart_3154172 baseEnd_3154172 := by
    simpa [prefixWord, tailWord_3154172, baseEnd_3154172] using wordTrace_append hprefix tailTrace_3154172
  have hstable : (prefixWord ++ tailWord_3154172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154172).length < 2 ^ (prefixWord ++ tailWord_3154172).sum := by decide
  have hdescent : baseEnd_3154172 < baseStart_3154172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154185 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 4]
def baseStart_3154185 : Nat := 118140960795 + 3154185 * 2 ^ 59
def prefixEnd_3154185 : Nat := 4983230072969 + 3 ^ 40 * 3154185 * 2
def baseEnd_3154185 : Nat := 1619612978201846970381673

theorem tailTrace_3154185 : CollatzResearch.WordTrace tailWord_3154185 prefixEnd_3154185 1619612978201846970381673 := by
  unfold tailWord_3154185
  simp only [CollatzResearch.WordTrace]
  refine ⟨115042578077933911755656009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76695052051955941170437339 115042578077933911755656009)
  ·
    refine ⟨86281933558450433816742007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115042578077933911755656009 86281933558450433816742007)
    ·
      refine ⟨129422900337675650725113011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86281933558450433816742007 129422900337675650725113011)
      ·
        refine ⟨194134350506513476087669517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129422900337675650725113011 194134350506513476087669517)
        ·
          refine ⟨72800381439942553532876069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194134350506513476087669517 72800381439942553532876069)
          ·
            refine ⟨13650071519989228787414263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72800381439942553532876069 13650071519989228787414263)
            ·
              refine ⟨20475107279983843181121395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13650071519989228787414263 20475107279983843181121395)
              ·
                refine ⟨30712660919975764771682093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20475107279983843181121395 30712660919975764771682093)
                ·
                  refine ⟨11517247844990911789380785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30712660919975764771682093 11517247844990911789380785)
                  ·
                    refine ⟨8637935883743183842035589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11517247844990911789380785 8637935883743183842035589)
                    ·
                      refine ⟨1619612978201846970381673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8637935883743183842035589 1619612978201846970381673)
                      ·
                        rfl

theorem cell23_3154185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_3154185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154185 prefixEnd_3154185 := by exact prefixLift 3154185
  have htrace : WordTrace (prefixWord ++ tailWord_3154185) baseStart_3154185 baseEnd_3154185 := by
    simpa [prefixWord, tailWord_3154185, baseEnd_3154185] using wordTrace_append hprefix tailTrace_3154185
  have hstable : (prefixWord ++ tailWord_3154185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154185).length < 2 ^ (prefixWord ++ tailWord_3154185).sum := by decide
  have hdescent : baseEnd_3154185 < baseStart_3154185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154199 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 2, 4]
def baseStart_3154199 : Nat := 118140960795 + 3154199 * 2 ^ 59
def prefixEnd_3154199 : Nat := 4983230072969 + 3 ^ 40 * 3154199 * 2
def baseEnd_3154199 : Nat := 539873388977003305202203

theorem tailTrace_3154199 : CollatzResearch.WordTrace tailWord_3154199 prefixEnd_3154199 539873388977003305202203 := by
  unfold tailWord_3154199
  simp only [CollatzResearch.WordTrace]
  refine ⟨115043088699883192146665651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76695392466588794764443767 115043088699883192146665651)
  ·
    refine ⟨172564633049824788219998477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115043088699883192146665651 172564633049824788219998477)
    ·
      refine ⟨64711737393684295582499429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172564633049824788219998477 64711737393684295582499429)
      ·
        refine ⟨12133450761315805421718643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64711737393684295582499429 12133450761315805421718643)
        ·
          refine ⟨18200176141973708132577965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12133450761315805421718643 18200176141973708132577965)
          ·
            refine ⟨6825066053240140549716737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18200176141973708132577965 6825066053240140549716737)
            ·
              refine ⟨5118799539930105412287553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6825066053240140549716737 5118799539930105412287553)
              ·
                refine ⟨3839099654947579059215665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5118799539930105412287553 3839099654947579059215665)
                ·
                  refine ⟨2879324741210684294411749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839099654947579059215665 2879324741210684294411749)
                  ·
                    refine ⟨539873388977003305202203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2879324741210684294411749 539873388977003305202203)
                    ·
                      rfl

theorem cell23_3154199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_3154199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154199 prefixEnd_3154199 := by exact prefixLift 3154199
  have htrace : WordTrace (prefixWord ++ tailWord_3154199) baseStart_3154199 baseEnd_3154199 := by
    simpa [prefixWord, tailWord_3154199, baseEnd_3154199] using wordTrace_append hprefix tailTrace_3154199
  have hstable : (prefixWord ++ tailWord_3154199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154199).length < 2 ^ (prefixWord ++ tailWord_3154199).sum := by decide
  have hdescent : baseEnd_3154199 < baseStart_3154199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154212 : List Nat := [2, 3, 1, 3, 1, 4, 1, 8]
def baseStart_3154212 : Nat := 118140960795 + 3154212 * 2 ^ 59
def prefixEnd_3154212 : Nat := 4983230072969 + 3 ^ 40 * 3154212 * 2
def baseEnd_3154212 : Nat := 59986179339982161657187

theorem tailTrace_3154212 : CollatzResearch.WordTrace tailWord_3154212 prefixEnd_3154212 59986179339982161657187 := by
  unfold tailWord_3154212
  simp only [CollatzResearch.WordTrace]
  refine ⟨57521781424418047683444445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76695708565890730244592593 57521781424418047683444445)
  ·
    refine ⟨21570668034156767881291667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57521781424418047683444445 21570668034156767881291667)
    ·
      refine ⟨32356002051235151821937501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21570668034156767881291667 32356002051235151821937501)
      ·
        refine ⟨12133500769213181933226563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32356002051235151821937501 12133500769213181933226563)
        ·
          refine ⟨18200251153819772899839845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12133500769213181933226563 18200251153819772899839845)
          ·
            refine ⟨3412547091341207418719971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18200251153819772899839845 3412547091341207418719971)
            ·
              refine ⟨5118820637011811128079957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412547091341207418719971 5118820637011811128079957)
              ·
                refine ⟨59986179339982161657187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5118820637011811128079957 59986179339982161657187)
                ·
                  rfl

theorem cell23_3154212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 8].length) (baseStart_3154212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154212 prefixEnd_3154212 := by exact prefixLift 3154212
  have htrace : WordTrace (prefixWord ++ tailWord_3154212) baseStart_3154212 baseEnd_3154212 := by
    simpa [prefixWord, tailWord_3154212, baseEnd_3154212] using wordTrace_append hprefix tailTrace_3154212
  have hstable : (prefixWord ++ tailWord_3154212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154212).length < 2 ^ (prefixWord ++ tailWord_3154212).sum := by decide
  have hdescent : baseEnd_3154212 < baseStart_3154212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154256 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 2, 1, 3]
def baseStart_3154256 : Nat := 118140960795 + 3154256 * 2 ^ 59
def prefixEnd_3154256 : Nat := 4983230072969 + 3 ^ 40 * 3154256 * 2
def baseEnd_3154256 : Nat := 1619649435328316192593847

theorem tailTrace_3154256 : CollatzResearch.WordTrace tailWord_3154256 prefixEnd_3154256 1619649435328316192593847 := by
  unfold tailWord_3154256
  simp only [CollatzResearch.WordTrace]
  refine ⟨57522583830338345440745311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76696778440451127254327081 57522583830338345440745311)
  ·
    refine ⟨86283875745507518161117967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57522583830338345440745311 86283875745507518161117967)
    ·
      refine ⟨129425813618261277241676951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86283875745507518161117967 129425813618261277241676951)
      ·
        refine ⟨194138720427391915862515427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129425813618261277241676951 194138720427391915862515427)
        ·
          refine ⟨291208080641087873793773141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194138720427391915862515427 291208080641087873793773141)
          ·
            refine ⟨3412594695012748521020779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 291208080641087873793773141 3412594695012748521020779)
            ·
              refine ⟨5118892042519122781531169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412594695012748521020779 5118892042519122781531169)
              ·
                refine ⟨3839169031889342086148377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5118892042519122781531169 3839169031889342086148377)
                ·
                  refine ⟨2879376773917006564611283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839169031889342086148377 2879376773917006564611283)
                  ·
                    refine ⟨4319065160875509846916925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2879376773917006564611283 4319065160875509846916925)
                    ·
                      refine ⟨1619649435328316192593847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4319065160875509846916925 1619649435328316192593847)
                      ·
                        rfl

theorem cell23_3154256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2, 1, 3].length) (baseStart_3154256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154256 prefixEnd_3154256 := by exact prefixLift 3154256
  have htrace : WordTrace (prefixWord ++ tailWord_3154256) baseStart_3154256 baseEnd_3154256 := by
    simpa [prefixWord, tailWord_3154256, baseEnd_3154256] using wordTrace_append hprefix tailTrace_3154256
  have hstable : (prefixWord ++ tailWord_3154256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154256).length < 2 ^ (prefixWord ++ tailWord_3154256).sum := by decide
  have hdescent : baseEnd_3154256 < baseStart_3154256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154265 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 5]
def baseStart_3154265 : Nat := 118140960795 + 3154265 * 2 ^ 59
def prefixEnd_3154265 : Nat := 4983230072969 + 3 ^ 40 * 3154265 * 2
def baseEnd_3154265 : Nat := 1619654056654206657381305

theorem tailTrace_3154265 : CollatzResearch.WordTrace tailWord_3154265 prefixEnd_3154265 1619654056654206657381305 := by
  unfold tailWord_3154265
  simp only [CollatzResearch.WordTrace]
  refine ⟨115045495917644085418568249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76696997278429390279045499 115045495917644085418568249)
  ·
    refine ⟨86284121938233064063926187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115045495917644085418568249 86284121938233064063926187)
    ·
      refine ⟨129426182907349596095889281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86284121938233064063926187 129426182907349596095889281)
      ·
        refine ⟨97069637180512197071916961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129426182907349596095889281 97069637180512197071916961)
        ·
          refine ⟨72802227885384147803937721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97069637180512197071916961 72802227885384147803937721)
          ·
            refine ⟨54601670914038110852953291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72802227885384147803937721 54601670914038110852953291)
            ·
              refine ⟨81902506371057166279429937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54601670914038110852953291 81902506371057166279429937)
              ·
                refine ⟨61426879778292874709572453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81902506371057166279429937 61426879778292874709572453)
                ·
                  refine ⟨11517539958429914008044835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61426879778292874709572453 11517539958429914008044835)
                  ·
                    refine ⟨17276309937644871012067253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11517539958429914008044835 17276309937644871012067253)
                    ·
                      refine ⟨1619654056654206657381305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17276309937644871012067253 1619654056654206657381305)
                      ·
                        rfl

theorem cell23_3154265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_3154265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154265 prefixEnd_3154265 := by exact prefixLift 3154265
  have htrace : WordTrace (prefixWord ++ tailWord_3154265) baseStart_3154265 baseEnd_3154265 := by
    simpa [prefixWord, tailWord_3154265, baseEnd_3154265] using wordTrace_append hprefix tailTrace_3154265
  have hstable : (prefixWord ++ tailWord_3154265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154265).length < 2 ^ (prefixWord ++ tailWord_3154265).sum := by decide
  have hdescent : baseEnd_3154265 < baseStart_3154265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154330 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2]
def baseStart_3154330 : Nat := 118140960795 + 3154330 * 2 ^ 59
def prefixEnd_3154330 : Nat := 4983230072969 + 3 ^ 40 * 3154330 * 2
def baseEnd_3154330 : Nat := 1619687432896748903068507

theorem tailTrace_3154330 : CollatzResearch.WordTrace tailWord_3154330 prefixEnd_3154330 1619687432896748903068507 := by
  unfold tailWord_3154330
  simp only [CollatzResearch.WordTrace]
  refine ⟨28761966665602150379921111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76698577774939067679789629 28761966665602150379921111)
  ·
    refine ⟨43142949998403225569881667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28761966665602150379921111 43142949998403225569881667)
    ·
      refine ⟨64714424997604838354822501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43142949998403225569881667 64714424997604838354822501)
      ·
        refine ⟨12133954687050907191529219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64714424997604838354822501 12133954687050907191529219)
        ·
          refine ⟨18200932030576360787293829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12133954687050907191529219 18200932030576360787293829)
          ·
            refine ⟨3412674755733067647617593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18200932030576360787293829 3412674755733067647617593)
            ·
              refine ⟨2559506066799800735713195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3412674755733067647617593 2559506066799800735713195)
              ·
                refine ⟨3839259100199701103569793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2559506066799800735713195 3839259100199701103569793)
                ·
                  refine ⟨2879444325149775827677345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839259100199701103569793 2879444325149775827677345)
                  ·
                    refine ⟨2159583243862331870758009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2879444325149775827677345 2159583243862331870758009)
                    ·
                      refine ⟨1619687432896748903068507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2159583243862331870758009 1619687432896748903068507)
                      ·
                        rfl

theorem cell23_3154330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_3154330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154330 prefixEnd_3154330 := by exact prefixLift 3154330
  have htrace : WordTrace (prefixWord ++ tailWord_3154330) baseStart_3154330 baseEnd_3154330 := by
    simpa [prefixWord, tailWord_3154330, baseEnd_3154330] using wordTrace_append hprefix tailTrace_3154330
  have hstable : (prefixWord ++ tailWord_3154330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154330).length < 2 ^ (prefixWord ++ tailWord_3154330).sum := by decide
  have hdescent : baseEnd_3154330 < baseStart_3154330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154345 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 2, 8]
def baseStart_3154345 : Nat := 118140960795 + 3154345 * 2 ^ 59
def prefixEnd_3154345 : Nat := 4983230072969 + 3 ^ 40 * 3154345 * 2
def baseEnd_3154345 : Nat := 539898378368855448126979

theorem tailTrace_3154345 : CollatzResearch.WordTrace tailWord_3154345 prefixEnd_3154345 539898378368855448126979 := by
  unfold tailWord_3154345
  simp only [CollatzResearch.WordTrace]
  refine ⟨115048413757354259081480489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76698942504902839387653659 115048413757354259081480489)
  ·
    refine ⟨86286310318015694311110367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115048413757354259081480489 86286310318015694311110367)
    ·
      refine ⟨129429465477023541466665551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86286310318015694311110367 129429465477023541466665551)
      ·
        refine ⟨194144198215535312199998327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129429465477023541466665551 194144198215535312199998327)
        ·
          refine ⟨291216297323302968299997491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194144198215535312199998327 291216297323302968299997491)
          ·
            refine ⟨436824445984954452449996237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291216297323302968299997491 436824445984954452449996237)
            ·
              refine ⟨163809167244357919668748589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 436824445984954452449996237 163809167244357919668748589)
              ·
                refine ⟨61428437716634219875780721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163809167244357919668748589 61428437716634219875780721)
                ·
                  refine ⟨46071328287475664906835541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61428437716634219875780721 46071328287475664906835541)
                  ·
                    refine ⟨539898378368855448126979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46071328287475664906835541 539898378368855448126979)
                    ·
                      rfl

theorem cell23_3154345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_3154345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154345 prefixEnd_3154345 := by exact prefixLift 3154345
  have htrace : WordTrace (prefixWord ++ tailWord_3154345) baseStart_3154345 baseEnd_3154345 := by
    simpa [prefixWord, tailWord_3154345, baseEnd_3154345] using wordTrace_append hprefix tailTrace_3154345
  have hstable : (prefixWord ++ tailWord_3154345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154345).length < 2 ^ (prefixWord ++ tailWord_3154345).sum := by decide
  have hdescent : baseEnd_3154345 < baseStart_3154345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154355 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 9]
def baseStart_3154355 : Nat := 118140960795 + 3154355 * 2 ^ 59
def prefixEnd_3154355 : Nat := 4983230072969 + 3 ^ 40 * 3154355 * 2
def baseEnd_3154355 : Nat := 1619700269913111305255891

theorem tailTrace_3154355 : CollatzResearch.WordTrace tailWord_3154355 prefixEnd_3154355 1619700269913111305255891 := by
  unfold tailWord_3154355
  simp only [CollatzResearch.WordTrace]
  refine ⟨115048778487318030789344519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76699185658212020526229679 115048778487318030789344519)
  ·
    refine ⟨172573167730977046184016779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115048778487318030789344519 172573167730977046184016779)
    ·
      refine ⟨258859751596465569276025169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172573167730977046184016779 258859751596465569276025169)
      ·
        refine ⟨194144813697349176957018877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258859751596465569276025169 194144813697349176957018877)
        ·
          refine ⟨72804305136505941358882079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194144813697349176957018877 72804305136505941358882079)
          ·
            refine ⟨109206457704758912038323119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72804305136505941358882079 109206457704758912038323119)
            ·
              refine ⟨163809686557138368057484679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109206457704758912038323119 163809686557138368057484679)
              ·
                refine ⟨245714529835707552086227019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163809686557138368057484679 245714529835707552086227019)
                ·
                  refine ⟨368571794753561328129340529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245714529835707552086227019 368571794753561328129340529)
                  ·
                    refine ⟨276428846065170996097005397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 368571794753561328129340529 276428846065170996097005397)
                    ·
                      refine ⟨1619700269913111305255891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 276428846065170996097005397 1619700269913111305255891)
                      ·
                        rfl

theorem cell23_3154355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_3154355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154355 prefixEnd_3154355 := by exact prefixLift 3154355
  have htrace : WordTrace (prefixWord ++ tailWord_3154355) baseStart_3154355 baseEnd_3154355 := by
    simpa [prefixWord, tailWord_3154355, baseEnd_3154355] using wordTrace_append hprefix tailTrace_3154355
  have hstable : (prefixWord ++ tailWord_3154355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154355).length < 2 ^ (prefixWord ++ tailWord_3154355).sum := by decide
  have hdescent : baseEnd_3154355 < baseStart_3154355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154382 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_3154382 : Nat := 118140960795 + 3154382 * 2 ^ 59
def prefixEnd_3154382 : Nat := 4983230072969 + 3 ^ 40 * 3154382 * 2
def baseEnd_3154382 : Nat := 1619714133890782699618267

theorem tailTrace_3154382 : CollatzResearch.WordTrace tailWord_3154382 prefixEnd_3154382 1619714133890782699618267 := by
  unfold tailWord_3154382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14381220407277526800072175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76699842172146809600384933 14381220407277526800072175)
  ·
    refine ⟨21571830610916290200108263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14381220407277526800072175 21571830610916290200108263)
    ·
      refine ⟨32357745916374435300162395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21571830610916290200108263 32357745916374435300162395)
      ·
        refine ⟨48536618874561652950243593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32357745916374435300162395 48536618874561652950243593)
        ·
          refine ⟨36402464155921239712682695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48536618874561652950243593 36402464155921239712682695)
          ·
            refine ⟨54603696233881859569024043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36402464155921239712682695 54603696233881859569024043)
            ·
              refine ⟨81905544350822789353536065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54603696233881859569024043 81905544350822789353536065)
              ·
                refine ⟨61429158263117092015152049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81905544350822789353536065 61429158263117092015152049)
                ·
                  refine ⟨46071868697337819011364037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61429158263117092015152049 46071868697337819011364037)
                  ·
                    refine ⟨8638475380750841064630757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46071868697337819011364037 8638475380750841064630757)
                    ·
                      refine ⟨1619714133890782699618267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8638475380750841064630757 1619714133890782699618267)
                      ·
                        rfl

theorem cell23_3154382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_3154382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154382 prefixEnd_3154382 := by exact prefixLift 3154382
  have htrace : WordTrace (prefixWord ++ tailWord_3154382) baseStart_3154382 baseEnd_3154382 := by
    simpa [prefixWord, tailWord_3154382, baseEnd_3154382] using wordTrace_append hprefix tailTrace_3154382
  have hstable : (prefixWord ++ tailWord_3154382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154382).length < 2 ^ (prefixWord ++ tailWord_3154382).sum := by decide
  have hdescent : baseEnd_3154382 < baseStart_3154382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154403 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 2, 1, 4]
def baseStart_3154403 : Nat := 118140960795 + 3154403 * 2 ^ 59
def prefixEnd_3154403 : Nat := 4983230072969 + 3 ^ 40 * 3154403 * 2
def baseEnd_3154403 : Nat := 1619724916984527117455671

theorem tailTrace_3154403 : CollatzResearch.WordTrace tailWord_3154403 prefixEnd_3154403 1619724916984527117455671 := by
  unfold tailWord_3154403
  simp only [CollatzResearch.WordTrace]
  refine ⟨115050529191144134987091863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76700352794096089991394575 115050529191144134987091863)
  ·
    refine ⟨172575793786716202480637795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115050529191144134987091863 172575793786716202480637795)
    ·
      refine ⟨258863690680074303720956693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172575793786716202480637795 258863690680074303720956693)
      ·
        refine ⟨12134235500628482986919845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 258863690680074303720956693 12134235500628482986919845)
        ·
          refine ⟨2275169156367840560047471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12134235500628482986919845 2275169156367840560047471)
          ·
            refine ⟨3412753734551760840071207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275169156367840560047471 3412753734551760840071207)
            ·
              refine ⟨5119130601827641260106811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412753734551760840071207 5119130601827641260106811)
              ·
                refine ⟨7678695902741461890160217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5119130601827641260106811 7678695902741461890160217)
                ·
                  refine ⟨5759021927056096417620163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7678695902741461890160217 5759021927056096417620163)
                  ·
                    refine ⟨8638532890584144626430245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5759021927056096417620163 8638532890584144626430245)
                    ·
                      refine ⟨1619724916984527117455671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8638532890584144626430245 1619724916984527117455671)
                      ·
                        rfl

theorem cell23_3154403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_3154403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154403 prefixEnd_3154403 := by exact prefixLift 3154403
  have htrace : WordTrace (prefixWord ++ tailWord_3154403) baseStart_3154403 baseEnd_3154403 := by
    simpa [prefixWord, tailWord_3154403, baseEnd_3154403] using wordTrace_append hprefix tailTrace_3154403
  have hstable : (prefixWord ++ tailWord_3154403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154403).length < 2 ^ (prefixWord ++ tailWord_3154403).sum := by decide
  have hdescent : baseEnd_3154403 < baseStart_3154403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154413 : List Nat := [1, 5, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_3154413 : Nat := 118140960795 + 3154413 * 2 ^ 59
def prefixEnd_3154413 : Nat := 4983230072969 + 3 ^ 40 * 3154413 * 2
def baseEnd_3154413 : Nat := 539910017263690692776875

theorem tailTrace_3154413 : CollatzResearch.WordTrace tailWord_3154413 prefixEnd_3154413 539910017263690692776875 := by
  unfold tailWord_3154413
  simp only [CollatzResearch.WordTrace]
  refine ⟨115050893921107906694955893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76700595947405271129970595 115050893921107906694955893)
  ·
    refine ⟨10786021305103866252652115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115050893921107906694955893 10786021305103866252652115)
    ·
      refine ⟨16179031957655799378978173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10786021305103866252652115 16179031957655799378978173)
      ·
        refine ⟨6067136984120924767116815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16179031957655799378978173 6067136984120924767116815)
        ·
          refine ⟨9100705476181387150675223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6067136984120924767116815 9100705476181387150675223)
          ·
            refine ⟨13651058214272080726012835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9100705476181387150675223 13651058214272080726012835)
            ·
              refine ⟨20476587321408121089019253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13651058214272080726012835 20476587321408121089019253)
              ·
                refine ⟨1919680061382011352095555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20476587321408121089019253 1919680061382011352095555)
                ·
                  refine ⟨2879520092073017028143333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919680061382011352095555 2879520092073017028143333)
                  ·
                    refine ⟨539910017263690692776875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2879520092073017028143333 539910017263690692776875)
                    ·
                      rfl

theorem cell23_3154413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_3154413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154413 prefixEnd_3154413 := by exact prefixLift 3154413
  have htrace : WordTrace (prefixWord ++ tailWord_3154413) baseStart_3154413 baseEnd_3154413 := by
    simpa [prefixWord, tailWord_3154413, baseEnd_3154413] using wordTrace_append hprefix tailTrace_3154413
  have hstable : (prefixWord ++ tailWord_3154413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154413).length < 2 ^ (prefixWord ++ tailWord_3154413).sum := by decide
  have hdescent : baseEnd_3154413 < baseStart_3154413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154419 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 5, 1, 3]
def baseStart_3154419 : Nat := 118140960795 + 3154419 * 2 ^ 59
def prefixEnd_3154419 : Nat := 4983230072969 + 3 ^ 40 * 3154419 * 2
def baseEnd_3154419 : Nat := 1619733132674999054855597

theorem tailTrace_3154419 : CollatzResearch.WordTrace tailWord_3154419 prefixEnd_3154419 1619733132674999054855597 := by
  unfold tailWord_3154419
  simp only [CollatzResearch.WordTrace]
  refine ⟨115051112759086169719674311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76700741839390779813116207 115051112759086169719674311)
  ·
    refine ⟨172576669138629254579511467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115051112759086169719674311 172576669138629254579511467)
    ·
      refine ⟨258865003707943881869267201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172576669138629254579511467 258865003707943881869267201)
      ·
        refine ⟨194148752780957911401950401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258865003707943881869267201 194148752780957911401950401)
        ·
          refine ⟨145611564585718433551462801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194148752780957911401950401 145611564585718433551462801)
          ·
            refine ⟨109208673439288825163597101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145611564585718433551462801 109208673439288825163597101)
            ·
              refine ⟨40953252539733309436348913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109208673439288825163597101 40953252539733309436348913)
              ·
                refine ⟨30714939404799982077261685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40953252539733309436348913 30714939404799982077261685)
                ·
                  refine ⟨2879525569199998319743283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30714939404799982077261685 2879525569199998319743283)
                  ·
                    refine ⟨4319288353799997479614925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2879525569199998319743283 4319288353799997479614925)
                    ·
                      refine ⟨1619733132674999054855597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4319288353799997479614925 1619733132674999054855597)
                      ·
                        rfl

theorem cell23_3154419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 1, 3].length) (baseStart_3154419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154419 prefixEnd_3154419 := by exact prefixLift 3154419
  have htrace : WordTrace (prefixWord ++ tailWord_3154419) baseStart_3154419 baseEnd_3154419 := by
    simpa [prefixWord, tailWord_3154419, baseEnd_3154419] using wordTrace_append hprefix tailTrace_3154419
  have hstable : (prefixWord ++ tailWord_3154419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154419).length < 2 ^ (prefixWord ++ tailWord_3154419).sum := by decide
  have hdescent : baseEnd_3154419 < baseStart_3154419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154446 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2]
def baseStart_3154446 : Nat := 118140960795 + 3154446 * 2 ^ 59
def prefixEnd_3154446 : Nat := 4983230072969 + 3 ^ 40 * 3154446 * 2
def baseEnd_3154446 : Nat := 1619746996652670449217973

theorem tailTrace_3154446 : CollatzResearch.WordTrace tailWord_3154446 prefixEnd_3154446 1619746996652670449217973 := by
  unfold tailWord_3154446
  simp only [CollatzResearch.WordTrace]
  refine ⟨14381512191248544166363399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76701398353325568887271461 14381512191248544166363399)
  ·
    refine ⟨21572268286872816249545099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14381512191248544166363399 21572268286872816249545099)
    ·
      refine ⟨32358402430309224374317649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21572268286872816249545099 32358402430309224374317649)
      ·
        refine ⟨24268801822731918280738237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32358402430309224374317649 24268801822731918280738237)
        ·
          refine ⟨9100800683524469355276839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24268801822731918280738237 9100800683524469355276839)
          ·
            refine ⟨13651201025286704032915259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9100800683524469355276839 13651201025286704032915259)
            ·
              refine ⟨20476801537930056049372889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13651201025286704032915259 20476801537930056049372889)
              ·
                refine ⟨15357601153447542037029667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20476801537930056049372889 15357601153447542037029667)
                ·
                  refine ⟨23036401730171313055544501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15357601153447542037029667 23036401730171313055544501)
                  ·
                    refine ⟨2159662662203560598957297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23036401730171313055544501 2159662662203560598957297)
                    ·
                      refine ⟨1619746996652670449217973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2159662662203560598957297 1619746996652670449217973)
                      ·
                        rfl

theorem cell23_3154446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_3154446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154446 prefixEnd_3154446 := by exact prefixLift 3154446
  have htrace : WordTrace (prefixWord ++ tailWord_3154446) baseStart_3154446 baseEnd_3154446 := by
    simpa [prefixWord, tailWord_3154446, baseEnd_3154446] using wordTrace_append hprefix tailTrace_3154446
  have hstable : (prefixWord ++ tailWord_3154446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154446).length < 2 ^ (prefixWord ++ tailWord_3154446).sum := by decide
  have hdescent : baseEnd_3154446 < baseStart_3154446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154456 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 1, 5]
def baseStart_3154456 : Nat := 118140960795 + 3154456 * 2 ^ 59
def prefixEnd_3154456 : Nat := 4983230072969 + 3 ^ 40 * 3154456 * 2
def baseEnd_3154456 : Nat := 539917377153071803364309

theorem tailTrace_3154456 : CollatzResearch.WordTrace tailWord_3154456 prefixEnd_3154456 539917377153071803364309 := by
  unfold tailWord_3154456
  simp only [CollatzResearch.WordTrace]
  refine ⟨57526231129976062519385611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76701641506634750025847481 57526231129976062519385611)
  ·
    refine ⟨86289346694964093779078417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57526231129976062519385611 86289346694964093779078417)
    ·
      refine ⟨64717010021223070334308813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86289346694964093779078417 64717010021223070334308813)
      ·
        refine ⟨24268878757958651375365805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64717010021223070334308813 24268878757958651375365805)
        ·
          refine ⟨9100829534234494265762177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24268878757958651375365805 9100829534234494265762177)
          ·
            refine ⟨6825622150675870699321633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9100829534234494265762177 6825622150675870699321633)
            ·
              refine ⟨5119216613006903024491225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6825622150675870699321633 5119216613006903024491225)
              ·
                refine ⟨3839412459755177268368419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5119216613006903024491225 3839412459755177268368419)
                ·
                  refine ⟨5759118689632765902552629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3839412459755177268368419 5759118689632765902552629)
                  ·
                    refine ⟨539917377153071803364309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5759118689632765902552629 539917377153071803364309)
                    ·
                      rfl

theorem cell23_3154456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_3154456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154456 prefixEnd_3154456 := by exact prefixLift 3154456
  have htrace : WordTrace (prefixWord ++ tailWord_3154456) baseStart_3154456 baseEnd_3154456 := by
    simpa [prefixWord, tailWord_3154456, baseEnd_3154456] using wordTrace_append hprefix tailTrace_3154456
  have hstable : (prefixWord ++ tailWord_3154456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154456).length < 2 ^ (prefixWord ++ tailWord_3154456).sum := by decide
  have hdescent : baseEnd_3154456 < baseStart_3154456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154469 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 4, 4]
def baseStart_3154469 : Nat := 118140960795 + 3154469 * 2 ^ 59
def prefixEnd_3154469 : Nat := 4983230072969 + 3 ^ 40 * 3154469 * 2
def baseEnd_3154469 : Nat := 539919602235907953076789

theorem tailTrace_3154469 : CollatzResearch.WordTrace tailWord_3154469 prefixEnd_3154469 539919602235907953076789 := by
  unfold tailWord_3154469
  simp only [CollatzResearch.WordTrace]
  refine ⟨115052936408905028258994461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76701957605936685505996307 115052936408905028258994461)
  ·
    refine ⟨43144851153339385597122923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115052936408905028258994461 43144851153339385597122923)
    ·
      refine ⟨64717276730009078395684385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43144851153339385597122923 64717276730009078395684385)
      ·
        refine ⟨48537957547506808796763289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64717276730009078395684385 48537957547506808796763289)
        ·
          refine ⟨36403468160630106597572467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48537957547506808796763289 36403468160630106597572467)
          ·
            refine ⟨54605202240945159896358701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36403468160630106597572467 54605202240945159896358701)
            ·
              refine ⟨20476950840354434961134513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54605202240945159896358701 20476950840354434961134513)
              ·
                refine ⟨15357713130265826220850885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20476950840354434961134513 15357713130265826220850885)
                ·
                  refine ⟨2879571211924842416409541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15357713130265826220850885 2879571211924842416409541)
                  ·
                    refine ⟨539919602235907953076789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2879571211924842416409541 539919602235907953076789)
                    ·
                      rfl

theorem cell23_3154469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_3154469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154469 prefixEnd_3154469 := by exact prefixLift 3154469
  have htrace : WordTrace (prefixWord ++ tailWord_3154469) baseStart_3154469 baseEnd_3154469 := by
    simpa [prefixWord, tailWord_3154469, baseEnd_3154469] using wordTrace_append hprefix tailTrace_3154469
  have hstable : (prefixWord ++ tailWord_3154469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154469).length < 2 ^ (prefixWord ++ tailWord_3154469).sum := by decide
  have hdescent : baseEnd_3154469 < baseStart_3154469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154476 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 5, 2, 2]
def baseStart_3154476 : Nat := 118140960795 + 3154476 * 2 ^ 59
def prefixEnd_3154476 : Nat := 4983230072969 + 3 ^ 40 * 3154476 * 2
def baseEnd_3154476 : Nat := 1619762401072305331842835

theorem tailTrace_3154476 : CollatzResearch.WordTrace tailWord_3154476 prefixEnd_3154476 1619762401072305331842835 := by
  unfold tailWord_3154476
  simp only [CollatzResearch.WordTrace]
  refine ⟨57526595859939834227249641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76702127813253112302999521 57526595859939834227249641)
  ·
    refine ⟨43144946894954875670437231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57526595859939834227249641 43144946894954875670437231)
    ·
      refine ⟨64717420342432313505655847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43144946894954875670437231 64717420342432313505655847)
      ·
        refine ⟨97076130513648470258483771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64717420342432313505655847 97076130513648470258483771)
        ·
          refine ⟨145614195770472705387725657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97076130513648470258483771 145614195770472705387725657)
          ·
            refine ⟨109210646827854529040794243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145614195770472705387725657 109210646827854529040794243)
            ·
              refine ⟨163815970241781793561191365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109210646827854529040794243 163815970241781793561191365)
              ·
                refine ⟨30715494420334086292723381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163815970241781793561191365 30715494420334086292723381)
                ·
                  refine ⟨2879577601906320589942817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30715494420334086292723381 2879577601906320589942817)
                  ·
                    refine ⟨2159683201429740442457113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2879577601906320589942817 2159683201429740442457113)
                    ·
                      refine ⟨1619762401072305331842835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2159683201429740442457113 1619762401072305331842835)
                      ·
                        rfl

theorem cell23_3154476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 2, 2].length) (baseStart_3154476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154476 prefixEnd_3154476 := by exact prefixLift 3154476
  have htrace : WordTrace (prefixWord ++ tailWord_3154476) baseStart_3154476 baseEnd_3154476 := by
    simpa [prefixWord, tailWord_3154476, baseEnd_3154476] using wordTrace_append hprefix tailTrace_3154476
  have hstable : (prefixWord ++ tailWord_3154476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154476).length < 2 ^ (prefixWord ++ tailWord_3154476).sum := by decide
  have hdescent : baseEnd_3154476 < baseStart_3154476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154482 : List Nat := [3, 2, 1, 1, 2, 1, 13]
def baseStart_3154482 : Nat := 118140960795 + 3154482 * 2 ^ 59
def prefixEnd_3154482 : Nat := 4983230072969 + 3 ^ 40 * 3154482 * 2
def baseEnd_3154482 : Nat := 19997104715509040844047

theorem tailTrace_3154482 : CollatzResearch.WordTrace tailWord_3154482 prefixEnd_3154482 19997104715509040844047 := by
  unfold tailWord_3154482
  simp only [CollatzResearch.WordTrace]
  refine ⟨28763352639464482869804425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76702273705238620986145133 28763352639464482869804425)
  ·
    refine ⟨21572514479598362152353319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28763352639464482869804425 21572514479598362152353319)
    ·
      refine ⟨32358771719397543228529979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21572514479598362152353319 32358771719397543228529979)
      ·
        refine ⟨48538157579096314842794969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32358771719397543228529979 48538157579096314842794969)
        ·
          refine ⟨36403618184322236132096227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48538157579096314842794969 36403618184322236132096227)
          ·
            refine ⟨54605427276483354198144341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36403618184322236132096227 54605427276483354198144341)
            ·
              refine ⟨19997104715509040844047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 54605427276483354198144341 19997104715509040844047)
              ·
                rfl

theorem cell23_3154482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 13].length) (baseStart_3154482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154482 prefixEnd_3154482 := by exact prefixLift 3154482
  have htrace : WordTrace (prefixWord ++ tailWord_3154482) baseStart_3154482 baseEnd_3154482 := by
    simpa [prefixWord, tailWord_3154482, baseEnd_3154482] using wordTrace_append hprefix tailTrace_3154482
  have hstable : (prefixWord ++ tailWord_3154482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154482).length < 2 ^ (prefixWord ++ tailWord_3154482).sum := by decide
  have hdescent : baseEnd_3154482 < baseStart_3154482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154503 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 2, 4]
def baseStart_3154503 : Nat := 118140960795 + 3154503 * 2 ^ 59
def prefixEnd_3154503 : Nat := 4983230072969 + 3 ^ 40 * 3154503 * 2
def baseEnd_3154503 : Nat := 539925421683325575401737

theorem tailTrace_3154503 : CollatzResearch.WordTrace tailWord_3154503 prefixEnd_3154503 539925421683325575401737 := by
  unfold tailWord_3154503
  simp only [CollatzResearch.WordTrace]
  refine ⟨115054176490781852065732163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76702784327187901377154775 115054176490781852065732163)
  ·
    refine ⟨172581264736172778098598245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115054176490781852065732163 172581264736172778098598245)
    ·
      refine ⟨32358987138032395893487171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172581264736172778098598245 32358987138032395893487171)
      ·
        refine ⟨48538480707048593840230757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32358987138032395893487171 48538480707048593840230757)
        ·
          refine ⟨9100965132571611345043267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48538480707048593840230757 9100965132571611345043267)
          ·
            refine ⟨13651447698857417017564901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9100965132571611345043267 13651447698857417017564901)
            ·
              refine ⟨2559646443535765690793419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13651447698857417017564901 2559646443535765690793419)
              ·
                refine ⟨3839469665303648536190129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2559646443535765690793419 3839469665303648536190129)
                ·
                  refine ⟨2879602248977736402142597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839469665303648536190129 2879602248977736402142597)
                  ·
                    refine ⟨539925421683325575401737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2879602248977736402142597 539925421683325575401737)
                    ·
                      rfl

theorem cell23_3154503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_3154503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154503 prefixEnd_3154503 := by exact prefixLift 3154503
  have htrace : WordTrace (prefixWord ++ tailWord_3154503) baseStart_3154503 baseEnd_3154503 := by
    simpa [prefixWord, tailWord_3154503, baseEnd_3154503] using wordTrace_append hprefix tailTrace_3154503
  have hstable : (prefixWord ++ tailWord_3154503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154503).length < 2 ^ (prefixWord ++ tailWord_3154503).sum := by decide
  have hdescent : baseEnd_3154503 < baseStart_3154503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154512 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 4, 7]
def baseStart_3154512 : Nat := 118140960795 + 3154512 * 2 ^ 59
def prefixEnd_3154512 : Nat := 4983230072969 + 3 ^ 40 * 3154512 * 2
def baseEnd_3154512 : Nat := 539926962125289063664223

theorem tailTrace_3154512 : CollatzResearch.WordTrace tailWord_3154512 prefixEnd_3154512 539926962125289063664223 := by
  unfold tailWord_3154512
  simp only [CollatzResearch.WordTrace]
  refine ⟨57527252373874623301404895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76703003165166164401873193 57527252373874623301404895)
  ·
    refine ⟨86290878560811934952107343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57527252373874623301404895 86290878560811934952107343)
    ·
      refine ⟨129436317841217902428161015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86290878560811934952107343 129436317841217902428161015)
      ·
        refine ⟨194154476761826853642241523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129436317841217902428161015 194154476761826853642241523)
        ·
          refine ⟨291231715142740280463362285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194154476761826853642241523 291231715142740280463362285)
          ·
            refine ⟨109211893178527605173760857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291231715142740280463362285 109211893178527605173760857)
            ·
              refine ⟨81908919883895703880320643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109211893178527605173760857 81908919883895703880320643)
              ·
                refine ⟨122863379825843555820480965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81908919883895703880320643 122863379825843555820480965)
                ·
                  refine ⟨23036883717345666716340181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122863379825843555820480965 23036883717345666716340181)
                  ·
                    refine ⟨539926962125289063664223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23036883717345666716340181 539926962125289063664223)
                    ·
                      rfl

theorem cell23_3154512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_3154512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154512 prefixEnd_3154512 := by exact prefixLift 3154512
  have htrace : WordTrace (prefixWord ++ tailWord_3154512) baseStart_3154512 baseEnd_3154512 := by
    simpa [prefixWord, tailWord_3154512, baseEnd_3154512] using wordTrace_append hprefix tailTrace_3154512
  have hstable : (prefixWord ++ tailWord_3154512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154512).length < 2 ^ (prefixWord ++ tailWord_3154512).sum := by decide
  have hdescent : baseEnd_3154512 < baseStart_3154512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154513 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 1, 2, 3]
def baseStart_3154513 : Nat := 118140960795 + 3154513 * 2 ^ 59
def prefixEnd_3154513 : Nat := 4983230072969 + 3 ^ 40 * 3154513 * 2
def baseEnd_3154513 : Nat := 1619781399856521687080165

theorem tailTrace_3154513 : CollatzResearch.WordTrace tailWord_3154513 prefixEnd_3154513 1619781399856521687080165 := by
  unfold tailWord_3154513
  simp only [CollatzResearch.WordTrace]
  refine ⟨115054541220745623773596193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76703027480497082515730795 115054541220745623773596193)
  ·
    refine ⟨86290905915559217830197145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115054541220745623773596193 86290905915559217830197145)
    ·
      refine ⟨64718179436669413372647859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86290905915559217830197145 64718179436669413372647859)
      ·
        refine ⟨97077269155004120058971789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64718179436669413372647859 97077269155004120058971789)
        ·
          refine ⟨36403975933126545022114421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97077269155004120058971789 36403975933126545022114421)
          ·
            refine ⟨3412872743730613595823227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36403975933126545022114421 3412872743730613595823227)
            ·
              refine ⟨5119309115595920393734841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412872743730613595823227 5119309115595920393734841)
              ·
                refine ⟨3839481836696940295301131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5119309115595920393734841 3839481836696940295301131)
                ·
                  refine ⟨5759222755045410442951697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3839481836696940295301131 5759222755045410442951697)
                  ·
                    refine ⟨4319417066284057832213773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5759222755045410442951697 4319417066284057832213773)
                    ·
                      refine ⟨1619781399856521687080165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4319417066284057832213773 1619781399856521687080165)
                      ·
                        rfl

theorem cell23_3154513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_3154513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154513 prefixEnd_3154513 := by exact prefixLift 3154513
  have htrace : WordTrace (prefixWord ++ tailWord_3154513) baseStart_3154513 baseEnd_3154513 := by
    simpa [prefixWord, tailWord_3154513, baseEnd_3154513] using wordTrace_append hprefix tailTrace_3154513
  have hstable : (prefixWord ++ tailWord_3154513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154513).length < 2 ^ (prefixWord ++ tailWord_3154513).sum := by decide
  have hdescent : baseEnd_3154513 < baseStart_3154513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154530 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3154530 : Nat := 118140960795 + 3154530 * 2 ^ 59
def prefixEnd_3154530 : Nat := 4983230072969 + 3 ^ 40 * 3154530 * 2
def baseEnd_3154530 : Nat := 1619790129027648120567587

theorem tailTrace_3154530 : CollatzResearch.WordTrace tailWord_3154530 prefixEnd_3154530 1619790129027648120567587 := by
  unfold tailWord_3154530
  simp only [CollatzResearch.WordTrace]
  refine ⟨28763790315421008919241261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76703440841122690451310029 28763790315421008919241261)
  ·
    refine ⟨10786421368282878344715473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28763790315421008919241261 10786421368282878344715473)
    ·
      refine ⟨8089816026212158758536605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10786421368282878344715473 8089816026212158758536605)
      ·
        refine ⟨3033681009829559534451227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8089816026212158758536605 3033681009829559534451227)
        ·
          refine ⟨4550521514744339301676841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033681009829559534451227 4550521514744339301676841)
          ·
            refine ⟨3412891136058254476257631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4550521514744339301676841 3412891136058254476257631)
            ·
              refine ⟨5119336704087381714386447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412891136058254476257631 5119336704087381714386447)
              ·
                refine ⟨7679005056131072571579671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5119336704087381714386447 7679005056131072571579671)
                ·
                  refine ⟨11518507584196608857369507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7679005056131072571579671 11518507584196608857369507)
                  ·
                    refine ⟨17277761376294913286054261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11518507584196608857369507 17277761376294913286054261)
                    ·
                      refine ⟨1619790129027648120567587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17277761376294913286054261 1619790129027648120567587)
                      ·
                        rfl

theorem cell23_3154530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3154530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154530 prefixEnd_3154530 := by exact prefixLift 3154530
  have htrace : WordTrace (prefixWord ++ tailWord_3154530) baseStart_3154530 baseEnd_3154530 := by
    simpa [prefixWord, tailWord_3154530, baseEnd_3154530] using wordTrace_append hprefix tailTrace_3154530
  have hstable : (prefixWord ++ tailWord_3154530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154530).length < 2 ^ (prefixWord ++ tailWord_3154530).sum := by decide
  have hdescent : baseEnd_3154530 < baseStart_3154530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154544 : List Nat := [2, 1, 1, 1, 7, 2, 2, 2, 1, 2, 2]
def baseStart_3154544 : Nat := 118140960795 + 3154544 * 2 ^ 59
def prefixEnd_3154544 : Nat := 4983230072969 + 3 ^ 40 * 3154544 * 2
def baseEnd_3154544 : Nat := 1619797317756811065792523

theorem tailTrace_3154544 : CollatzResearch.WordTrace tailWord_3154544 prefixEnd_3154544 1619797317756811065792523 := by
  unfold tailWord_3154544
  simp only [CollatzResearch.WordTrace]
  refine ⟨57527835941816658033987343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76703781255755544045316457 57527835941816658033987343)
  ·
    refine ⟨86291753912724987050981015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57527835941816658033987343 86291753912724987050981015)
    ·
      refine ⟨129437630869087480576471523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86291753912724987050981015 129437630869087480576471523)
      ·
        refine ⟨194156446303631220864707285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129437630869087480576471523 194156446303631220864707285)
        ·
          refine ⟨4550541710241356739016577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 194156446303631220864707285 4550541710241356739016577)
          ·
            refine ⟨3412906282681017554262433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4550541710241356739016577 3412906282681017554262433)
            ·
              refine ⟨2559679712010763165696825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3412906282681017554262433 2559679712010763165696825)
              ·
                refine ⟨1919759784008072374272619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559679712010763165696825 1919759784008072374272619)
                ·
                  refine ⟨2879639676012108561408929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919759784008072374272619 2879639676012108561408929)
                  ·
                    refine ⟨2159729757009081421056697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2879639676012108561408929 2159729757009081421056697)
                    ·
                      refine ⟨1619797317756811065792523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2159729757009081421056697 1619797317756811065792523)
                      ·
                        rfl

theorem cell23_3154544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 1, 2, 2].length) (baseStart_3154544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154544 prefixEnd_3154544 := by exact prefixLift 3154544
  have htrace : WordTrace (prefixWord ++ tailWord_3154544) baseStart_3154544 baseEnd_3154544 := by
    simpa [prefixWord, tailWord_3154544, baseEnd_3154544] using wordTrace_append hprefix tailTrace_3154544
  have hstable : (prefixWord ++ tailWord_3154544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154544).length < 2 ^ (prefixWord ++ tailWord_3154544).sum := by decide
  have hdescent : baseEnd_3154544 < baseStart_3154544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154569 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 4, 4, 3]
def baseStart_3154569 : Nat := 118140960795 + 3154569 * 2 ^ 59
def prefixEnd_3154569 : Nat := 4983230072969 + 3 ^ 40 * 3154569 * 2
def baseEnd_3154569 : Nat := 1619810154773173467979907

theorem tailTrace_3154569 : CollatzResearch.WordTrace tailWord_3154569 prefixEnd_3154569 1619810154773173467979907 := by
  unfold tailWord_3154569
  simp only [CollatzResearch.WordTrace]
  refine ⟨115056583708542745337634761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76704389139028496891756507 115056583708542745337634761)
  ·
    refine ⟨86292437781407059003226071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115056583708542745337634761 86292437781407059003226071)
    ·
      refine ⟨129438656672110588504839107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86292437781407059003226071 129438656672110588504839107)
      ·
        refine ⟨194157985008165882757258661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129438656672110588504839107 194157985008165882757258661)
        ·
          refine ⟨36404622189031103016985999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194157985008165882757258661 36404622189031103016985999)
          ·
            refine ⟨54606933283546654525478999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36404622189031103016985999 54606933283546654525478999)
            ·
              refine ⟨81910399925319981788218499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54606933283546654525478999 81910399925319981788218499)
              ·
                refine ⟨122865599887979972682327749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81910399925319981788218499 122865599887979972682327749)
                ·
                  refine ⟨23037299978996244877936453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122865599887979972682327749 23037299978996244877936453)
                  ·
                    refine ⟨4319493746061795914613085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23037299978996244877936453 4319493746061795914613085)
                    ·
                      refine ⟨1619810154773173467979907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4319493746061795914613085 1619810154773173467979907)
                      ·
                        rfl

theorem cell23_3154569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 4, 3].length) (baseStart_3154569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154569 prefixEnd_3154569 := by exact prefixLift 3154569
  have htrace : WordTrace (prefixWord ++ tailWord_3154569) baseStart_3154569 baseEnd_3154569 := by
    simpa [prefixWord, tailWord_3154569, baseEnd_3154569] using wordTrace_append hprefix tailTrace_3154569
  have hstable : (prefixWord ++ tailWord_3154569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154569).length < 2 ^ (prefixWord ++ tailWord_3154569).sum := by decide
  have hdescent : baseEnd_3154569 < baseStart_3154569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154583 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 4, 2, 2]
def baseStart_3154583 : Nat := 118140960795 + 3154583 * 2 ^ 59
def prefixEnd_3154583 : Nat := 4983230072969 + 3 ^ 40 * 3154583 * 2
def baseEnd_3154583 : Nat := 1619817343502336413204843

theorem tailTrace_3154583 : CollatzResearch.WordTrace tailWord_3154583 prefixEnd_3154583 1619817343502336413204843 := by
  unfold tailWord_3154583
  simp only [CollatzResearch.WordTrace]
  refine ⟨115057094330492025728644403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76704729553661350485762935 115057094330492025728644403)
  ·
    refine ⟨172585641495738038592966605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115057094330492025728644403 172585641495738038592966605)
    ·
      refine ⟨64719615560901764472362477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172585641495738038592966605 64719615560901764472362477)
      ·
        refine ⟨24269855835338161677135929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64719615560901764472362477 24269855835338161677135929)
        ·
          refine ⟨18202391876503621257851947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24269855835338161677135929 18202391876503621257851947)
          ·
            refine ⟨27303587814755431886777921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18202391876503621257851947 27303587814755431886777921)
            ·
              refine ⟨20477690861066573915083441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27303587814755431886777921 20477690861066573915083441)
              ·
                refine ⟨15358268145799930436312581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20477690861066573915083441 15358268145799930436312581)
                ·
                  refine ⟨2879675277337486956808609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15358268145799930436312581 2879675277337486956808609)
                  ·
                    refine ⟨2159756458003115217606457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2879675277337486956808609 2159756458003115217606457)
                    ·
                      refine ⟨1619817343502336413204843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2159756458003115217606457 1619817343502336413204843)
                      ·
                        rfl

theorem cell23_3154583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_3154583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154583 prefixEnd_3154583 := by exact prefixLift 3154583
  have htrace : WordTrace (prefixWord ++ tailWord_3154583) baseStart_3154583 baseEnd_3154583 := by
    simpa [prefixWord, tailWord_3154583, baseEnd_3154583] using wordTrace_append hprefix tailTrace_3154583
  have hstable : (prefixWord ++ tailWord_3154583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154583).length < 2 ^ (prefixWord ++ tailWord_3154583).sum := by decide
  have hdescent : baseEnd_3154583 < baseStart_3154583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154636 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_3154636 : Nat := 118140960795 + 3154636 * 2 ^ 59
def prefixEnd_3154636 : Nat := 4983230072969 + 3 ^ 40 * 3154636 * 2
def baseEnd_3154636 : Nat := 539948185992341568614033

theorem tailTrace_3154636 : CollatzResearch.WordTrace tailWord_3154636 prefixEnd_3154636 539948185992341568614033 := by
  unfold tailWord_3154636
  simp only [CollatzResearch.WordTrace]
  refine ⟨57529513699650007890161881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76706018266200010520215841 57529513699650007890161881)
  ·
    refine ⟨43147135274737505917621411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57529513699650007890161881 43147135274737505917621411)
    ·
      refine ⟨64720702912106258876432117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43147135274737505917621411 64720702912106258876432117)
      ·
        refine ⟨6067565898009961769665511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64720702912106258876432117 6067565898009961769665511)
        ·
          refine ⟨9101348847014942654498267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6067565898009961769665511 9101348847014942654498267)
          ·
            refine ⟨13652023270522413981747401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9101348847014942654498267 13652023270522413981747401)
            ·
              refine ⟨10239017452891810486310551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13652023270522413981747401 10239017452891810486310551)
              ·
                refine ⟨15358526179337715729465827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10239017452891810486310551 15358526179337715729465827)
                ·
                  refine ⟨23037789269006573594198741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15358526179337715729465827 23037789269006573594198741)
                  ·
                    refine ⟨539948185992341568614033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23037789269006573594198741 539948185992341568614033)
                    ·
                      rfl

theorem cell23_3154636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_3154636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154636 prefixEnd_3154636 := by exact prefixLift 3154636
  have htrace : WordTrace (prefixWord ++ tailWord_3154636) baseStart_3154636 baseEnd_3154636 := by
    simpa [prefixWord, tailWord_3154636, baseEnd_3154636] using wordTrace_append hprefix tailTrace_3154636
  have hstable : (prefixWord ++ tailWord_3154636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154636).length < 2 ^ (prefixWord ++ tailWord_3154636).sum := by decide
  have hdescent : baseEnd_3154636 < baseStart_3154636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154690 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3154690 : Nat := 118140960795 + 3154690 * 2 ^ 59
def prefixEnd_3154690 : Nat := 4983230072969 + 3 ^ 40 * 3154690 * 2
def baseEnd_3154690 : Nat := 1619872285932367494566851

theorem tailTrace_3154690 : CollatzResearch.WordTrace tailWord_3154690 prefixEnd_3154690 1619872285932367494566851 := by
  unfold tailWord_3154690
  simp only [CollatzResearch.WordTrace]
  refine ⟨28765249235276095750697381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76707331294069588668526349 28765249235276095750697381)
  ·
    refine ⟨5393484231614267953255759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28765249235276095750697381 5393484231614267953255759)
    ·
      refine ⟨8090226347421401929883639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5393484231614267953255759 8090226347421401929883639)
      ·
        refine ⟨12135339521132102894825459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8090226347421401929883639 12135339521132102894825459)
        ·
          refine ⟨18203009281698154342238189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12135339521132102894825459 18203009281698154342238189)
          ·
            refine ⟨6826128480636807878339321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18203009281698154342238189 6826128480636807878339321)
            ·
              refine ⟨5119596360477605908754491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6826128480636807878339321 5119596360477605908754491)
              ·
                refine ⟨7679394540716408863131737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5119596360477605908754491 7679394540716408863131737)
                ·
                  refine ⟨5759545905537306647348803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7679394540716408863131737 5759545905537306647348803)
                  ·
                    refine ⟨8639318858305959971023205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5759545905537306647348803 8639318858305959971023205)
                    ·
                      refine ⟨1619872285932367494566851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8639318858305959971023205 1619872285932367494566851)
                      ·
                        rfl

theorem cell23_3154690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3154690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154690 prefixEnd_3154690 := by exact prefixLift 3154690
  have htrace : WordTrace (prefixWord ++ tailWord_3154690) baseStart_3154690 baseEnd_3154690 := by
    simpa [prefixWord, tailWord_3154690, baseEnd_3154690] using wordTrace_append hprefix tailTrace_3154690
  have hstable : (prefixWord ++ tailWord_3154690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154690).length < 2 ^ (prefixWord ++ tailWord_3154690).sum := by decide
  have hdescent : baseEnd_3154690 < baseStart_3154690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154699 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 8]
def baseStart_3154699 : Nat := 118140960795 + 3154699 * 2 ^ 59
def prefixEnd_3154699 : Nat := 4983230072969 + 3 ^ 40 * 3154699 * 2
def baseEnd_3154699 : Nat := 1619876907258257959354309

theorem tailTrace_3154699 : CollatzResearch.WordTrace tailWord_3154699 prefixEnd_3154699 1619876907258257959354309 := by
  unfold tailWord_3154699
  simp only [CollatzResearch.WordTrace]
  refine ⟨115061325198071777539867151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76707550132047851693244767 115061325198071777539867151)
  ·
    refine ⟨172591987797107666309800727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115061325198071777539867151 172591987797107666309800727)
    ·
      refine ⟨258887981695661499464701091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172591987797107666309800727 258887981695661499464701091)
      ·
        refine ⟨388331972543492249197051637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258887981695661499464701091 388331972543492249197051637)
        ·
          refine ⟨36406122425952398362223591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 388331972543492249197051637 36406122425952398362223591)
          ·
            refine ⟨54609183638928597543335387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36406122425952398362223591 54609183638928597543335387)
            ·
              refine ⟨81913775458392896315003081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54609183638928597543335387 81913775458392896315003081)
              ·
                refine ⟨61435331593794672236252311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81913775458392896315003081 61435331593794672236252311)
                ·
                  refine ⟨92152997390692008354378467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61435331593794672236252311 92152997390692008354378467)
                  ·
                    refine ⟨138229496086038012531567701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92152997390692008354378467 138229496086038012531567701)
                    ·
                      refine ⟨1619876907258257959354309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 138229496086038012531567701 1619876907258257959354309)
                      ·
                        rfl

theorem cell23_3154699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_3154699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154699 prefixEnd_3154699 := by exact prefixLift 3154699
  have htrace : WordTrace (prefixWord ++ tailWord_3154699) baseStart_3154699 baseEnd_3154699 := by
    simpa [prefixWord, tailWord_3154699, baseEnd_3154699] using wordTrace_append hprefix tailTrace_3154699
  have hstable : (prefixWord ++ tailWord_3154699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154699).length < 2 ^ (prefixWord ++ tailWord_3154699).sum := by decide
  have hdescent : baseEnd_3154699 < baseStart_3154699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154723 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 3, 1, 3]
def baseStart_3154723 : Nat := 118140960795 + 3154723 * 2 ^ 59
def prefixEnd_3154723 : Nat := 4983230072969 + 3 ^ 40 * 3154723 * 2
def baseEnd_3154723 : Nat := 1619889230793965865454199

theorem tailTrace_3154723 : CollatzResearch.WordTrace tailWord_3154723 prefixEnd_3154723 1619889230793965865454199 := by
  unfold tailWord_3154723
  simp only [CollatzResearch.WordTrace]
  refine ⟨115062200549984829638740823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76708133699989886425827215 115062200549984829638740823)
  ·
    refine ⟨172593300824977244458111235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115062200549984829638740823 172593300824977244458111235)
    ·
      refine ⟨258889951237465866687166853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172593300824977244458111235 258889951237465866687166853)
      ·
        refine ⟨48541865857024850003843785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258889951237465866687166853 48541865857024850003843785)
        ·
          refine ⟨36406399392768637502882839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48541865857024850003843785 36406399392768637502882839)
          ·
            refine ⟨54609599089152956254324259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36406399392768637502882839 54609599089152956254324259)
            ·
              refine ⟨81914398633729434381486389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54609599089152956254324259 81914398633729434381486389)
              ·
                refine ⟨7679474871912134473264349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81914398633729434381486389 7679474871912134473264349)
                ·
                  refine ⟨2879803076967050427474131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7679474871912134473264349 2879803076967050427474131)
                  ·
                    refine ⟨4319704615450575641211197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2879803076967050427474131 4319704615450575641211197)
                    ·
                      refine ⟨1619889230793965865454199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4319704615450575641211197 1619889230793965865454199)
                      ·
                        rfl

theorem cell23_3154723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_3154723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154723 prefixEnd_3154723 := by exact prefixLift 3154723
  have htrace : WordTrace (prefixWord ++ tailWord_3154723) baseStart_3154723 baseEnd_3154723 := by
    simpa [prefixWord, tailWord_3154723, baseEnd_3154723] using wordTrace_append hprefix tailTrace_3154723
  have hstable : (prefixWord ++ tailWord_3154723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154723).length < 2 ^ (prefixWord ++ tailWord_3154723).sum := by decide
  have hdescent : baseEnd_3154723 < baseStart_3154723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154766 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_3154766 : Nat := 118140960795 + 3154766 * 2 ^ 59
def prefixEnd_3154766 : Nat := 4983230072969 + 3 ^ 40 * 3154766 * 2
def baseEnd_3154766 : Nat := 1619911310462109197216501

theorem tailTrace_3154766 : CollatzResearch.WordTrace tailWord_3154766 prefixEnd_3154766 1619911310462109197216501 := by
  unfold tailWord_3154766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14382971111103630997819519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76709179259219365321704101 14382971111103630997819519)
  ·
    refine ⟨21574456666655446496729279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14382971111103630997819519 21574456666655446496729279)
    ·
      refine ⟨32361684999983169745093919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21574456666655446496729279 32361684999983169745093919)
      ·
        refine ⟨48542527499974754617640879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32361684999983169745093919 48542527499974754617640879)
        ·
          refine ⟨72813791249962131926461319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48542527499974754617640879 72813791249962131926461319)
          ·
            refine ⟨109220686874943197889691979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72813791249962131926461319 109220686874943197889691979)
            ·
              refine ⟨163831030312414796834537969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109220686874943197889691979 163831030312414796834537969)
              ·
                refine ⟨122873272734311097625903477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163831030312414796834537969 122873272734311097625903477)
                ·
                  refine ⟨11519369318841665402428451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122873272734311097625903477 11519369318841665402428451)
                  ·
                    refine ⟨17279053978262498103642677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11519369318841665402428451 17279053978262498103642677)
                    ·
                      refine ⟨1619911310462109197216501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17279053978262498103642677 1619911310462109197216501)
                      ·
                        rfl

theorem cell23_3154766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_3154766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154766 prefixEnd_3154766 := by exact prefixLift 3154766
  have htrace : WordTrace (prefixWord ++ tailWord_3154766) baseStart_3154766 baseEnd_3154766 := by
    simpa [prefixWord, tailWord_3154766, baseEnd_3154766] using wordTrace_append hprefix tailTrace_3154766
  have hstable : (prefixWord ++ tailWord_3154766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154766).length < 2 ^ (prefixWord ++ tailWord_3154766).sum := by decide
  have hdescent : baseEnd_3154766 < baseStart_3154766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154773 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 4, 4]
def baseStart_3154773 : Nat := 118140960795 + 3154773 * 2 ^ 59
def prefixEnd_3154773 : Nat := 4983230072969 + 3 ^ 40 * 3154773 * 2
def baseEnd_3154773 : Nat := 539971634942230223276323

theorem tailTrace_3154773 : CollatzResearch.WordTrace tailWord_3154773 prefixEnd_3154773 539971634942230223276323 := by
  unfold tailWord_3154773
  simp only [CollatzResearch.WordTrace]
  refine ⟨115064024199803688178060973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76709349466535792118707315 115064024199803688178060973)
  ·
    refine ⟨43149009074926383066772865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115064024199803688178060973 43149009074926383066772865)
    ·
      refine ⟨32361756806194787300079649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43149009074926383066772865 32361756806194787300079649)
      ·
        refine ⟨24271317604646090475059737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32361756806194787300079649 24271317604646090475059737)
        ·
          refine ⟨18203488203484567856294803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24271317604646090475059737 18203488203484567856294803)
          ·
            refine ⟨27305232305226851784442205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18203488203484567856294803 27305232305226851784442205)
            ·
              refine ⟨10239462114460069419165827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27305232305226851784442205 10239462114460069419165827)
              ·
                refine ⟨15359193171690104128748741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10239462114460069419165827 15359193171690104128748741)
                ·
                  refine ⟨2879848719691894524140389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15359193171690104128748741 2879848719691894524140389)
                  ·
                    refine ⟨539971634942230223276323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2879848719691894524140389 539971634942230223276323)
                    ·
                      rfl

theorem cell23_3154773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_3154773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154773 prefixEnd_3154773 := by exact prefixLift 3154773
  have htrace : WordTrace (prefixWord ++ tailWord_3154773) baseStart_3154773 baseEnd_3154773 := by
    simpa [prefixWord, tailWord_3154773, baseEnd_3154773] using wordTrace_append hprefix tailTrace_3154773
  have hstable : (prefixWord ++ tailWord_3154773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154773).length < 2 ^ (prefixWord ++ tailWord_3154773).sum := by decide
  have hdescent : baseEnd_3154773 < baseStart_3154773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154776 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3154776 : Nat := 118140960795 + 3154776 * 2 ^ 59
def prefixEnd_3154776 : Nat := 4983230072969 + 3 ^ 40 * 3154776 * 2
def baseEnd_3154776 : Nat := 1619916445268654158091455

theorem tailTrace_3154776 : CollatzResearch.WordTrace tailWord_3154776 prefixEnd_3154776 1619916445268654158091455 := by
  unfold tailWord_3154776
  simp only [CollatzResearch.WordTrace]
  refine ⟨57532066809396409845210091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76709422412528546460280121 57532066809396409845210091)
  ·
    refine ⟨86298100214094614767815137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57532066809396409845210091 86298100214094614767815137)
    ·
      refine ⟨64723575160570961075861353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86298100214094614767815137 64723575160570961075861353)
      ·
        refine ⟨48542681370428220806896015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64723575160570961075861353 48542681370428220806896015)
        ·
          refine ⟨72814022055642331210344023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48542681370428220806896015 72814022055642331210344023)
          ·
            refine ⟨109221033083463496815516035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72814022055642331210344023 109221033083463496815516035)
            ·
              refine ⟨163831549625195245223274053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109221033083463496815516035 163831549625195245223274053)
              ·
                refine ⟨30718415554724108479363885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163831549625195245223274053 30718415554724108479363885)
                ·
                  refine ⟨11519405833021540679761457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30718415554724108479363885 11519405833021540679761457)
                  ·
                    refine ⟨8639554374766155509821093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11519405833021540679761457 8639554374766155509821093)
                    ·
                      refine ⟨1619916445268654158091455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8639554374766155509821093 1619916445268654158091455)
                      ·
                        rfl

theorem cell23_3154776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3154776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154776 prefixEnd_3154776 := by exact prefixLift 3154776
  have htrace : WordTrace (prefixWord ++ tailWord_3154776) baseStart_3154776 baseEnd_3154776 := by
    simpa [prefixWord, tailWord_3154776, baseEnd_3154776] using wordTrace_append hprefix tailTrace_3154776
  have hstable : (prefixWord ++ tailWord_3154776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154776).length < 2 ^ (prefixWord ++ tailWord_3154776).sum := by decide
  have hdescent : baseEnd_3154776 < baseStart_3154776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154813 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_3154813 : Nat := 118140960795 + 3154813 * 2 ^ 59
def prefixEnd_3154813 : Nat := 4983230072969 + 3 ^ 40 * 3154813 * 2
def baseEnd_3154813 : Nat := 1619935444052870513328785

theorem tailTrace_3154813 : CollatzResearch.WordTrace tailWord_3154813 prefixEnd_3154813 1619935444052870513328785 := by
  unfold tailWord_3154813
  simp only [CollatzResearch.WordTrace]
  refine ⟨115065483119658775009517093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76710322079772516673011395 115065483119658775009517093)
  ·
    refine ⟨21574778084936020314284455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115065483119658775009517093 21574778084936020314284455)
    ·
      refine ⟨32362167127404030471426683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21574778084936020314284455 32362167127404030471426683)
      ·
        refine ⟨48543250691106045707140025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32362167127404030471426683 48543250691106045707140025)
        ·
          refine ⟨36407438018329534280355019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48543250691106045707140025 36407438018329534280355019)
          ·
            refine ⟨54611157027494301420532529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36407438018329534280355019 54611157027494301420532529)
            ·
              refine ⟨40958367770620726065399397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54611157027494301420532529 40958367770620726065399397)
              ·
                refine ⟨7679693956991386137262387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40958367770620726065399397 7679693956991386137262387)
                ·
                  refine ⟨11519540935487079205893581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7679693956991386137262387 11519540935487079205893581)
                  ·
                    refine ⟨4319827850807654702210093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11519540935487079205893581 4319827850807654702210093)
                    ·
                      refine ⟨1619935444052870513328785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4319827850807654702210093 1619935444052870513328785)
                      ·
                        rfl

theorem cell23_3154813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_3154813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154813 prefixEnd_3154813 := by exact prefixLift 3154813
  have htrace : WordTrace (prefixWord ++ tailWord_3154813) baseStart_3154813 baseEnd_3154813 := by
    simpa [prefixWord, tailWord_3154813, baseEnd_3154813] using wordTrace_append hprefix tailTrace_3154813
  have hstable : (prefixWord ++ tailWord_3154813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154813).length < 2 ^ (prefixWord ++ tailWord_3154813).sum := by decide
  have hdescent : baseEnd_3154813 < baseStart_3154813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154847 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3154847 : Nat := 118140960795 + 3154847 * 2 ^ 59
def prefixEnd_3154847 : Nat := 4983230072969 + 3 ^ 40 * 3154847 * 2
def baseEnd_3154847 : Nat := 1619952902395123380303629

theorem tailTrace_3154847 : CollatzResearch.WordTrace tailWord_3154847 prefixEnd_3154847 1619952902395123380303629 := by
  unfold tailWord_3154847
  simp only [CollatzResearch.WordTrace]
  refine ⟨115066723201535598816254795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76711148801023732544169863 115066723201535598816254795)
  ·
    refine ⟨172600084802303398224382193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115066723201535598816254795 172600084802303398224382193)
    ·
      refine ⟨129450063601727548668286645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172600084802303398224382193 129450063601727548668286645)
      ·
        refine ⟨12135943462661957687651873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129450063601727548668286645 12135943462661957687651873)
        ·
          refine ⟨9101957596996468265738905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12135943462661957687651873 9101957596996468265738905)
          ·
            refine ⟨6826468197747351199304179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9101957596996468265738905 6826468197747351199304179)
            ·
              refine ⟨10239702296621026798956269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6826468197747351199304179 10239702296621026798956269)
              ·
                refine ⟨3839888361232885049608601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10239702296621026798956269 3839888361232885049608601)
                ·
                  refine ⟨2879916270924663787206451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839888361232885049608601 2879916270924663787206451)
                  ·
                    refine ⟨4319874406386995680809677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2879916270924663787206451 4319874406386995680809677)
                    ·
                      refine ⟨1619952902395123380303629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4319874406386995680809677 1619952902395123380303629)
                      ·
                        rfl

theorem cell23_3154847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3154847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154847 prefixEnd_3154847 := by exact prefixLift 3154847
  have htrace : WordTrace (prefixWord ++ tailWord_3154847) baseStart_3154847 baseEnd_3154847 := by
    simpa [prefixWord, tailWord_3154847, baseEnd_3154847] using wordTrace_append hprefix tailTrace_3154847
  have hstable : (prefixWord ++ tailWord_3154847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154847).length < 2 ^ (prefixWord ++ tailWord_3154847).sum := by decide
  have hdescent : baseEnd_3154847 < baseStart_3154847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154873 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3154873 : Nat := 118140960795 + 3154873 * 2 ^ 59
def prefixEnd_3154873 : Nat := 4983230072969 + 3 ^ 40 * 3154873 * 2
def baseEnd_3154873 : Nat := 1619966252892140278578509

theorem tailTrace_3154873 : CollatzResearch.WordTrace tailWord_3154873 prefixEnd_3154873 1619966252892140278578509 := by
  unfold tailWord_3154873
  simp only [CollatzResearch.WordTrace]
  refine ⟨115067671499441405256701273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76711780999627603504467515 115067671499441405256701273)
  ·
    refine ⟨86300753624581053942525955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115067671499441405256701273 86300753624581053942525955)
    ·
      refine ⟨129451130436871580913788933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86300753624581053942525955 129451130436871580913788933)
      ·
        refine ⟨24272086956913421421335425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129451130436871580913788933 24272086956913421421335425)
        ·
          refine ⟨18204065217685066066001569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24272086956913421421335425 18204065217685066066001569)
          ·
            refine ⟨13653048913263799549501177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18204065217685066066001569 13653048913263799549501177)
            ·
              refine ⟨10239786684947849662125883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13653048913263799549501177 10239786684947849662125883)
              ·
                refine ⟨15359680027421774493188825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10239786684947849662125883 15359680027421774493188825)
                ·
                  refine ⟨11519760020566330869891619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15359680027421774493188825 11519760020566330869891619)
                  ·
                    refine ⟨17279640030849496304837429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11519760020566330869891619 17279640030849496304837429)
                    ·
                      refine ⟨1619966252892140278578509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17279640030849496304837429 1619966252892140278578509)
                      ·
                        rfl

theorem cell23_3154873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3154873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154873 prefixEnd_3154873 := by exact prefixLift 3154873
  have htrace : WordTrace (prefixWord ++ tailWord_3154873) baseStart_3154873 baseEnd_3154873 := by
    simpa [prefixWord, tailWord_3154873, baseEnd_3154873] using wordTrace_append hprefix tailTrace_3154873
  have hstable : (prefixWord ++ tailWord_3154873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154873).length < 2 ^ (prefixWord ++ tailWord_3154873).sum := by decide
  have hdescent : baseEnd_3154873 < baseStart_3154873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154887 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 2, 2, 2]
def baseStart_3154887 : Nat := 118140960795 + 3154887 * 2 ^ 59
def prefixEnd_3154887 : Nat := 4983230072969 + 3 ^ 40 * 3154887 * 2
def baseEnd_3154887 : Nat := 1619973441621303223803445

theorem tailTrace_3154887 : CollatzResearch.WordTrace tailWord_3154887 prefixEnd_3154887 1619973441621303223803445 := by
  unfold tailWord_3154887
  simp only [CollatzResearch.WordTrace]
  refine ⟨115068182121390685647710915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76712121414260457098473943 115068182121390685647710915)
  ·
    refine ⟨172602273182086028471566373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115068182121390685647710915 172602273182086028471566373)
    ·
      refine ⟨32362926221641130338418695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172602273182086028471566373 32362926221641130338418695)
      ·
        refine ⟨48544389332461695507628043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32362926221641130338418695 48544389332461695507628043)
        ·
          refine ⟨72816583998692543261442065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48544389332461695507628043 72816583998692543261442065)
          ·
            refine ⟨54612437999019407446081549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72816583998692543261442065 54612437999019407446081549)
            ·
              refine ⟨20479664249632277792280581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54612437999019407446081549 20479664249632277792280581)
              ·
                refine ⟨3839937046806052086052609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20479664249632277792280581 3839937046806052086052609)
                ·
                  refine ⟨2879952785104539064539457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839937046806052086052609 2879952785104539064539457)
                  ·
                    refine ⟨2159964588828404298404593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2879952785104539064539457 2159964588828404298404593)
                    ·
                      refine ⟨1619973441621303223803445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2159964588828404298404593 1619973441621303223803445)
                      ·
                        rfl

theorem cell23_3154887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_3154887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154887 prefixEnd_3154887 := by exact prefixLift 3154887
  have htrace : WordTrace (prefixWord ++ tailWord_3154887) baseStart_3154887 baseEnd_3154887 := by
    simpa [prefixWord, tailWord_3154887, baseEnd_3154887] using wordTrace_append hprefix tailTrace_3154887
  have hstable : (prefixWord ++ tailWord_3154887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154887).length < 2 ^ (prefixWord ++ tailWord_3154887).sum := by decide
  have hdescent : baseEnd_3154887 < baseStart_3154887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154896 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_3154896 : Nat := 118140960795 + 3154896 * 2 ^ 59
def prefixEnd_3154896 : Nat := 4983230072969 + 3 ^ 40 * 3154896 * 2
def baseEnd_3154896 : Nat := 1619978062947193688590903

theorem tailTrace_3154896 : CollatzResearch.WordTrace tailWord_3154896 prefixEnd_3154896 1619978062947193688590903 := by
  unfold tailWord_3154896
  simp only [CollatzResearch.WordTrace]
  refine ⟨57534255189179040092394271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76712340252238720123192361 57534255189179040092394271)
  ·
    refine ⟨86301382783768560138591407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57534255189179040092394271 86301382783768560138591407)
    ·
      refine ⟨129452074175652840207887111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86301382783768560138591407 129452074175652840207887111)
      ·
        refine ⟨194178111263479260311830667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129452074175652840207887111 194178111263479260311830667)
        ·
          refine ⟨291267166895218890467746001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194178111263479260311830667 291267166895218890467746001)
          ·
            refine ⟨218450375171414167850809501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291267166895218890467746001 218450375171414167850809501)
            ·
              refine ⟨81918890689280312944053563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218450375171414167850809501 81918890689280312944053563)
              ·
                refine ⟨122878336033920469416080345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81918890689280312944053563 122878336033920469416080345)
                ·
                  refine ⟨92158752025440352062060259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122878336033920469416080345 92158752025440352062060259)
                  ·
                    refine ⟨138238128038160528093090389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92158752025440352062060259 138238128038160528093090389)
                    ·
                      refine ⟨1619978062947193688590903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 138238128038160528093090389 1619978062947193688590903)
                      ·
                        rfl

theorem cell23_3154896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_3154896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154896 prefixEnd_3154896 := by exact prefixLift 3154896
  have htrace : WordTrace (prefixWord ++ tailWord_3154896) baseStart_3154896 baseEnd_3154896 := by
    simpa [prefixWord, tailWord_3154896, baseEnd_3154896] using wordTrace_append hprefix tailTrace_3154896
  have hstable : (prefixWord ++ tailWord_3154896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154896).length < 2 ^ (prefixWord ++ tailWord_3154896).sum := by decide
  have hdescent : baseEnd_3154896 < baseStart_3154896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154900 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3154900 : Nat := 118140960795 + 3154900 * 2 ^ 59
def prefixEnd_3154900 : Nat := 4983230072969 + 3 ^ 40 * 3154900 * 2
def baseEnd_3154900 : Nat := 1619980116869811672940885

theorem tailTrace_3154900 : CollatzResearch.WordTrace tailWord_3154900 prefixEnd_3154900 1619980116869811672940885 := by
  unfold tailWord_3154900
  simp only [CollatzResearch.WordTrace]
  refine ⟨57534328135171794433967077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76712437513562392578622769 57534328135171794433967077)
  ·
    refine ⟨10787686525344711456368827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57534328135171794433967077 10787686525344711456368827)
    ·
      refine ⟨16181529788017067184553241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10787686525344711456368827 16181529788017067184553241)
      ·
        refine ⟨12136147341012800388414931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16181529788017067184553241 12136147341012800388414931)
        ·
          refine ⟨18204221011519200582622397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12136147341012800388414931 18204221011519200582622397)
          ·
            refine ⟨6826582879319700218483399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18204221011519200582622397 6826582879319700218483399)
            ·
              refine ⟨10239874318979550327725099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6826582879319700218483399 10239874318979550327725099)
              ·
                refine ⟨15359811478469325491587649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10239874318979550327725099 15359811478469325491587649)
                ·
                  refine ⟨11519858608851994118690737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15359811478469325491587649 11519858608851994118690737)
                  ·
                    refine ⟨8639893956638995589018053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11519858608851994118690737 8639893956638995589018053)
                    ·
                      refine ⟨1619980116869811672940885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8639893956638995589018053 1619980116869811672940885)
                      ·
                        rfl

theorem cell23_3154900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3154900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154900 prefixEnd_3154900 := by exact prefixLift 3154900
  have htrace : WordTrace (prefixWord ++ tailWord_3154900) baseStart_3154900 baseEnd_3154900 := by
    simpa [prefixWord, tailWord_3154900, baseEnd_3154900] using wordTrace_append hprefix tailTrace_3154900
  have hstable : (prefixWord ++ tailWord_3154900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154900).length < 2 ^ (prefixWord ++ tailWord_3154900).sum := by decide
  have hdescent : baseEnd_3154900 < baseStart_3154900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154932 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3154932 : Nat := 118140960795 + 3154932 * 2 ^ 59
def prefixEnd_3154932 : Nat := 4983230072969 + 3 ^ 40 * 3154932 * 2
def baseEnd_3154932 : Nat := 1619996548250755547740739

theorem tailTrace_3154932 : CollatzResearch.WordTrace tailWord_3154932 prefixEnd_3154932 1619996548250755547740739 := by
  unfold tailWord_3154932
  simp only [CollatzResearch.WordTrace]
  refine ⟨57534911703113829166549525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76713215604151772222066033 57534911703113829166549525)
  ·
    refine ⟨2696948986083460742182009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57534911703113829166549525 2696948986083460742182009)
    ·
      refine ⟨2022711739562595556636507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2696948986083460742182009 2022711739562595556636507)
      ·
        refine ⟨3034067609343893334954761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2022711739562595556636507 3034067609343893334954761)
        ·
          refine ⟨2275550707007920001216071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3034067609343893334954761 2275550707007920001216071)
          ·
            refine ⟨3413326060511880001824107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275550707007920001216071 3413326060511880001824107)
            ·
              refine ⟨5119989090767820002736161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3413326060511880001824107 5119989090767820002736161)
              ·
                refine ⟨3839991818075865002052121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5119989090767820002736161 3839991818075865002052121)
                ·
                  refine ⟨2879993863556898751539091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839991818075865002052121 2879993863556898751539091)
                  ·
                    refine ⟨4319990795335348127308637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2879993863556898751539091 4319990795335348127308637)
                    ·
                      refine ⟨1619996548250755547740739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4319990795335348127308637 1619996548250755547740739)
                      ·
                        rfl

theorem cell23_3154932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3154932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154932 prefixEnd_3154932 := by exact prefixLift 3154932
  have htrace : WordTrace (prefixWord ++ tailWord_3154932) baseStart_3154932 baseEnd_3154932 := by
    simpa [prefixWord, tailWord_3154932, baseEnd_3154932] using wordTrace_append hprefix tailTrace_3154932
  have hstable : (prefixWord ++ tailWord_3154932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154932).length < 2 ^ (prefixWord ++ tailWord_3154932).sum := by decide
  have hdescent : baseEnd_3154932 < baseStart_3154932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154970 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 3, 4]
def baseStart_3154970 : Nat := 118140960795 + 3154970 * 2 ^ 59
def prefixEnd_3154970 : Nat := 4983230072969 + 3 ^ 40 * 3154970 * 2
def baseEnd_3154970 : Nat := 540005353505208799688521

theorem tailTrace_3154970 : CollatzResearch.WordTrace tailWord_3154970 prefixEnd_3154970 540005353505208799688521 := by
  unfold tailWord_3154970
  simp only [CollatzResearch.WordTrace]
  refine ⟨28767802345022497705745591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76714139586726660548654909 28767802345022497705745591)
  ·
    refine ⟨43151703517533746558618387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28767802345022497705745591 43151703517533746558618387)
    ·
      refine ⟨64727555276300619837927581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43151703517533746558618387 64727555276300619837927581)
      ·
        refine ⟨24272833228612732439222843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64727555276300619837927581 24272833228612732439222843)
        ·
          refine ⟨36409249842919098658834265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24272833228612732439222843 36409249842919098658834265)
          ·
            refine ⟨27306937382189323994125699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36409249842919098658834265 27306937382189323994125699)
            ·
              refine ⟨40960406073283985991188549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27306937382189323994125699 40960406073283985991188549)
              ·
                refine ⟨7680076138740747373347853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40960406073283985991188549 7680076138740747373347853)
                ·
                  refine ⟨2880028552027780265005445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7680076138740747373347853 2880028552027780265005445)
                  ·
                    refine ⟨540005353505208799688521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2880028552027780265005445 540005353505208799688521)
                    ·
                      rfl

theorem cell23_3154970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_3154970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3154970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3154970 prefixEnd_3154970 := by exact prefixLift 3154970
  have htrace : WordTrace (prefixWord ++ tailWord_3154970) baseStart_3154970 baseEnd_3154970 := by
    simpa [prefixWord, tailWord_3154970, baseEnd_3154970] using wordTrace_append hprefix tailTrace_3154970
  have hstable : (prefixWord ++ tailWord_3154970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154970).length < 2 ^ (prefixWord ++ tailWord_3154970).sum := by decide
  have hdescent : baseEnd_3154970 < baseStart_3154970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155044 : List Nat := [2, 3, 1, 1, 2, 1, 1, 7, 1, 1, 3]
def baseStart_3155044 : Nat := 118140960795 + 3155044 * 2 ^ 59
def prefixEnd_3155044 : Nat := 4983230072969 + 3 ^ 40 * 3155044 * 2
def baseEnd_3155044 : Nat := 1620054058084059109540223

theorem tailTrace_3155044 : CollatzResearch.WordTrace tailWord_3155044 prefixEnd_3155044 1620054058084059109540223 := by
  unfold tailWord_3155044
  simp only [CollatzResearch.WordTrace]
  refine ⟨57536954190910950730588093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76715938921214600974117457 57536954190910950730588093)
  ·
    refine ⟨21576357821591606523970535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57536954190910950730588093 21576357821591606523970535)
    ·
      refine ⟨32364536732387409785955803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21576357821591606523970535 32364536732387409785955803)
      ·
        refine ⟨48546805098581114678933705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32364536732387409785955803 48546805098581114678933705)
        ·
          refine ⟨36410103823935836009200279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48546805098581114678933705 36410103823935836009200279)
          ·
            refine ⟨54615155735903754013800419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36410103823935836009200279 54615155735903754013800419)
            ·
              refine ⟨81922733603855631020700629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54615155735903754013800419 81922733603855631020700629)
              ·
                refine ⟨1920064068840366352047671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 81922733603855631020700629 1920064068840366352047671)
                ·
                  refine ⟨2880096103260549528071507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920064068840366352047671 2880096103260549528071507)
                  ·
                    refine ⟨4320144154890824292107261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2880096103260549528071507 4320144154890824292107261)
                    ·
                      refine ⟨1620054058084059109540223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4320144154890824292107261 1620054058084059109540223)
                      ·
                        rfl

theorem cell23_3155044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_3155044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155044 prefixEnd_3155044 := by exact prefixLift 3155044
  have htrace : WordTrace (prefixWord ++ tailWord_3155044) baseStart_3155044 baseEnd_3155044 := by
    simpa [prefixWord, tailWord_3155044, baseEnd_3155044] using wordTrace_append hprefix tailTrace_3155044
  have hstable : (prefixWord ++ tailWord_3155044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155044).length < 2 ^ (prefixWord ++ tailWord_3155044).sum := by decide
  have hdescent : baseEnd_3155044 < baseStart_3155044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155054 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_3155054 : Nat := 118140960795 + 3155054 * 2 ^ 59
def prefixEnd_3155054 : Nat := 4983230072969 + 3 ^ 40 * 3155054 * 2
def baseEnd_3155054 : Nat := 1620059192890604070415177

theorem tailTrace_3155054 : CollatzResearch.WordTrace tailWord_3155054 prefixEnd_3155054 1620059192890604070415177 := by
  unfold tailWord_3155054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14384284138973209146130027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76716182074523782112693477 14384284138973209146130027)
  ·
    refine ⟨21576426208459813719195041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14384284138973209146130027 21576426208459813719195041)
    ·
      refine ⟨16182319656344860289396281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21576426208459813719195041 16182319656344860289396281)
      ·
        refine ⟨12136739742258645217047211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16182319656344860289396281 12136739742258645217047211)
        ·
          refine ⟨18205109613387967825570817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12136739742258645217047211 18205109613387967825570817)
          ·
            refine ⟨13653832210040975869178113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18205109613387967825570817 13653832210040975869178113)
            ·
              refine ⟨10240374157530731901883585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13653832210040975869178113 10240374157530731901883585)
              ·
                refine ⟨7680280618148048926412689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10240374157530731901883585 7680280618148048926412689)
                ·
                  refine ⟨5760210463611036694809517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7680280618148048926412689 5760210463611036694809517)
                  ·
                    refine ⟨2160078923854138760553569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5760210463611036694809517 2160078923854138760553569)
                    ·
                      refine ⟨1620059192890604070415177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160078923854138760553569 1620059192890604070415177)
                      ·
                        rfl

theorem cell23_3155054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_3155054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155054 prefixEnd_3155054 := by exact prefixLift 3155054
  have htrace : WordTrace (prefixWord ++ tailWord_3155054) baseStart_3155054 baseEnd_3155054 := by
    simpa [prefixWord, tailWord_3155054, baseEnd_3155054] using wordTrace_append hprefix tailTrace_3155054
  have hstable : (prefixWord ++ tailWord_3155054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155054).length < 2 ^ (prefixWord ++ tailWord_3155054).sum := by decide
  have hdescent : baseEnd_3155054 < baseStart_3155054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155067 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 7, 2, 2]
def baseStart_3155067 : Nat := 118140960795 + 3155067 * 2 ^ 59
def prefixEnd_3155067 : Nat := 4983230072969 + 3 ^ 40 * 3155067 * 2
def baseEnd_3155067 : Nat := 1620065868139112519552617

theorem tailTrace_3155067 : CollatzResearch.WordTrace tailWord_3155067 prefixEnd_3155067 1620065868139112519552617 := by
  unfold tailWord_3155067
  simp only [CollatzResearch.WordTrace]
  refine ⟨115074747260738576389263455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76716498173825717592842303 115074747260738576389263455)
  ·
    refine ⟨172612120891107864583895183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115074747260738576389263455 172612120891107864583895183)
    ·
      refine ⟨258918181336661796875842775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172612120891107864583895183 258918181336661796875842775)
      ·
        refine ⟨388377272004992695313764163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258918181336661796875842775 388377272004992695313764163)
        ·
          refine ⟨582565908007489042970646245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388377272004992695313764163 582565908007489042970646245)
          ·
            refine ⟨109231107751404195556996171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 582565908007489042970646245 109231107751404195556996171)
            ·
              refine ⟨163846661627106293335494257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109231107751404195556996171 163846661627106293335494257)
              ·
                refine ⟨122884996220329720001620693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163846661627106293335494257 122884996220329720001620693)
                ·
                  refine ⟨2880117098913977812537985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 122884996220329720001620693 2880117098913977812537985)
                  ·
                    refine ⟨2160087824185483359403489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2880117098913977812537985 2160087824185483359403489)
                    ·
                      refine ⟨1620065868139112519552617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160087824185483359403489 1620065868139112519552617)
                      ·
                        rfl

theorem cell23_3155067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 2, 2].length) (baseStart_3155067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155067 prefixEnd_3155067 := by exact prefixLift 3155067
  have htrace : WordTrace (prefixWord ++ tailWord_3155067) baseStart_3155067 baseEnd_3155067 := by
    simpa [prefixWord, tailWord_3155067, baseEnd_3155067] using wordTrace_append hprefix tailTrace_3155067
  have hstable : (prefixWord ++ tailWord_3155067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155067).length < 2 ^ (prefixWord ++ tailWord_3155067).sum := by decide
  have hdescent : baseEnd_3155067 < baseStart_3155067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155077 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 1, 6]
def baseStart_3155077 : Nat := 118140960795 + 3155077 * 2 ^ 59
def prefixEnd_3155077 : Nat := 4983230072969 + 3 ^ 40 * 3155077 * 2
def baseEnd_3155077 : Nat := 540023667648552493475857

theorem tailTrace_3155077 : CollatzResearch.WordTrace tailWord_3155077 prefixEnd_3155077 540023667648552493475857 := by
  unfold tailWord_3155077
  simp only [CollatzResearch.WordTrace]
  refine ⟨115075111990702348097127485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76716741327134898731418323 115075111990702348097127485)
  ·
    refine ⟨43153166996513380536422807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115075111990702348097127485 43153166996513380536422807)
    ·
      refine ⟨64729750494770070804634211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43153166996513380536422807 64729750494770070804634211)
      ·
        refine ⟨97094625742155106206951317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64729750494770070804634211 97094625742155106206951317)
        ·
          refine ⟨4551310581663520603450843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97094625742155106206951317 4551310581663520603450843)
          ·
            refine ⟨6826965872495280905176265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551310581663520603450843 6826965872495280905176265)
            ·
              refine ⟨5120224404371460678882199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6826965872495280905176265 5120224404371460678882199)
              ·
                refine ⟨7680336606557191018323299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5120224404371460678882199 7680336606557191018323299)
                ·
                  refine ⟨11520504909835786527484949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7680336606557191018323299 11520504909835786527484949)
                  ·
                    refine ⟨540023667648552493475857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11520504909835786527484949 540023667648552493475857)
                    ·
                      rfl

theorem cell23_3155077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_3155077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155077 prefixEnd_3155077 := by exact prefixLift 3155077
  have htrace : WordTrace (prefixWord ++ tailWord_3155077) baseStart_3155077 baseEnd_3155077 := by
    simpa [prefixWord, tailWord_3155077, baseEnd_3155077] using wordTrace_append hprefix tailTrace_3155077
  have hstable : (prefixWord ++ tailWord_3155077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155077).length < 2 ^ (prefixWord ++ tailWord_3155077).sum := by decide
  have hdescent : baseEnd_3155077 < baseStart_3155077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155083 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 7]
def baseStart_3155083 : Nat := 118140960795 + 3155083 * 2 ^ 59
def prefixEnd_3155083 : Nat := 4983230072969 + 3 ^ 40 * 3155083 * 2
def baseEnd_3155083 : Nat := 1620074083829584456952543

theorem tailTrace_3155083 : CollatzResearch.WordTrace tailWord_3155083 prefixEnd_3155083 1620074083829584456952543 := by
  unfold tailWord_3155083
  simp only [CollatzResearch.WordTrace]
  refine ⟨115075330828680611121845903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76716887219120407414563935 115075330828680611121845903)
  ·
    refine ⟨172612996243020916682768855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115075330828680611121845903 172612996243020916682768855)
    ·
      refine ⟨258919494364531375024153283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172612996243020916682768855 258919494364531375024153283)
      ·
        refine ⟨388379241546797062536229925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258919494364531375024153283 388379241546797062536229925)
        ·
          refine ⟨72821107790024449225543111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 388379241546797062536229925 72821107790024449225543111)
          ·
            refine ⟨109231661685036673838314667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72821107790024449225543111 109231661685036673838314667)
            ·
              refine ⟨163847492527555010757472001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109231661685036673838314667 163847492527555010757472001)
              ·
                refine ⟨122885619395666258068104001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163847492527555010757472001 122885619395666258068104001)
                ·
                  refine ⟨92164214546749693551078001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122885619395666258068104001 92164214546749693551078001)
                  ·
                    refine ⟨69123160910062270163308501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92164214546749693551078001 69123160910062270163308501)
                    ·
                      refine ⟨1620074083829584456952543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69123160910062270163308501 1620074083829584456952543)
                      ·
                        rfl

theorem cell23_3155083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_3155083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155083 prefixEnd_3155083 := by exact prefixLift 3155083
  have htrace : WordTrace (prefixWord ++ tailWord_3155083) baseStart_3155083 baseEnd_3155083 := by
    simpa [prefixWord, tailWord_3155083, baseEnd_3155083] using wordTrace_append hprefix tailTrace_3155083
  have hstable : (prefixWord ++ tailWord_3155083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155083).length < 2 ^ (prefixWord ++ tailWord_3155083).sum := by decide
  have hdescent : baseEnd_3155083 < baseStart_3155083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155111 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 2, 4]
def baseStart_3155111 : Nat := 118140960795 + 3155111 * 2 ^ 59
def prefixEnd_3155111 : Nat := 4983230072969 + 3 ^ 40 * 3155111 * 2
def baseEnd_3155111 : Nat := 540029487095970115800805

theorem tailTrace_3155111 : CollatzResearch.WordTrace tailWord_3155111 prefixEnd_3155111 540029487095970115800805 := by
  unfold tailWord_3155111
  simp only [CollatzResearch.WordTrace]
  refine ⟨115076352072579171903865187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76717568048386114602576791 115076352072579171903865187)
  ·
    refine ⟨172614528108868757855797781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115076352072579171903865187 172614528108868757855797781)
    ·
      refine ⟨8091306005103223024490521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 172614528108868757855797781 8091306005103223024490521)
      ·
        refine ⟨6068479503827417268367891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8091306005103223024490521 6068479503827417268367891)
        ·
          refine ⟨9102719255741125902551837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6068479503827417268367891 9102719255741125902551837)
          ·
            refine ⟨3413519720902922213456939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9102719255741125902551837 3413519720902922213456939)
            ·
              refine ⟨5120279581354383320185409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3413519720902922213456939 5120279581354383320185409)
              ·
                refine ⟨3840209686015787490139057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5120279581354383320185409 3840209686015787490139057)
                ·
                  refine ⟨2880157264511840617604293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3840209686015787490139057 2880157264511840617604293)
                  ·
                    refine ⟨540029487095970115800805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2880157264511840617604293 540029487095970115800805)
                    ·
                      rfl

theorem cell23_3155111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_3155111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155111 prefixEnd_3155111 := by exact prefixLift 3155111
  have htrace : WordTrace (prefixWord ++ tailWord_3155111) baseStart_3155111 baseEnd_3155111 := by
    simpa [prefixWord, tailWord_3155111, baseEnd_3155111] using wordTrace_append hprefix tailTrace_3155111
  have hstable : (prefixWord ++ tailWord_3155111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155111).length < 2 ^ (prefixWord ++ tailWord_3155111).sum := by decide
  have hdescent : baseEnd_3155111 < baseStart_3155111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155134 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_3155134 : Nat := 118140960795 + 3155134 * 2 ^ 59
def prefixEnd_3155134 : Nat := 4983230072969 + 3 ^ 40 * 3155134 * 2
def baseEnd_3155134 : Nat := 1620100271342963757414809

theorem tailTrace_3155134 : CollatzResearch.WordTrace tailWord_3155134 prefixEnd_3155134 1620100271342963757414809 := by
  unfold tailWord_3155134
  simp only [CollatzResearch.WordTrace]
  refine ⟨14384648868936980853994057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76718127300997231221301637 14384648868936980853994057)
  ·
    refine ⟨10788486651702735640495543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14384648868936980853994057 10788486651702735640495543)
    ·
      refine ⟨16182729977554103460743315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10788486651702735640495543 16182729977554103460743315)
      ·
        refine ⟨24274094966331155191114973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16182729977554103460743315 24274094966331155191114973)
        ·
          refine ⟨9102785612374183196668115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24274094966331155191114973 9102785612374183196668115)
          ·
            refine ⟨13654178418561274795002173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9102785612374183196668115 13654178418561274795002173)
            ·
              refine ⟨5120316906960478048125815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13654178418561274795002173 5120316906960478048125815)
              ·
                refine ⟨7680475360440717072188723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5120316906960478048125815 7680475360440717072188723)
                ·
                  refine ⟨11520713040661075608283085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7680475360440717072188723 11520713040661075608283085)
                  ·
                    refine ⟨4320267390247903353106157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11520713040661075608283085 4320267390247903353106157)
                    ·
                      refine ⟨1620100271342963757414809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4320267390247903353106157 1620100271342963757414809)
                      ·
                        rfl

theorem cell23_3155134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_3155134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155134 prefixEnd_3155134 := by exact prefixLift 3155134
  have htrace : WordTrace (prefixWord ++ tailWord_3155134) baseStart_3155134 baseEnd_3155134 := by
    simpa [prefixWord, tailWord_3155134, baseEnd_3155134] using wordTrace_append hprefix tailTrace_3155134
  have hstable : (prefixWord ++ tailWord_3155134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155134).length < 2 ^ (prefixWord ++ tailWord_3155134).sum := by decide
  have hdescent : baseEnd_3155134 < baseStart_3155134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155144 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 1, 3, 2]
def baseStart_3155144 : Nat := 118140960795 + 3155144 * 2 ^ 59
def prefixEnd_3155144 : Nat := 4983230072969 + 3 ^ 40 * 3155144 * 2
def baseEnd_3155144 : Nat := 1620105406149508718289763

theorem tailTrace_3155144 : CollatzResearch.WordTrace tailWord_3155144 prefixEnd_3155144 1620105406149508718289763 := by
  unfold tailWord_3155144
  simp only [CollatzResearch.WordTrace]
  refine ⟨57538777840729809269908243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76718370454306412359877657 57538777840729809269908243)
  ·
    refine ⟨86308166761094713904862365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57538777840729809269908243 86308166761094713904862365)
    ·
      refine ⟨32365562535410517714323387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86308166761094713904862365 32365562535410517714323387)
      ·
        refine ⟨48548343803115776571485081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32365562535410517714323387 48548343803115776571485081)
        ·
          refine ⟨36411257852336832428613811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48548343803115776571485081 36411257852336832428613811)
          ·
            refine ⟨54616886778505248642920717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36411257852336832428613811 54616886778505248642920717)
            ·
              refine ⟨20481332541939468241095269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54616886778505248642920717 20481332541939468241095269)
              ·
                refine ⟨3840249851613650295205363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20481332541939468241095269 3840249851613650295205363)
                ·
                  refine ⟨5760374777420475442808045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3840249851613650295205363 5760374777420475442808045)
                  ·
                    refine ⟨2160140541532678291053017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5760374777420475442808045 2160140541532678291053017)
                    ·
                      refine ⟨1620105406149508718289763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160140541532678291053017 1620105406149508718289763)
                      ·
                        rfl

theorem cell23_3155144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_3155144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155144 prefixEnd_3155144 := by exact prefixLift 3155144
  have htrace : WordTrace (prefixWord ++ tailWord_3155144) baseStart_3155144 baseEnd_3155144 := by
    simpa [prefixWord, tailWord_3155144, baseEnd_3155144] using wordTrace_append hprefix tailTrace_3155144
  have hstable : (prefixWord ++ tailWord_3155144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155144).length < 2 ^ (prefixWord ++ tailWord_3155144).sum := by decide
  have hdescent : baseEnd_3155144 < baseStart_3155144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155237 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_3155237 : Nat := 118140960795 + 3155237 * 2 ^ 59
def prefixEnd_3155237 : Nat := 4983230072969 + 3 ^ 40 * 3155237 * 2
def baseEnd_3155237 : Nat := 1620153159850376854426835

theorem tailTrace_3155237 : CollatzResearch.WordTrace tailWord_3155237 prefixEnd_3155237 1620153159850376854426835 := by
  unfold tailWord_3155237
  simp only [CollatzResearch.WordTrace]
  refine ⟨115080947670122695422951965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76720631780081796948634643 115080947670122695422951965)
  ·
    refine ⟨43155355376296010783606987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115080947670122695422951965 43155355376296010783606987)
    ·
      refine ⟨64733033064444016175410481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43155355376296010783606987 64733033064444016175410481)
      ·
        refine ⟨48549774798333012131557861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64733033064444016175410481 48549774798333012131557861)
        ·
          refine ⟨9103082774687439774667099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48549774798333012131557861 9103082774687439774667099)
          ·
            refine ⟨13654624162031159662000649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9103082774687439774667099 13654624162031159662000649)
            ·
              refine ⟨10240968121523369746500487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13654624162031159662000649 10240968121523369746500487)
              ·
                refine ⟨15361452182285054619750731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10240968121523369746500487 15361452182285054619750731)
                ·
                  refine ⟨23042178273427581929626097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15361452182285054619750731 23042178273427581929626097)
                  ·
                    refine ⟨17281633705070686447219573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23042178273427581929626097 17281633705070686447219573)
                    ·
                      refine ⟨1620153159850376854426835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17281633705070686447219573 1620153159850376854426835)
                      ·
                        rfl

theorem cell23_3155237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_3155237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155237 prefixEnd_3155237 := by exact prefixLift 3155237
  have htrace : WordTrace (prefixWord ++ tailWord_3155237) baseStart_3155237 baseEnd_3155237 := by
    simpa [prefixWord, tailWord_3155237, baseEnd_3155237] using wordTrace_append hprefix tailTrace_3155237
  have hstable : (prefixWord ++ tailWord_3155237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155237).length < 2 ^ (prefixWord ++ tailWord_3155237).sum := by decide
  have hdescent : baseEnd_3155237 < baseStart_3155237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155284 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_3155284 : Nat := 118140960795 + 3155284 * 2 ^ 59
def prefixEnd_3155284 : Nat := 4983230072969 + 3 ^ 40 * 3155284 * 2
def baseEnd_3155284 : Nat := 1620177293441138170539119

theorem tailTrace_3155284 : CollatzResearch.WordTrace tailWord_3155284 prefixEnd_3155284 1620177293441138170539119 := by
  unfold tailWord_3155284
  simp only [CollatzResearch.WordTrace]
  refine ⟨57541330950476211224956453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76721774600634948299941937 57541330950476211224956453)
  ·
    refine ⟨10788999553214289604679335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57541330950476211224956453 10788999553214289604679335)
    ·
      refine ⟨16183499329821434407019003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10788999553214289604679335 16183499329821434407019003)
      ·
        refine ⟨24275248994732151610528505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16183499329821434407019003 24275248994732151610528505)
        ·
          refine ⟨18206436746049113707896379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24275248994732151610528505 18206436746049113707896379)
          ·
            refine ⟨27309655119073670561844569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18206436746049113707896379 27309655119073670561844569)
            ·
              refine ⟨20482241339305252921383427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27309655119073670561844569 20482241339305252921383427)
              ·
                refine ⟨30723362008957879382075141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20482241339305252921383427 30723362008957879382075141)
                ·
                  refine ⟨5760630376679602384139089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30723362008957879382075141 5760630376679602384139089)
                  ·
                    refine ⟨4320472782509701788104317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5760630376679602384139089 4320472782509701788104317)
                    ·
                      refine ⟨1620177293441138170539119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4320472782509701788104317 1620177293441138170539119)
                      ·
                        rfl

theorem cell23_3155284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_3155284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155284 prefixEnd_3155284 := by exact prefixLift 3155284
  have htrace : WordTrace (prefixWord ++ tailWord_3155284) baseStart_3155284 baseEnd_3155284 := by
    simpa [prefixWord, tailWord_3155284, baseEnd_3155284] using wordTrace_append hprefix tailTrace_3155284
  have hstable : (prefixWord ++ tailWord_3155284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155284).length < 2 ^ (prefixWord ++ tailWord_3155284).sum := by decide
  have hdescent : baseEnd_3155284 < baseStart_3155284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155287 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 8]
def baseStart_3155287 : Nat := 118140960795 + 3155287 * 2 ^ 59
def prefixEnd_3155287 : Nat := 4983230072969 + 3 ^ 40 * 3155287 * 2
def baseEnd_3155287 : Nat := 180019870431455739866845

theorem tailTrace_3155287 : CollatzResearch.WordTrace tailWord_3155287 prefixEnd_3155287 180019870431455739866845 := by
  unfold tailWord_3155287
  simp only [CollatzResearch.WordTrace]
  refine ⟨115082771319941553962272115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76721847546627702641514743 115082771319941553962272115)
  ·
    refine ⟨172624156979912330943408173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115082771319941553962272115 172624156979912330943408173)
    ·
      refine ⟨64734058867467124103778065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172624156979912330943408173 64734058867467124103778065)
      ·
        refine ⟨48550544150600343077833549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64734058867467124103778065 48550544150600343077833549)
        ·
          refine ⟨18206454056475128654187581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48550544150600343077833549 18206454056475128654187581)
          ·
            refine ⟨6827420271178173245320343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18206454056475128654187581 6827420271178173245320343)
            ·
              refine ⟨10241130406767259867980515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6827420271178173245320343 10241130406767259867980515)
              ·
                refine ⟨15361695610150889801970773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10241130406767259867980515 15361695610150889801970773)
                ·
                  refine ⟨180019870431455739866845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15361695610150889801970773 180019870431455739866845)
                  ·
                    rfl

theorem cell23_3155287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 8].length) (baseStart_3155287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155287 prefixEnd_3155287 := by exact prefixLift 3155287
  have htrace : WordTrace (prefixWord ++ tailWord_3155287) baseStart_3155287 baseEnd_3155287 := by
    simpa [prefixWord, tailWord_3155287, baseEnd_3155287] using wordTrace_append hprefix tailTrace_3155287
  have hstable : (prefixWord ++ tailWord_3155287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155287).length < 2 ^ (prefixWord ++ tailWord_3155287).sum := by decide
  have hdescent : baseEnd_3155287 < baseStart_3155287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155324 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 1, 5, 2]
def baseStart_3155324 : Nat := 118140960795 + 3155324 * 2 ^ 59
def prefixEnd_3155324 : Nat := 4983230072969 + 3 ^ 40 * 3155324 * 2
def baseEnd_3155324 : Nat := 1620197832667318014038935

theorem tailTrace_3155324 : CollatzResearch.WordTrace tailWord_3155324 prefixEnd_3155324 1620197832667318014038935 := by
  unfold tailWord_3155324
  simp only [CollatzResearch.WordTrace]
  refine ⟨57542060410403754640684513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76722747213871672854246017 57542060410403754640684513)
  ·
    refine ⟨43156545307802815980513385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57542060410403754640684513 43156545307802815980513385)
    ·
      refine ⟨32367408980852111985385039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43156545307802815980513385 32367408980852111985385039)
      ·
        refine ⟨48551113471278167978077559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32367408980852111985385039 48551113471278167978077559)
        ·
          refine ⟨72826670206917251967116339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48551113471278167978077559 72826670206917251967116339)
          ·
            refine ⟨109240005310375877950674509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72826670206917251967116339 109240005310375877950674509)
            ·
              refine ⟨40965001991390954231502941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109240005310375877950674509 40965001991390954231502941)
              ·
                refine ⟨15361875746771607836813603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40965001991390954231502941 15361875746771607836813603)
                ·
                  refine ⟨23042813620157411755220405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15361875746771607836813603 23042813620157411755220405)
                  ·
                    refine ⟨2160263776889757352051913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23042813620157411755220405 2160263776889757352051913)
                    ·
                      refine ⟨1620197832667318014038935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160263776889757352051913 1620197832667318014038935)
                      ·
                        rfl

theorem cell23_3155324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_3155324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155324 prefixEnd_3155324 := by exact prefixLift 3155324
  have htrace : WordTrace (prefixWord ++ tailWord_3155324) baseStart_3155324 baseEnd_3155324 := by
    simpa [prefixWord, tailWord_3155324, baseEnd_3155324] using wordTrace_append hprefix tailTrace_3155324
  have hstable : (prefixWord ++ tailWord_3155324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155324).length < 2 ^ (prefixWord ++ tailWord_3155324).sum := by decide
  have hdescent : baseEnd_3155324 < baseStart_3155324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155348 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_3155348 : Nat := 118140960795 + 3155348 * 2 ^ 59
def prefixEnd_3155348 : Nat := 4983230072969 + 3 ^ 40 * 3155348 * 2
def baseEnd_3155348 : Nat := 1620210156203025920138825

theorem tailTrace_3155348 : CollatzResearch.WordTrace tailWord_3155348 prefixEnd_3155348 1620210156203025920138825 := by
  unfold tailWord_3155348
  simp only [CollatzResearch.WordTrace]
  refine ⟨57542498086360280690121349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76723330781813707586828465 57542498086360280690121349)
  ·
    refine ⟨10789218391192552629397753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57542498086360280690121349 10789218391192552629397753)
    ·
      refine ⟨8091913793394414472048315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10789218391192552629397753 8091913793394414472048315)
      ·
        refine ⟨12137870690091621708072473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8091913793394414472048315 12137870690091621708072473)
        ·
          refine ⟨9103403017568716281054355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12137870690091621708072473 9103403017568716281054355)
          ·
            refine ⟨13655104526353074421581533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9103403017568716281054355 13655104526353074421581533)
            ·
              refine ⟨5120664197382402908093075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13655104526353074421581533 5120664197382402908093075)
              ·
                refine ⟨7680996296073604362139613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5120664197382402908093075 7680996296073604362139613)
                ·
                  refine ⟨2880373611027601635802355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7680996296073604362139613 2880373611027601635802355)
                  ·
                    refine ⟨4320560416541402453703533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2880373611027601635802355 4320560416541402453703533)
                    ·
                      refine ⟨1620210156203025920138825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4320560416541402453703533 1620210156203025920138825)
                      ·
                        rfl

theorem cell23_3155348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_3155348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155348 prefixEnd_3155348 := by exact prefixLift 3155348
  have htrace : WordTrace (prefixWord ++ tailWord_3155348) baseStart_3155348 baseEnd_3155348 := by
    simpa [prefixWord, tailWord_3155348, baseEnd_3155348] using wordTrace_append hprefix tailTrace_3155348
  have hstable : (prefixWord ++ tailWord_3155348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155348).length < 2 ^ (prefixWord ++ tailWord_3155348).sum := by decide
  have hdescent : baseEnd_3155348 < baseStart_3155348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155354 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_3155354 : Nat := 118140960795 + 3155354 * 2 ^ 59
def prefixEnd_3155354 : Nat := 4983230072969 + 3 ^ 40 * 3155354 * 2
def baseEnd_3155354 : Nat := 1620213237086952896663797

theorem tailTrace_3155354 : CollatzResearch.WordTrace tailWord_3155354 prefixEnd_3155354 1620213237086952896663797 := by
  unfold tailWord_3155354
  simp only [CollatzResearch.WordTrace]
  refine ⟨28771303752674706101240279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76723476673799216269974077 28771303752674706101240279)
  ·
    refine ⟨43156955629012059151860419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28771303752674706101240279 43156955629012059151860419)
    ·
      refine ⟨64735433443518088727790629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43156955629012059151860419 64735433443518088727790629)
      ·
        refine ⟨12137893770659641636460743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64735433443518088727790629 12137893770659641636460743)
        ·
          refine ⟨18206840655989462454691115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12137893770659641636460743 18206840655989462454691115)
          ·
            refine ⟨27310260983984193682036673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18206840655989462454691115 27310260983984193682036673)
            ·
              refine ⟨20482695737988145261527505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27310260983984193682036673 20482695737988145261527505)
              ·
                refine ⟨15362021803491108946145629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20482695737988145261527505 15362021803491108946145629)
                ·
                  refine ⟨5760758176309165854804611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15362021803491108946145629 5760758176309165854804611)
                  ·
                    refine ⟨8641137264463748782206917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5760758176309165854804611 8641137264463748782206917)
                    ·
                      refine ⟨1620213237086952896663797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8641137264463748782206917 1620213237086952896663797)
                      ·
                        rfl

theorem cell23_3155354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_3155354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155354 prefixEnd_3155354 := by exact prefixLift 3155354
  have htrace : WordTrace (prefixWord ++ tailWord_3155354) baseStart_3155354 baseEnd_3155354 := by
    simpa [prefixWord, tailWord_3155354, baseEnd_3155354] using wordTrace_append hprefix tailTrace_3155354
  have hstable : (prefixWord ++ tailWord_3155354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155354).length < 2 ^ (prefixWord ++ tailWord_3155354).sum := by decide
  have hdescent : baseEnd_3155354 < baseStart_3155354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155377 : List Nat := [1, 2, 2, 4, 1, 1, 1, 11]
def baseStart_3155377 : Nat := 118140960795 + 3155377 * 2 ^ 59
def prefixEnd_3155377 : Nat := 4983230072969 + 3 ^ 40 * 3155377 * 2
def baseEnd_3155377 : Nat := 60008335079333566913933

theorem tailTrace_3155377 : CollatzResearch.WordTrace tailWord_3155377 prefixEnd_3155377 60008335079333566913933 := by
  unfold tailWord_3155377
  simp only [CollatzResearch.WordTrace]
  refine ⟨115086053889615499333048385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76724035926410332888698923 115086053889615499333048385)
  ·
    refine ⟨86314540417211624499786289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115086053889615499333048385 86314540417211624499786289)
    ·
      refine ⟨64735905312908718374839717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86314540417211624499786289 64735905312908718374839717)
      ·
        refine ⟨12137982246170384695282447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64735905312908718374839717 12137982246170384695282447)
        ·
          refine ⟨18206973369255577042923671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12137982246170384695282447 18206973369255577042923671)
          ·
            refine ⟨27310460053883365564385507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18206973369255577042923671 27310460053883365564385507)
            ·
              refine ⟨40965690080825048346578261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27310460053883365564385507 40965690080825048346578261)
              ·
                refine ⟨60008335079333566913933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 40965690080825048346578261 60008335079333566913933)
                ·
                  rfl

theorem cell23_3155377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 11].length) (baseStart_3155377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155377 prefixEnd_3155377 := by exact prefixLift 3155377
  have htrace : WordTrace (prefixWord ++ tailWord_3155377) baseStart_3155377 baseEnd_3155377 := by
    simpa [prefixWord, tailWord_3155377, baseEnd_3155377] using wordTrace_append hprefix tailTrace_3155377
  have hstable : (prefixWord ++ tailWord_3155377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155377).length < 2 ^ (prefixWord ++ tailWord_3155377).sum := by decide
  have hdescent : baseEnd_3155377 < baseStart_3155377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155407 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 2, 7]
def baseStart_3155407 : Nat := 118140960795 + 3155407 * 2 ^ 59
def prefixEnd_3155407 : Nat := 4983230072969 + 3 ^ 40 * 3155407 * 2
def baseEnd_3155407 : Nat := 540080150520547063100351

theorem tailTrace_3155407 : CollatzResearch.WordTrace tailWord_3155407 prefixEnd_3155407 540080150520547063100351 := by
  unfold tailWord_3155407
  simp only [CollatzResearch.WordTrace]
  refine ⟨115087148079506814456640475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76724765386337876304426983 115087148079506814456640475)
  ·
    refine ⟨172630722119260221684960713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115087148079506814456640475 172630722119260221684960713)
    ·
      refine ⟨129473041589445166263720535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172630722119260221684960713 129473041589445166263720535)
      ·
        refine ⟨194209562384167749395580803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129473041589445166263720535 194209562384167749395580803)
        ·
          refine ⟨291314343576251624093371205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194209562384167749395580803 291314343576251624093371205)
          ·
            refine ⟨54621439420547179517507101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291314343576251624093371205 54621439420547179517507101)
            ·
              refine ⟨20483039782705192319065163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54621439420547179517507101 20483039782705192319065163)
              ·
                refine ⟨30724559674057788478597745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20483039782705192319065163 30724559674057788478597745)
                ·
                  refine ⟨23043419755543341358948309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30724559674057788478597745 23043419755543341358948309)
                  ·
                    refine ⟨540080150520547063100351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23043419755543341358948309 540080150520547063100351)
                    ·
                      rfl

theorem cell23_3155407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_3155407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155407 prefixEnd_3155407 := by exact prefixLift 3155407
  have htrace : WordTrace (prefixWord ++ tailWord_3155407) baseStart_3155407 baseEnd_3155407 := by
    simpa [prefixWord, tailWord_3155407, baseEnd_3155407] using wordTrace_append hprefix tailTrace_3155407
  have hstable : (prefixWord ++ tailWord_3155407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155407).length < 2 ^ (prefixWord ++ tailWord_3155407).sum := by decide
  have hdescent : baseEnd_3155407 < baseStart_3155407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155421 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_3155421 : Nat := 118140960795 + 3155421 * 2 ^ 59
def prefixEnd_3155421 : Nat := 4983230072969 + 3 ^ 40 * 3155421 * 2
def baseEnd_3155421 : Nat := 1620247640290804134525989

theorem tailTrace_3155421 : CollatzResearch.WordTrace tailWord_3155421 prefixEnd_3155421 1620247640290804134525989 := by
  unfold tailWord_3155421
  simp only [CollatzResearch.WordTrace]
  refine ⟨115087658701456094847650117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76725105800970729898433411 115087658701456094847650117)
  ·
    refine ⟨21578936006523017783934397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115087658701456094847650117 21578936006523017783934397)
    ·
      refine ⟨8092101002446131668975399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21578936006523017783934397 8092101002446131668975399)
      ·
        refine ⟨12138151503669197503463099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8092101002446131668975399 12138151503669197503463099)
        ·
          refine ⟨18207227255503796255194649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12138151503669197503463099 18207227255503796255194649)
          ·
            refine ⟨13655420441627847191395987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18207227255503796255194649 13655420441627847191395987)
            ·
              refine ⟨20483130662441770787093981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13655420441627847191395987 20483130662441770787093981)
              ·
                refine ⟨7681173998415664045160243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20483130662441770787093981 7681173998415664045160243)
                ·
                  refine ⟨11521760997623496067740365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7681173998415664045160243 11521760997623496067740365)
                  ·
                    refine ⟨4320660374108811025402637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11521760997623496067740365 4320660374108811025402637)
                    ·
                      refine ⟨1620247640290804134525989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4320660374108811025402637 1620247640290804134525989)
                      ·
                        rfl

theorem cell23_3155421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_3155421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155421 prefixEnd_3155421 := by exact prefixLift 3155421
  have htrace : WordTrace (prefixWord ++ tailWord_3155421) baseStart_3155421 baseEnd_3155421 := by
    simpa [prefixWord, tailWord_3155421, baseEnd_3155421] using wordTrace_append hprefix tailTrace_3155421
  have hstable : (prefixWord ++ tailWord_3155421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155421).length < 2 ^ (prefixWord ++ tailWord_3155421).sum := by decide
  have hdescent : baseEnd_3155421 < baseStart_3155421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155448 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 1, 3, 2]
def baseStart_3155448 : Nat := 118140960795 + 3155448 * 2 ^ 59
def prefixEnd_3155448 : Nat := 4983230072969 + 3 ^ 40 * 3155448 * 2
def baseEnd_3155448 : Nat := 1620261504268475528888365

theorem tailTrace_3155448 : CollatzResearch.WordTrace tailWord_3155448 prefixEnd_3155448 1620261504268475528888365 := by
  unfold tailWord_3155448
  simp only [CollatzResearch.WordTrace]
  refine ⟨57544321736179139229441499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76725762314905518972588665 57544321736179139229441499)
  ·
    refine ⟨86316482604268708844162249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57544321736179139229441499 86316482604268708844162249)
    ·
      refine ⟨64737361953201531633121687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86316482604268708844162249 64737361953201531633121687)
      ·
        refine ⟨97106042929802297449682531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64737361953201531633121687 97106042929802297449682531)
        ·
          refine ⟨145659064394703446174523797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97106042929802297449682531 145659064394703446174523797)
          ·
            refine ⟨6827768643501724039430803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145659064394703446174523797 6827768643501724039430803)
            ·
              refine ⟨10241652965252586059146205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6827768643501724039430803 10241652965252586059146205)
              ·
                refine ⟨3840619861969719772179827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10241652965252586059146205 3840619861969719772179827)
                ·
                  refine ⟨5760929792954579658269741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3840619861969719772179827 5760929792954579658269741)
                  ·
                    refine ⟨2160348672357967371851153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5760929792954579658269741 2160348672357967371851153)
                    ·
                      refine ⟨1620261504268475528888365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160348672357967371851153 1620261504268475528888365)
                      ·
                        rfl

theorem cell23_3155448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 3, 2].length) (baseStart_3155448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155448 prefixEnd_3155448 := by exact prefixLift 3155448
  have htrace : WordTrace (prefixWord ++ tailWord_3155448) baseStart_3155448 baseEnd_3155448 := by
    simpa [prefixWord, tailWord_3155448, baseEnd_3155448] using wordTrace_append hprefix tailTrace_3155448
  have hstable : (prefixWord ++ tailWord_3155448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155448).length < 2 ^ (prefixWord ++ tailWord_3155448).sum := by decide
  have hdescent : baseEnd_3155448 < baseStart_3155448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155464 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_3155464 : Nat := 118140960795 + 3155464 * 2 ^ 59
def prefixEnd_3155464 : Nat := 4983230072969 + 3 ^ 40 * 3155464 * 2
def baseEnd_3155464 : Nat := 1620269719958947466288291

theorem tailTrace_3155464 : CollatzResearch.WordTrace tailWord_3155464 prefixEnd_3155464 1620269719958947466288291 := by
  unfold tailWord_3155464
  simp only [CollatzResearch.WordTrace]
  refine ⟨57544613520150156595732723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76726151360200208794310297 57544613520150156595732723)
  ·
    refine ⟨86316920280225234893599085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57544613520150156595732723 86316920280225234893599085)
    ·
      refine ⟨32368845105084463085099657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86316920280225234893599085 32368845105084463085099657)
      ·
        refine ⟨24276633828813347313824743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32368845105084463085099657 24276633828813347313824743)
        ·
          refine ⟨36414950743220020970737115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24276633828813347313824743 36414950743220020970737115)
          ·
            refine ⟨54622426114830031456105673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36414950743220020970737115 54622426114830031456105673)
            ·
              refine ⟨40966819586122523592079255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54622426114830031456105673 40966819586122523592079255)
              ·
                refine ⟨61450229379183785388118883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40966819586122523592079255 61450229379183785388118883)
                ·
                  refine ⟨92175344068775678082178325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61450229379183785388118883 92175344068775678082178325)
                  ·
                    refine ⟨4320719253223859910102109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92175344068775678082178325 4320719253223859910102109)
                    ·
                      refine ⟨1620269719958947466288291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4320719253223859910102109 1620269719958947466288291)
                      ·
                        rfl

theorem cell23_3155464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_3155464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155464 prefixEnd_3155464 := by exact prefixLift 3155464
  have htrace : WordTrace (prefixWord ++ tailWord_3155464) baseStart_3155464 baseEnd_3155464 := by
    simpa [prefixWord, tailWord_3155464, baseEnd_3155464] using wordTrace_append hprefix tailTrace_3155464
  have hstable : (prefixWord ++ tailWord_3155464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155464).length < 2 ^ (prefixWord ++ tailWord_3155464).sum := by decide
  have hdescent : baseEnd_3155464 < baseStart_3155464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155484 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 7]
def baseStart_3155484 : Nat := 118140960795 + 3155484 * 2 ^ 59
def prefixEnd_3155484 : Nat := 4983230072969 + 3 ^ 40 * 3155484 * 2
def baseEnd_3155484 : Nat := 180031109952448598670911

theorem tailTrace_3155484 : CollatzResearch.WordTrace tailWord_3155484 prefixEnd_3155484 180031109952448598670911 := by
  unfold tailWord_3155484
  simp only [CollatzResearch.WordTrace]
  refine ⟨57544978250113928303596753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76726637666818571071462337 57544978250113928303596753)
  ·
    refine ⟨43158733687585446227697565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57544978250113928303596753 43158733687585446227697565)
    ·
      refine ⟨16184525132844542335386587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43158733687585446227697565 16184525132844542335386587)
      ·
        refine ⟨24276787699266813503079881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16184525132844542335386587 24276787699266813503079881)
        ·
          refine ⟨18207590774450110127309911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24276787699266813503079881 18207590774450110127309911)
          ·
            refine ⟨27311386161675165190964867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18207590774450110127309911 27311386161675165190964867)
            ·
              refine ⟨40967079242512747786447301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27311386161675165190964867 40967079242512747786447301)
              ·
                refine ⟨7681327357971140209958869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40967079242512747786447301 7681327357971140209958869)
                ·
                  refine ⟨180031109952448598670911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7681327357971140209958869 180031109952448598670911)
                  ·
                    rfl

theorem cell23_3155484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_3155484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155484 prefixEnd_3155484 := by exact prefixLift 3155484
  have htrace : WordTrace (prefixWord ++ tailWord_3155484) baseStart_3155484 baseEnd_3155484 := by
    simpa [prefixWord, tailWord_3155484, baseEnd_3155484] using wordTrace_append hprefix tailTrace_3155484
  have hstable : (prefixWord ++ tailWord_3155484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155484).length < 2 ^ (prefixWord ++ tailWord_3155484).sum := by decide
  have hdescent : baseEnd_3155484 < baseStart_3155484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155548 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 2, 5]
def baseStart_3155548 : Nat := 118140960795 + 3155548 * 2 ^ 59
def prefixEnd_3155548 : Nat := 4983230072969 + 3 ^ 40 * 3155548 * 2
def baseEnd_3155548 : Nat := 540104284111308379212635

theorem tailTrace_3155548 : CollatzResearch.WordTrace tailWord_3155548 prefixEnd_3155548 540104284111308379212635 := by
  unfold tailWord_3155548
  simp only [CollatzResearch.WordTrace]
  refine ⟨57546145385997997768761649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76728193847997330358348865 57546145385997997768761649)
  ·
    refine ⟨43159609039498498326571237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57546145385997997768761649 43159609039498498326571237)
    ·
      refine ⟨8092426694905968436232107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43159609039498498326571237 8092426694905968436232107)
      ·
        refine ⟨12138640042358952654348161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8092426694905968436232107 12138640042358952654348161)
        ·
          refine ⟨9103980031769214490761121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12138640042358952654348161 9103980031769214490761121)
          ·
            refine ⟨6827985023826910868070841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9103980031769214490761121 6827985023826910868070841)
            ·
              refine ⟨5120988767870183151053131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6827985023826910868070841 5120988767870183151053131)
              ·
                refine ⟨7681483151805274726579697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5120988767870183151053131 7681483151805274726579697)
                ·
                  refine ⟨5761112363853956044934773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7681483151805274726579697 5761112363853956044934773)
                  ·
                    refine ⟨540104284111308379212635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5761112363853956044934773 540104284111308379212635)
                    ·
                      rfl

theorem cell23_3155548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_3155548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155548 prefixEnd_3155548 := by exact prefixLift 3155548
  have htrace : WordTrace (prefixWord ++ tailWord_3155548) baseStart_3155548 baseEnd_3155548 := by
    simpa [prefixWord, tailWord_3155548, baseEnd_3155548] using wordTrace_append hprefix tailTrace_3155548
  have hstable : (prefixWord ++ tailWord_3155548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155548).length < 2 ^ (prefixWord ++ tailWord_3155548).sum := by decide
  have hdescent : baseEnd_3155548 < baseStart_3155548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155551 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 6, 4, 2]
def baseStart_3155551 : Nat := 118140960795 + 3155551 * 2 ^ 59
def prefixEnd_3155551 : Nat := 4983230072969 + 3 ^ 40 * 3155551 * 2
def baseEnd_3155551 : Nat := 1620314392775888625900391

theorem tailTrace_3155551 : CollatzResearch.WordTrace tailWord_3155551 prefixEnd_3155551 1620314392775888625900391 := by
  unfold tailWord_3155551
  simp only [CollatzResearch.WordTrace]
  refine ⟨115092400190985127049882507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76728266793990084699921671 115092400190985127049882507)
  ·
    refine ⟨172638600286477690574823761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115092400190985127049882507 172638600286477690574823761)
    ·
      refine ⟨129478950214858267931117821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172638600286477690574823761 129478950214858267931117821)
      ·
        refine ⟨48554606330571850474169183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129478950214858267931117821 48554606330571850474169183)
        ·
          refine ⟨72831909495857775711253775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48554606330571850474169183 72831909495857775711253775)
          ·
            refine ⟨109247864243786663566880663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72831909495857775711253775 109247864243786663566880663)
            ·
              refine ⟨163871796365679995350320995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109247864243786663566880663 163871796365679995350320995)
              ·
                refine ⟨245807694548519993025481493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163871796365679995350320995 245807694548519993025481493)
                ·
                  refine ⟨11522235681961874673069445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 245807694548519993025481493 11522235681961874673069445)
                  ·
                    refine ⟨2160419190367851501200521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11522235681961874673069445 2160419190367851501200521)
                    ·
                      refine ⟨1620314392775888625900391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160419190367851501200521 1620314392775888625900391)
                      ·
                        rfl

theorem cell23_3155551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_3155551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155551 prefixEnd_3155551 := by exact prefixLift 3155551
  have htrace : WordTrace (prefixWord ++ tailWord_3155551) baseStart_3155551 baseEnd_3155551 := by
    simpa [prefixWord, tailWord_3155551, baseEnd_3155551] using wordTrace_append hprefix tailTrace_3155551
  have hstable : (prefixWord ++ tailWord_3155551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155551).length < 2 ^ (prefixWord ++ tailWord_3155551).sum := by decide
  have hdescent : baseEnd_3155551 < baseStart_3155551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155564 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_3155564 : Nat := 118140960795 + 3155564 * 2 ^ 59
def prefixEnd_3155564 : Nat := 4983230072969 + 3 ^ 40 * 3155564 * 2
def baseEnd_3155564 : Nat := 1620321068024397075037831

theorem tailTrace_3155564 : CollatzResearch.WordTrace tailWord_3155564 prefixEnd_3155564 1620321068024397075037831 := by
  unfold tailWord_3155564
  simp only [CollatzResearch.WordTrace]
  refine ⟨57546437169969015135052873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76728582893292020180070497 57546437169969015135052873)
  ·
    refine ⟨43159827877476761351289655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57546437169969015135052873 43159827877476761351289655)
    ·
      refine ⟨64739741816215142026934483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43159827877476761351289655 64739741816215142026934483)
      ·
        refine ⟨97109612724322713040401725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64739741816215142026934483 97109612724322713040401725)
        ·
          refine ⟨36416104771621017390150647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97109612724322713040401725 36416104771621017390150647)
          ·
            refine ⟨54624157157431526085225971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36416104771621017390150647 54624157157431526085225971)
            ·
              refine ⟨81936235736147289127838957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54624157157431526085225971 81936235736147289127838957)
              ·
                refine ⟨30726088401055233422939609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81936235736147289127838957 30726088401055233422939609)
                ·
                  refine ⟨23044566300791425067204707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30726088401055233422939609 23044566300791425067204707)
                  ·
                    refine ⟨34566849451187137600807061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23044566300791425067204707 34566849451187137600807061)
                    ·
                      refine ⟨1620321068024397075037831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34566849451187137600807061 1620321068024397075037831)
                      ·
                        rfl

theorem cell23_3155564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_3155564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155564 prefixEnd_3155564 := by exact prefixLift 3155564
  have htrace : WordTrace (prefixWord ++ tailWord_3155564) baseStart_3155564 baseEnd_3155564 := by
    simpa [prefixWord, tailWord_3155564, baseEnd_3155564] using wordTrace_append hprefix tailTrace_3155564
  have hstable : (prefixWord ++ tailWord_3155564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155564).length < 2 ^ (prefixWord ++ tailWord_3155564).sum := by decide
  have hdescent : baseEnd_3155564 < baseStart_3155564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155591 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 6]
def baseStart_3155591 : Nat := 118140960795 + 3155591 * 2 ^ 59
def prefixEnd_3155591 : Nat := 4983230072969 + 3 ^ 40 * 3155591 * 2
def baseEnd_3155591 : Nat := 180037214666896496600023

theorem tailTrace_3155591 : CollatzResearch.WordTrace tailWord_3155591 prefixEnd_3155591 180037214666896496600023 := by
  unfold tailWord_3155591
  simp only [CollatzResearch.WordTrace]
  refine ⟨115093859110840213881338627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76729239407226809254225751 115093859110840213881338627)
  ·
    refine ⟨172640788666260320822007941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115093859110840213881338627 172640788666260320822007941)
    ·
      refine ⟨32370147874923810154126489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172640788666260320822007941 32370147874923810154126489)
      ·
        refine ⟨24277610906192857615594867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32370147874923810154126489 24277610906192857615594867)
        ·
          refine ⟨36416416359289286423392301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24277610906192857615594867 36416416359289286423392301)
          ·
            refine ⟨13656156134733482408772113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36416416359289286423392301 13656156134733482408772113)
            ·
              refine ⟨10242117101050111806579085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13656156134733482408772113 10242117101050111806579085)
              ·
                refine ⟨3840793912893791927467157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10242117101050111806579085 3840793912893791927467157)
                ·
                  refine ⟨180037214666896496600023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3840793912893791927467157 180037214666896496600023)
                  ·
                    rfl

theorem cell23_3155591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 6].length) (baseStart_3155591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155591 prefixEnd_3155591 := by exact prefixLift 3155591
  have htrace : WordTrace (prefixWord ++ tailWord_3155591) baseStart_3155591 baseEnd_3155591 := by
    simpa [prefixWord, tailWord_3155591, baseEnd_3155591] using wordTrace_append hprefix tailTrace_3155591
  have hstable : (prefixWord ++ tailWord_3155591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155591).length < 2 ^ (prefixWord ++ tailWord_3155591).sum := by decide
  have hdescent : baseEnd_3155591 < baseStart_3155591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155602 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_3155602 : Nat := 118140960795 + 3155602 * 2 ^ 59
def prefixEnd_3155602 : Nat := 4983230072969 + 3 ^ 40 * 3155602 * 2
def baseEnd_3155602 : Nat := 1620340580289267926362657

theorem tailTrace_3155602 : CollatzResearch.WordTrace tailWord_3155602 prefixEnd_3155602 1620340580289267926362657 := by
  unfold tailWord_3155602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28773565078450090689997265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76729506875866908506659373 28773565078450090689997265)
  ·
    refine ⟨21580173808837568017497949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28773565078450090689997265 21580173808837568017497949)
    ·
      refine ⟨8092565178314088006561731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21580173808837568017497949 8092565178314088006561731)
      ·
        refine ⟨12138847767471132009842597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8092565178314088006561731 12138847767471132009842597)
        ·
          refine ⟨2276033956400837251845487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12138847767471132009842597 2276033956400837251845487)
          ·
            refine ⟨3414050934601255877768231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276033956400837251845487 3414050934601255877768231)
            ·
              refine ⟨5121076401901883816652347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3414050934601255877768231 5121076401901883816652347)
              ·
                refine ⟨7681614602852825724978521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121076401901883816652347 7681614602852825724978521)
                ·
                  refine ⟨5761210952139619293733891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7681614602852825724978521 5761210952139619293733891)
                  ·
                    refine ⟨8641816428209428940600837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5761210952139619293733891 8641816428209428940600837)
                    ·
                      refine ⟨1620340580289267926362657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8641816428209428940600837 1620340580289267926362657)
                      ·
                        rfl

theorem cell23_3155602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_3155602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155602 prefixEnd_3155602 := by exact prefixLift 3155602
  have htrace : WordTrace (prefixWord ++ tailWord_3155602) baseStart_3155602 baseEnd_3155602 := by
    simpa [prefixWord, tailWord_3155602, baseEnd_3155602] using wordTrace_append hprefix tailTrace_3155602
  have hstable : (prefixWord ++ tailWord_3155602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155602).length < 2 ^ (prefixWord ++ tailWord_3155602).sum := by decide
  have hdescent : baseEnd_3155602 < baseStart_3155602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155612 : List Nat := [2, 2, 3, 2, 3, 1, 2, 3, 1, 4]
def baseStart_3155612 : Nat := 118140960795 + 3155612 * 2 ^ 59
def prefixEnd_3155612 : Nat := 4983230072969 + 3 ^ 40 * 3155612 * 2
def baseEnd_3155612 : Nat := 540115238365270962412537

theorem tailTrace_3155612 : CollatzResearch.WordTrace tailWord_3155612 prefixEnd_3155612 540115238365270962412537 := by
  unfold tailWord_3155612
  simp only [CollatzResearch.WordTrace]
  refine ⟨57547312521882067233926545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76729750029176089645235393 57547312521882067233926545)
  ·
    refine ⟨43160484391411550425444909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57547312521882067233926545 43160484391411550425444909)
    ·
      refine ⟨16185181646779331409541841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43160484391411550425444909 16185181646779331409541841)
      ·
        refine ⟨12138886235084498557156381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16185181646779331409541841 12138886235084498557156381)
        ·
          refine ⟨4552082338156686958933643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12138886235084498557156381 4552082338156686958933643)
          ·
            refine ⟨6828123507235030438400465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552082338156686958933643 6828123507235030438400465)
            ·
              refine ⟨5121092630426272828800349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6828123507235030438400465 5121092630426272828800349)
              ·
                refine ⟨1920409736409852310800131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5121092630426272828800349 1920409736409852310800131)
                ·
                  refine ⟨2880614604614778466200197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920409736409852310800131 2880614604614778466200197)
                  ·
                    refine ⟨540115238365270962412537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2880614604614778466200197 540115238365270962412537)
                    ·
                      rfl

theorem cell23_3155612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_3155612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155612 prefixEnd_3155612 := by exact prefixLift 3155612
  have htrace : WordTrace (prefixWord ++ tailWord_3155612) baseStart_3155612 baseEnd_3155612 := by
    simpa [prefixWord, tailWord_3155612, baseEnd_3155612] using wordTrace_append hprefix tailTrace_3155612
  have hstable : (prefixWord ++ tailWord_3155612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155612).length < 2 ^ (prefixWord ++ tailWord_3155612).sum := by decide
  have hdescent : baseEnd_3155612 < baseStart_3155612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155635 : List Nat := [1, 1, 1, 2, 3, 3, 1, 6, 1, 1, 3]
def baseStart_3155635 : Nat := 118140960795 + 3155635 * 2 ^ 59
def prefixEnd_3155635 : Nat := 4983230072969 + 3 ^ 40 * 3155635 * 2
def baseEnd_3155635 : Nat := 1620357525150866297250005

theorem tailTrace_3155635 : CollatzResearch.WordTrace tailWord_3155635 prefixEnd_3155635 1620357525150866297250005 := by
  unfold tailWord_3155635
  simp only [CollatzResearch.WordTrace]
  refine ⟨115095463922680809395940359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76730309281787206263960239 115095463922680809395940359)
  ·
    refine ⟨172643195884021214093910539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115095463922680809395940359 172643195884021214093910539)
    ·
      refine ⟨258964793826031821140865809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172643195884021214093910539 258964793826031821140865809)
      ·
        refine ⟨194223595369523865855649357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258964793826031821140865809 194223595369523865855649357)
        ·
          refine ⟨72833848263571449695868509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194223595369523865855649357 72833848263571449695868509)
          ·
            refine ⟨27312693098839293635950691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72833848263571449695868509 27312693098839293635950691)
            ·
              refine ⟨40969039648258940453926037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27312693098839293635950691 40969039648258940453926037)
              ·
                refine ⟨1920423733512137833777783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40969039648258940453926037 1920423733512137833777783)
                ·
                  refine ⟨2880635600268206750666675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920423733512137833777783 2880635600268206750666675)
                  ·
                    refine ⟨4320953400402310126000013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2880635600268206750666675 4320953400402310126000013)
                    ·
                      refine ⟨1620357525150866297250005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4320953400402310126000013 1620357525150866297250005)
                      ·
                        rfl

theorem cell23_3155635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 1, 1, 3].length) (baseStart_3155635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155635 prefixEnd_3155635 := by exact prefixLift 3155635
  have htrace : WordTrace (prefixWord ++ tailWord_3155635) baseStart_3155635 baseEnd_3155635 := by
    simpa [prefixWord, tailWord_3155635, baseEnd_3155635] using wordTrace_append hprefix tailTrace_3155635
  have hstable : (prefixWord ++ tailWord_3155635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155635).length < 2 ^ (prefixWord ++ tailWord_3155635).sum := by decide
  have hdescent : baseEnd_3155635 < baseStart_3155635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155641 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3155641 : Nat := 118140960795 + 3155641 * 2 ^ 59
def prefixEnd_3155641 : Nat := 4983230072969 + 3 ^ 40 * 3155641 * 2
def baseEnd_3155641 : Nat := 1620360606034793273774977

theorem tailTrace_3155641 : CollatzResearch.WordTrace tailWord_3155641 prefixEnd_3155641 1620360606034793273774977 := by
  unfold tailWord_3155641
  simp only [CollatzResearch.WordTrace]
  refine ⟨115095682760659072420658777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76730455173772714947105851 115095682760659072420658777)
  ·
    refine ⟨86321762070494304315494083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115095682760659072420658777 86321762070494304315494083)
    ·
      refine ⟨129482643105741456473241125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86321762070494304315494083 129482643105741456473241125)
      ·
        refine ⟨24277995582326523088732711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129482643105741456473241125 24277995582326523088732711)
        ·
          refine ⟨36416993373489784633099067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24277995582326523088732711 36416993373489784633099067)
          ·
            refine ⟨54625490060234676949648601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36416993373489784633099067 54625490060234676949648601)
            ·
              refine ⟨40969117545176007712236451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54625490060234676949648601 40969117545176007712236451)
              ·
                refine ⟨61453676317764011568354677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40969117545176007712236451 61453676317764011568354677)
                ·
                  refine ⟨5761282154790376084533251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61453676317764011568354677 5761282154790376084533251)
                  ·
                    refine ⟨8641923232185564126799877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5761282154790376084533251 8641923232185564126799877)
                    ·
                      refine ⟨1620360606034793273774977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8641923232185564126799877 1620360606034793273774977)
                      ·
                        rfl

theorem cell23_3155641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3155641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155641 prefixEnd_3155641 := by exact prefixLift 3155641
  have htrace : WordTrace (prefixWord ++ tailWord_3155641) baseStart_3155641 baseEnd_3155641 := by
    simpa [prefixWord, tailWord_3155641, baseEnd_3155641] using wordTrace_append hprefix tailTrace_3155641
  have hstable : (prefixWord ++ tailWord_3155641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155641).length < 2 ^ (prefixWord ++ tailWord_3155641).sum := by decide
  have hdescent : baseEnd_3155641 < baseStart_3155641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155671 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_3155671 : Nat := 118140960795 + 3155671 * 2 ^ 59
def prefixEnd_3155671 : Nat := 4983230072969 + 3 ^ 40 * 3155671 * 2
def baseEnd_3155671 : Nat := 1620376010454428156399839

theorem tailTrace_3155671 : CollatzResearch.WordTrace tailWord_3155671 prefixEnd_3155671 1620376010454428156399839 := by
  unfold tailWord_3155671
  simp only [CollatzResearch.WordTrace]
  refine ⟨115096776950550387544250867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76731184633700258362833911 115096776950550387544250867)
  ·
    refine ⟨172645165425825581316376301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115096776950550387544250867 172645165425825581316376301)
    ·
      refine ⟨64741937034684592993641113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172645165425825581316376301 64741937034684592993641113)
      ·
        refine ⟨48556452776013444745230835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64741937034684592993641113 48556452776013444745230835)
        ·
          refine ⟨72834679164020167117846253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48556452776013444745230835 72834679164020167117846253)
          ·
            refine ⟨27313004686507562669192345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72834679164020167117846253 27313004686507562669192345)
            ·
              refine ⟨20484753514880672001894259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27313004686507562669192345 20484753514880672001894259)
              ·
                refine ⟨30727130272321008002841389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20484753514880672001894259 30727130272321008002841389)
                ·
                  refine ⟨11522673852120378001065521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30727130272321008002841389 11522673852120378001065521)
                  ·
                    refine ⟨8642005389090283500799141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11522673852120378001065521 8642005389090283500799141)
                    ·
                      refine ⟨1620376010454428156399839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8642005389090283500799141 1620376010454428156399839)
                      ·
                        rfl

theorem cell23_3155671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_3155671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155671 prefixEnd_3155671 := by exact prefixLift 3155671
  have htrace : WordTrace (prefixWord ++ tailWord_3155671) baseStart_3155671 baseEnd_3155671 := by
    simpa [prefixWord, tailWord_3155671, baseEnd_3155671] using wordTrace_append hprefix tailTrace_3155671
  have hstable : (prefixWord ++ tailWord_3155671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155671).length < 2 ^ (prefixWord ++ tailWord_3155671).sum := by decide
  have hdescent : baseEnd_3155671 < baseStart_3155671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155692 : List Nat := [2, 2, 1, 1, 2, 2, 2, 6, 1, 2, 2]
def baseStart_3155692 : Nat := 118140960795 + 3155692 * 2 ^ 59
def prefixEnd_3155692 : Nat := 4983230072969 + 3 ^ 40 * 3155692 * 2
def baseEnd_3155692 : Nat := 1620386793548172574237243

theorem tailTrace_3155692 : CollatzResearch.WordTrace tailWord_3155692 prefixEnd_3155692 1620386793548172574237243 := by
  unfold tailWord_3155692
  simp only [CollatzResearch.WordTrace]
  refine ⟨57548771441737154065382665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76731695255649538753843553 57548771441737154065382665)
  ·
    refine ⟨43161578581302865549036999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57548771441737154065382665 43161578581302865549036999)
    ·
      refine ⟨64742367871954298323555499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43161578581302865549036999 64742367871954298323555499)
      ·
        refine ⟨97113551807931447485333249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64742367871954298323555499 97113551807931447485333249)
        ·
          refine ⟨72835163855948585613999937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97113551807931447485333249 72835163855948585613999937)
          ·
            refine ⟨54626372891961439210499953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72835163855948585613999937 54626372891961439210499953)
            ·
              refine ⟨40969779668971079407874965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54626372891961439210499953 40969779668971079407874965)
              ·
                refine ⟨1920458421983019347244139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40969779668971079407874965 1920458421983019347244139)
                ·
                  refine ⟨2880687632974529020866209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920458421983019347244139 2880687632974529020866209)
                  ·
                    refine ⟨2160515724730896765649657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2880687632974529020866209 2160515724730896765649657)
                    ·
                      refine ⟨1620386793548172574237243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160515724730896765649657 1620386793548172574237243)
                      ·
                        rfl

theorem cell23_3155692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 1, 2, 2].length) (baseStart_3155692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155692 prefixEnd_3155692 := by exact prefixLift 3155692
  have htrace : WordTrace (prefixWord ++ tailWord_3155692) baseStart_3155692 baseEnd_3155692 := by
    simpa [prefixWord, tailWord_3155692, baseEnd_3155692] using wordTrace_append hprefix tailTrace_3155692
  have hstable : (prefixWord ++ tailWord_3155692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155692).length < 2 ^ (prefixWord ++ tailWord_3155692).sum := by decide
  have hdescent : baseEnd_3155692 < baseStart_3155692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155702 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_3155702 : Nat := 118140960795 + 3155702 * 2 ^ 59
def prefixEnd_3155702 : Nat := 4983230072969 + 3 ^ 40 * 3155702 * 2
def baseEnd_3155702 : Nat := 540130642784905845037399

theorem tailTrace_3155702 : CollatzResearch.WordTrace tailWord_3155702 prefixEnd_3155702 540130642784905845037399 := by
  unfold tailWord_3155702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7193619225839879989914335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76731938408958719892419573 7193619225839879989914335)
  ·
    refine ⟨10790428838759819984871503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7193619225839879989914335 10790428838759819984871503)
    ·
      refine ⟨16185643258139729977307255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10790428838759819984871503 16185643258139729977307255)
      ·
        refine ⟨24278464887209594965960883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16185643258139729977307255 24278464887209594965960883)
        ·
          refine ⟨36417697330814392448941325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24278464887209594965960883 36417697330814392448941325)
          ·
            refine ⟨13656636499055397168352997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36417697330814392448941325 13656636499055397168352997)
            ·
              refine ⟨2560619343572886969066187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13656636499055397168352997 2560619343572886969066187)
              ·
                refine ⟨3840929015359330453599281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560619343572886969066187 3840929015359330453599281)
                ·
                  refine ⟨2880696761519497840199461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3840929015359330453599281 2880696761519497840199461)
                  ·
                    refine ⟨540130642784905845037399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2880696761519497840199461 540130642784905845037399)
                    ·
                      rfl

theorem cell23_3155702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_3155702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155702 prefixEnd_3155702 := by exact prefixLift 3155702
  have htrace : WordTrace (prefixWord ++ tailWord_3155702) baseStart_3155702 baseEnd_3155702 := by
    simpa [prefixWord, tailWord_3155702, baseEnd_3155702] using wordTrace_append hprefix tailTrace_3155702
  have hstable : (prefixWord ++ tailWord_3155702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155702).length < 2 ^ (prefixWord ++ tailWord_3155702).sum := by decide
  have hdescent : baseEnd_3155702 < baseStart_3155702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155708 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_3155708 : Nat := 118140960795 + 3155708 * 2 ^ 59
def prefixEnd_3155708 : Nat := 4983230072969 + 3 ^ 40 * 3155708 * 2
def baseEnd_3155708 : Nat := 1620395009238644511637169

theorem tailTrace_3155708 : CollatzResearch.WordTrace tailWord_3155708 prefixEnd_3155708 1620395009238644511637169 := by
  unfold tailWord_3155708
  simp only [CollatzResearch.WordTrace]
  refine ⟨57549063225708171431673889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76732084300944228575565185 57549063225708171431673889)
  ·
    refine ⟨43161797419281128573755417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57549063225708171431673889 43161797419281128573755417)
    ·
      refine ⟨32371348064460846430316563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43161797419281128573755417 32371348064460846430316563)
      ·
        refine ⟨48557022096691269645474845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32371348064460846430316563 48557022096691269645474845)
        ·
          refine ⟨18208883286259226117053067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48557022096691269645474845 18208883286259226117053067)
          ·
            refine ⟨27313324929388839175579601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18208883286259226117053067 27313324929388839175579601)
            ·
              refine ⟨20484993697041629381684701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27313324929388839175579601 20484993697041629381684701)
              ·
                refine ⟨7681872636390611018131763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20484993697041629381684701 7681872636390611018131763)
                ·
                  refine ⟨11522808954585916527197645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7681872636390611018131763 11522808954585916527197645)
                  ·
                    refine ⟨4321053357969718697699117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11522808954585916527197645 4321053357969718697699117)
                    ·
                      refine ⟨1620395009238644511637169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4321053357969718697699117 1620395009238644511637169)
                      ·
                        rfl

theorem cell23_3155708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_3155708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155708 prefixEnd_3155708 := by exact prefixLift 3155708
  have htrace : WordTrace (prefixWord ++ tailWord_3155708) baseStart_3155708 baseEnd_3155708 := by
    simpa [prefixWord, tailWord_3155708, baseEnd_3155708] using wordTrace_append hprefix tailTrace_3155708
  have hstable : (prefixWord ++ tailWord_3155708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155708).length < 2 ^ (prefixWord ++ tailWord_3155708).sum := by decide
  have hdescent : baseEnd_3155708 < baseStart_3155708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155732 : List Nat := [2, 4, 4, 1, 2, 10]
def baseStart_3155732 : Nat := 118140960795 + 3155732 * 2 ^ 59
def prefixEnd_3155732 : Nat := 4983230072969 + 3 ^ 40 * 3155732 * 2
def baseEnd_3155732 : Nat := 6668342933227787727313

theorem tailTrace_3155732 : CollatzResearch.WordTrace tailWord_3155732 prefixEnd_3155732 6668342933227787727313 := by
  unfold tailWord_3155732
  simp only [CollatzResearch.WordTrace]
  refine ⟨57549500901664697481110725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76732667868886263308147633 57549500901664697481110725)
  ·
    refine ⟨10790531419062130777708261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57549500901664697481110725 10790531419062130777708261)
    ·
      refine ⟨2023224641074149520820299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10790531419062130777708261 2023224641074149520820299)
      ·
        refine ⟨3034836961611224281230449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023224641074149520820299 3034836961611224281230449)
        ·
          refine ⟨2276127721208418210922837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3034836961611224281230449 2276127721208418210922837)
          ·
            refine ⟨6668342933227787727313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2276127721208418210922837 6668342933227787727313)
            ·
              rfl

theorem cell23_3155732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 10].length) (baseStart_3155732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155732 prefixEnd_3155732 := by exact prefixLift 3155732
  have htrace : WordTrace (prefixWord ++ tailWord_3155732) baseStart_3155732 baseEnd_3155732 := by
    simpa [prefixWord, tailWord_3155732, baseEnd_3155732] using wordTrace_append hprefix tailTrace_3155732
  have hstable : (prefixWord ++ tailWord_3155732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155732).length < 2 ^ (prefixWord ++ tailWord_3155732).sum := by decide
  have hdescent : baseEnd_3155732 < baseStart_3155732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155748 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3155748 : Nat := 118140960795 + 3155748 * 2 ^ 59
def prefixEnd_3155748 : Nat := 4983230072969 + 3 ^ 40 * 3155748 * 2
def baseEnd_3155748 : Nat := 1620415548464824355136985

theorem tailTrace_3155748 : CollatzResearch.WordTrace tailWord_3155748 prefixEnd_3155748 1620415548464824355136985 := by
  unfold tailWord_3155748
  simp only [CollatzResearch.WordTrace]
  refine ⟨57549792685635714847401949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76733056914180953129869265 57549792685635714847401949)
  ·
    refine ⟨21581172257113393067775731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57549792685635714847401949 21581172257113393067775731)
    ·
      refine ⟨32371758385670089601663597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21581172257113393067775731 32371758385670089601663597)
      ·
        refine ⟨12139409394626283600623849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32371758385670089601663597 12139409394626283600623849)
        ·
          refine ⟨9104557045969712700467887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12139409394626283600623849 9104557045969712700467887)
          ·
            refine ⟨13656835568954569050701831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9104557045969712700467887 13656835568954569050701831)
            ·
              refine ⟨20485253353431853576052747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13656835568954569050701831 20485253353431853576052747)
              ·
                refine ⟨30727880030147780364079121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20485253353431853576052747 30727880030147780364079121)
                ·
                  refine ⟨23045910022610835273059341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30727880030147780364079121 23045910022610835273059341)
                  ·
                    refine ⟨8642216258479063227397253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23045910022610835273059341 8642216258479063227397253)
                    ·
                      refine ⟨1620415548464824355136985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8642216258479063227397253 1620415548464824355136985)
                      ·
                        rfl

theorem cell23_3155748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3155748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155748 prefixEnd_3155748 := by exact prefixLift 3155748
  have htrace : WordTrace (prefixWord ++ tailWord_3155748) baseStart_3155748 baseEnd_3155748 := by
    simpa [prefixWord, tailWord_3155748, baseEnd_3155748] using wordTrace_append hprefix tailTrace_3155748
  have hstable : (prefixWord ++ tailWord_3155748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155748).length < 2 ^ (prefixWord ++ tailWord_3155748).sum := by decide
  have hdescent : baseEnd_3155748 < baseStart_3155748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155865 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 3, 4]
def baseStart_3155865 : Nat := 118140960795 + 3155865 * 2 ^ 59
def prefixEnd_3155865 : Nat := 4983230072969 + 3 ^ 40 * 3155865 * 2
def baseEnd_3155865 : Nat := 540158541900466799124649

theorem tailTrace_3155865 : CollatzResearch.WordTrace tailWord_3155865 prefixEnd_3155865 540158541900466799124649 := by
  unfold tailWord_3155865
  simp only [CollatzResearch.WordTrace]
  refine ⟨115103852711847558676813049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76735901807898372451208699 115103852711847558676813049)
  ·
    refine ⟨86327889533885669007609787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115103852711847558676813049 86327889533885669007609787)
    ·
      refine ⟨129491834300828503511414681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86327889533885669007609787 129491834300828503511414681)
      ·
        refine ⟨97118875725621377633561011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129491834300828503511414681 97118875725621377633561011)
        ·
          refine ⟨145678313588432066450341517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97118875725621377633561011 145678313588432066450341517)
          ·
            refine ⟨54629367595662024918878069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145678313588432066450341517 54629367595662024918878069)
            ·
              refine ⟨5121503212093314836144819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54629367595662024918878069 5121503212093314836144819)
              ·
                refine ⟨7682254818139972254217229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121503212093314836144819 7682254818139972254217229)
                ·
                  refine ⟨2880845556802489595331461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7682254818139972254217229 2880845556802489595331461)
                  ·
                    refine ⟨540158541900466799124649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2880845556802489595331461 540158541900466799124649)
                    ·
                      rfl

theorem cell23_3155865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 4].length) (baseStart_3155865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155865 prefixEnd_3155865 := by exact prefixLift 3155865
  have htrace : WordTrace (prefixWord ++ tailWord_3155865) baseStart_3155865 baseEnd_3155865 := by
    simpa [prefixWord, tailWord_3155865, baseEnd_3155865] using wordTrace_append hprefix tailTrace_3155865
  have hstable : (prefixWord ++ tailWord_3155865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155865).length < 2 ^ (prefixWord ++ tailWord_3155865).sum := by decide
  have hdescent : baseEnd_3155865 < baseStart_3155865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155886 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3155886 : Nat := 118140960795 + 3155886 * 2 ^ 59
def prefixEnd_3155886 : Nat := 4983230072969 + 3 ^ 40 * 3155886 * 2
def baseEnd_3155886 : Nat := 540162136265048271737117

theorem tailTrace_3155886 : CollatzResearch.WordTrace tailWord_3155886 prefixEnd_3155886 540162136265048271737117 := by
  unfold tailWord_3155886
  simp only [CollatzResearch.WordTrace]
  refine ⟨14388077330596434907915939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76736412429847652842218341 14388077330596434907915939)
  ·
    refine ⟨21582115995894652361873909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14388077330596434907915939 21582115995894652361873909)
    ·
      refine ⟨2023323374615123658925679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21582115995894652361873909 2023323374615123658925679)
      ·
        refine ⟨3034985061922685488388519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023323374615123658925679 3034985061922685488388519)
        ·
          refine ⟨4552477592884028232582779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034985061922685488388519 4552477592884028232582779)
          ·
            refine ⟨6828716389326042348874169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552477592884028232582779 6828716389326042348874169)
            ·
              refine ⟨5121537291994531761655627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6828716389326042348874169 5121537291994531761655627)
              ·
                refine ⟨7682305937991797642483441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121537291994531761655627 7682305937991797642483441)
                ·
                  refine ⟨5761729453493848231862581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7682305937991797642483441 5761729453493848231862581)
                  ·
                    refine ⟨540162136265048271737117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5761729453493848231862581 540162136265048271737117)
                    ·
                      rfl

theorem cell23_3155886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3155886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155886 prefixEnd_3155886 := by exact prefixLift 3155886
  have htrace : WordTrace (prefixWord ++ tailWord_3155886) baseStart_3155886 baseEnd_3155886 := by
    simpa [prefixWord, tailWord_3155886, baseEnd_3155886] using wordTrace_append hprefix tailTrace_3155886
  have hstable : (prefixWord ++ tailWord_3155886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155886).length < 2 ^ (prefixWord ++ tailWord_3155886).sum := by decide
  have hdescent : baseEnd_3155886 < baseStart_3155886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155916 : List Nat := [2, 2, 1, 4, 1, 4, 2, 2, 1, 4]
def baseStart_3155916 : Nat := 118140960795 + 3155916 * 2 ^ 59
def prefixEnd_3155916 : Nat := 4983230072969 + 3 ^ 40 * 3155916 * 2
def baseEnd_3155916 : Nat := 540167271071593232612071

theorem tailTrace_3155916 : CollatzResearch.WordTrace tailWord_3155916 prefixEnd_3155916 540167271071593232612071 := by
  unfold tailWord_3155916
  simp only [CollatzResearch.WordTrace]
  refine ⟨57552856417331397193459801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76737141889775196257946401 57552856417331397193459801)
  ·
    refine ⟨43164642312998547895094851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57552856417331397193459801 43164642312998547895094851)
    ·
      refine ⟨64746963469497821842642277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43164642312998547895094851 64746963469497821842642277)
      ·
        refine ⟨12140055650530841595495427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64746963469497821842642277 12140055650530841595495427)
        ·
          refine ⟨18210083475796262393243141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12140055650530841595495427 18210083475796262393243141)
          ·
            refine ⟨3414390651711799198733089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18210083475796262393243141 3414390651711799198733089)
            ·
              refine ⟨2560792988783849399049817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3414390651711799198733089 2560792988783849399049817)
              ·
                refine ⟨1920594741587887049287363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2560792988783849399049817 1920594741587887049287363)
                ·
                  refine ⟨2880892112381830573931045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920594741587887049287363 2880892112381830573931045)
                  ·
                    refine ⟨540167271071593232612071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2880892112381830573931045 540167271071593232612071)
                    ·
                      rfl

theorem cell23_3155916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_3155916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155916 prefixEnd_3155916 := by exact prefixLift 3155916
  have htrace : WordTrace (prefixWord ++ tailWord_3155916) baseStart_3155916 baseEnd_3155916 := by
    simpa [prefixWord, tailWord_3155916, baseEnd_3155916] using wordTrace_append hprefix tailTrace_3155916
  have hstable : (prefixWord ++ tailWord_3155916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155916).length < 2 ^ (prefixWord ++ tailWord_3155916).sum := by decide
  have hdescent : baseEnd_3155916 < baseStart_3155916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155925 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_3155925 : Nat := 118140960795 + 3155925 * 2 ^ 59
def prefixEnd_3155925 : Nat := 4983230072969 + 3 ^ 40 * 3155925 * 2
def baseEnd_3155925 : Nat := 540168811513556720874557

theorem tailTrace_3155925 : CollatzResearch.WordTrace tailWord_3155925 prefixEnd_3155925 540168811513556720874557 := by
  unfold tailWord_3155925
  simp only [CollatzResearch.WordTrace]
  refine ⟨115106041091630188923997229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76737360727753459282664819 115106041091630188923997229)
  ·
    refine ⟨43164765409361320846498961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115106041091630188923997229 43164765409361320846498961)
    ·
      refine ⟨32373574057020990634874221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43164765409361320846498961 32373574057020990634874221)
      ·
        refine ⟨12140090271382871488077833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32373574057020990634874221 12140090271382871488077833)
        ·
          refine ⟨9105067703537153616058375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12140090271382871488077833 9105067703537153616058375)
          ·
            refine ⟨13657601555305730424087563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9105067703537153616058375 13657601555305730424087563)
            ·
              refine ⟨20486402332958595636131345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13657601555305730424087563 20486402332958595636131345)
              ·
                refine ⟨15364801749718946727098509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20486402332958595636131345 15364801749718946727098509)
                ·
                  refine ⟨5761800656144605022661941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15364801749718946727098509 5761800656144605022661941)
                  ·
                    refine ⟨540168811513556720874557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5761800656144605022661941 540168811513556720874557)
                    ·
                      rfl

theorem cell23_3155925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_3155925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155925 prefixEnd_3155925 := by exact prefixLift 3155925
  have htrace : WordTrace (prefixWord ++ tailWord_3155925) baseStart_3155925 baseEnd_3155925 := by
    simpa [prefixWord, tailWord_3155925, baseEnd_3155925] using wordTrace_append hprefix tailTrace_3155925
  have hstable : (prefixWord ++ tailWord_3155925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155925).length < 2 ^ (prefixWord ++ tailWord_3155925).sum := by decide
  have hdescent : baseEnd_3155925 < baseStart_3155925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155979 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 3, 2, 2]
def baseStart_3155979 : Nat := 118140960795 + 3155979 * 2 ^ 59
def prefixEnd_3155979 : Nat := 4983230072969 + 3 ^ 40 * 3155979 * 2
def baseEnd_3155979 : Nat := 1620534162496012951348423

theorem tailTrace_3155979 : CollatzResearch.WordTrace tailWord_3155979 prefixEnd_3155979 1620534162496012951348423 := by
  unfold tailWord_3155979
  simp only [CollatzResearch.WordTrace]
  refine ⟨115108010633434556146462991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76738673755623037430975327 115108010633434556146462991)
  ·
    refine ⟨172662015950151834219694487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115108010633434556146462991 172662015950151834219694487)
    ·
      refine ⟨258993023925227751329541731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172662015950151834219694487 258993023925227751329541731)
      ·
        refine ⟨388489535887841626994312597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258993023925227751329541731 388489535887841626994312597)
        ·
          refine ⟨18210446994742576265358403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 388489535887841626994312597 18210446994742576265358403)
          ·
            refine ⟨27315670492113864398037605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18210446994742576265358403 27315670492113864398037605)
            ·
              refine ⟨5121688217271349574632051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27315670492113864398037605 5121688217271349574632051)
              ·
                refine ⟨7682532325907024361948077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121688217271349574632051 7682532325907024361948077)
                ·
                  refine ⟨2880949622215134135730529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7682532325907024361948077 2880949622215134135730529)
                  ·
                    refine ⟨2160712216661350601797897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2880949622215134135730529 2160712216661350601797897)
                    ·
                      refine ⟨1620534162496012951348423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160712216661350601797897 1620534162496012951348423)
                      ·
                        rfl

theorem cell23_3155979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 2, 2].length) (baseStart_3155979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155979 prefixEnd_3155979 := by exact prefixLift 3155979
  have htrace : WordTrace (prefixWord ++ tailWord_3155979) baseStart_3155979 baseEnd_3155979 := by
    simpa [prefixWord, tailWord_3155979, baseEnd_3155979] using wordTrace_append hprefix tailTrace_3155979
  have hstable : (prefixWord ++ tailWord_3155979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155979).length < 2 ^ (prefixWord ++ tailWord_3155979).sum := by decide
  have hdescent : baseEnd_3155979 < baseStart_3155979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155989 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 1, 6]
def baseStart_3155989 : Nat := 118140960795 + 3155989 * 2 ^ 59
def prefixEnd_3155989 : Nat := 4983230072969 + 3 ^ 40 * 3155989 * 2
def baseEnd_3155989 : Nat := 540179765767519304074459

theorem tailTrace_3155989 : CollatzResearch.WordTrace tailWord_3155989 prefixEnd_3155989 540179765767519304074459 := by
  unfold tailWord_3155989
  simp only [CollatzResearch.WordTrace]
  refine ⟨115108375363398327854327021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76738916908932218569551347 115108375363398327854327021)
  ·
    refine ⟨43165640761274372945372633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115108375363398327854327021 43165640761274372945372633)
    ·
      refine ⟨32374230570955779709029475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43165640761274372945372633 32374230570955779709029475)
      ·
        refine ⟨48561345856433669563544213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32374230570955779709029475 48561345856433669563544213)
        ·
          refine ⟨2276313087020328260791135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48561345856433669563544213 2276313087020328260791135)
          ·
            refine ⟨3414469630530492391186703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276313087020328260791135 3414469630530492391186703)
            ·
              refine ⟨5121704445795738586780055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3414469630530492391186703 5121704445795738586780055)
              ·
                refine ⟨7682556668693607880170083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121704445795738586780055 7682556668693607880170083)
                ·
                  refine ⟨11523835003040411820255125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682556668693607880170083 11523835003040411820255125)
                  ·
                    refine ⟨540179765767519304074459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11523835003040411820255125 540179765767519304074459)
                    ·
                      rfl

theorem cell23_3155989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_3155989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155989 prefixEnd_3155989 := by exact prefixLift 3155989
  have htrace : WordTrace (prefixWord ++ tailWord_3155989) baseStart_3155989 baseEnd_3155989 := by
    simpa [prefixWord, tailWord_3155989, baseEnd_3155989] using wordTrace_append hprefix tailTrace_3155989
  have hstable : (prefixWord ++ tailWord_3155989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155989).length < 2 ^ (prefixWord ++ tailWord_3155989).sum := by decide
  have hdescent : baseEnd_3155989 < baseStart_3155989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155995 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 3]
def baseStart_3155995 : Nat := 118140960795 + 3155995 * 2 ^ 59
def prefixEnd_3155995 : Nat := 4983230072969 + 3 ^ 40 * 3155995 * 2
def baseEnd_3155995 : Nat := 1620542378186484888748349

theorem tailTrace_3155995 : CollatzResearch.WordTrace tailWord_3155995 prefixEnd_3155995 1620542378186484888748349 := by
  unfold tailWord_3155995
  simp only [CollatzResearch.WordTrace]
  refine ⟨115108594201376590879045439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76739062800917727252696959 115108594201376590879045439)
  ·
    refine ⟨172662891302064886318568159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115108594201376590879045439 172662891302064886318568159)
    ·
      refine ⟨258994336953097329477852239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172662891302064886318568159 258994336953097329477852239)
      ·
        refine ⟨388491505429645994216778359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258994336953097329477852239 388491505429645994216778359)
        ·
          refine ⟨582737258144468991325167539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388491505429645994216778359 582737258144468991325167539)
          ·
            refine ⟨874105887216703486987751309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582737258144468991325167539 874105887216703486987751309)
            ·
              refine ⟨327789707706263807620406741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 874105887216703486987751309 327789707706263807620406741)
              ·
                refine ⟨7682571274365557991103283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 327789707706263807620406741 7682571274365557991103283)
                ·
                  refine ⟨11523856911548336986654925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682571274365557991103283 11523856911548336986654925)
                  ·
                    refine ⟨4321446341830626369995597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11523856911548336986654925 4321446341830626369995597)
                    ·
                      refine ⟨1620542378186484888748349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4321446341830626369995597 1620542378186484888748349)
                      ·
                        rfl

theorem cell23_3155995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 3].length) (baseStart_3155995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3155995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3155995 prefixEnd_3155995 := by exact prefixLift 3155995
  have htrace : WordTrace (prefixWord ++ tailWord_3155995) baseStart_3155995 baseEnd_3155995 := by
    simpa [prefixWord, tailWord_3155995, baseEnd_3155995] using wordTrace_append hprefix tailTrace_3155995
  have hstable : (prefixWord ++ tailWord_3155995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155995).length < 2 ^ (prefixWord ++ tailWord_3155995).sum := by decide
  have hdescent : baseEnd_3155995 < baseStart_3155995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156029 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_3156029 : Nat := 118140960795 + 3156029 * 2 ^ 59
def prefixEnd_3156029 : Nat := 4983230072969 + 3 ^ 40 * 3156029 * 2
def baseEnd_3156029 : Nat := 1620559836528737755723193

theorem tailTrace_3156029 : CollatzResearch.WordTrace tailWord_3156029 prefixEnd_3156029 1620559836528737755723193 := by
  unfold tailWord_3156029
  simp only [CollatzResearch.WordTrace]
  refine ⟨115109834283253414685783141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76739889522168943123855427 115109834283253414685783141)
  ·
    refine ⟨21583093928110015253584339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115109834283253414685783141 21583093928110015253584339)
    ·
      refine ⟨32374640892165022880376509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21583093928110015253584339 32374640892165022880376509)
      ·
        refine ⟨12140490334561883580141191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32374640892165022880376509 12140490334561883580141191)
        ·
          refine ⟨18210735501842825370211787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12140490334561883580141191 18210735501842825370211787)
          ·
            refine ⟨27316103252764238055317681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18210735501842825370211787 27316103252764238055317681)
            ·
              refine ⟨20487077439573178541488261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27316103252764238055317681 20487077439573178541488261)
              ·
                refine ⟨3841327019919970976529049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20487077439573178541488261 3841327019919970976529049)
                ·
                  refine ⟨2880995264939978232396787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3841327019919970976529049 2880995264939978232396787)
                  ·
                    refine ⟨4321492897409967348595181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2880995264939978232396787 4321492897409967348595181)
                    ·
                      refine ⟨1620559836528737755723193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4321492897409967348595181 1620559836528737755723193)
                      ·
                        rfl

theorem cell23_3156029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_3156029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156029 prefixEnd_3156029 := by exact prefixLift 3156029
  have htrace : WordTrace (prefixWord ++ tailWord_3156029) baseStart_3156029 baseEnd_3156029 := by
    simpa [prefixWord, tailWord_3156029, baseEnd_3156029] using wordTrace_append hprefix tailTrace_3156029
  have hstable : (prefixWord ++ tailWord_3156029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156029).length < 2 ^ (prefixWord ++ tailWord_3156029).sum := by decide
  have hdescent : baseEnd_3156029 < baseStart_3156029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156030 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_3156030 : Nat := 118140960795 + 3156030 * 2 ^ 59
def prefixEnd_3156030 : Nat := 4983230072969 + 3 ^ 40 * 3156030 * 2
def baseEnd_3156030 : Nat := 1620560350009392251810689

theorem tailTrace_3156030 : CollatzResearch.WordTrace tailWord_3156030 prefixEnd_3156030 1620560350009392251810689 := by
  unfold tailWord_3156030
  simp only [CollatzResearch.WordTrace]
  refine ⟨14388733844531223982071193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76739913837499861237713029 14388733844531223982071193)
  ·
    refine ⟨10791550383398417986553395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14388733844531223982071193 10791550383398417986553395)
    ·
      refine ⟨16187325575097626979830093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10791550383398417986553395 16187325575097626979830093)
      ·
        refine ⟨6070247090661610117436285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16187325575097626979830093 6070247090661610117436285)
        ·
          refine ⟨2276342658998103794038607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6070247090661610117436285 2276342658998103794038607)
          ·
            refine ⟨3414513988497155691057911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276342658998103794038607 3414513988497155691057911)
            ·
              refine ⟨5121770982745733536586867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3414513988497155691057911 5121770982745733536586867)
              ·
                refine ⟨7682656474118600304880301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121770982745733536586867 7682656474118600304880301)
                ·
                  refine ⟨2880996177794475114330113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7682656474118600304880301 2880996177794475114330113)
                  ·
                    refine ⟨2160747133345856335747585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2880996177794475114330113 2160747133345856335747585)
                    ·
                      refine ⟨1620560350009392251810689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160747133345856335747585 1620560350009392251810689)
                      ·
                        rfl

theorem cell23_3156030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_3156030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156030 prefixEnd_3156030 := by exact prefixLift 3156030
  have htrace : WordTrace (prefixWord ++ tailWord_3156030) baseStart_3156030 baseEnd_3156030 := by
    simpa [prefixWord, tailWord_3156030, baseEnd_3156030] using wordTrace_append hprefix tailTrace_3156030
  have hstable : (prefixWord ++ tailWord_3156030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156030).length < 2 ^ (prefixWord ++ tailWord_3156030).sum := by decide
  have hdescent : baseEnd_3156030 < baseStart_3156030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156046 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3]
def baseStart_3156046 : Nat := 118140960795 + 3156046 * 2 ^ 59
def prefixEnd_3156046 : Nat := 4983230072969 + 3 ^ 40 * 3156046 * 2
def baseEnd_3156046 : Nat := 1620568565699864189210615

theorem tailTrace_3156046 : CollatzResearch.WordTrace tailWord_3156046 prefixEnd_3156046 1620568565699864189210615 := by
  unfold tailWord_3156046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14388806790523978323643999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76740302882794551059434661 14388806790523978323643999)
  ·
    refine ⟨21583210185785967485465999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14388806790523978323643999 21583210185785967485465999)
    ·
      refine ⟨32374815278678951228198999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21583210185785967485465999 32374815278678951228198999)
      ·
        refine ⟨48562222918018426842298499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32374815278678951228198999 48562222918018426842298499)
        ·
          refine ⟨72843334377027640263447749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48562222918018426842298499 72843334377027640263447749)
          ·
            refine ⟨13658125195692682549396453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72843334377027640263447749 13658125195692682549396453)
            ·
              refine ⟨2560898474192377978011835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13658125195692682549396453 2560898474192377978011835)
              ·
                refine ⟨3841347711288566967017753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560898474192377978011835 3841347711288566967017753)
                ·
                  refine ⟨2881010783466425225263315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3841347711288566967017753 2881010783466425225263315)
                  ·
                    refine ⟨4321516175199637837894973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2881010783466425225263315 4321516175199637837894973)
                    ·
                      refine ⟨1620568565699864189210615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4321516175199637837894973 1620568565699864189210615)
                      ·
                        rfl

theorem cell23_3156046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_3156046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156046 prefixEnd_3156046 := by exact prefixLift 3156046
  have htrace : WordTrace (prefixWord ++ tailWord_3156046) baseStart_3156046 baseEnd_3156046 := by
    simpa [prefixWord, tailWord_3156046, baseEnd_3156046] using wordTrace_append hprefix tailTrace_3156046
  have hstable : (prefixWord ++ tailWord_3156046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156046).length < 2 ^ (prefixWord ++ tailWord_3156046).sum := by decide
  have hdescent : baseEnd_3156046 < baseStart_3156046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156055 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_3156055 : Nat := 118140960795 + 3156055 * 2 ^ 59
def prefixEnd_3156055 : Nat := 4983230072969 + 3 ^ 40 * 3156055 * 2
def baseEnd_3156055 : Nat := 1620573187025754653998073

theorem tailTrace_3156055 : CollatzResearch.WordTrace tailWord_3156055 prefixEnd_3156055 1620573187025754653998073 := by
  unfold tailWord_3156055
  simp only [CollatzResearch.WordTrace]
  refine ⟨115110782581159221126229619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76740521720772814084153079 115110782581159221126229619)
  ·
    refine ⟨172666173871738831689344429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115110782581159221126229619 172666173871738831689344429)
    ·
      refine ⟨64749815201902061883504161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172666173871738831689344429 64749815201902061883504161)
      ·
        refine ⟨48562361401426546412628121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64749815201902061883504161 48562361401426546412628121)
        ·
          refine ⟨36421771051069909809471091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48562361401426546412628121 36421771051069909809471091)
          ·
            refine ⟨54632656576604864714206637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36421771051069909809471091 54632656576604864714206637)
            ·
              refine ⟨20487246216226824267827489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54632656576604864714206637 20487246216226824267827489)
              ·
                refine ⟨15365434662170118200870617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20487246216226824267827489 15365434662170118200870617)
                ·
                  refine ⟨11524075996627588650652963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15365434662170118200870617 11524075996627588650652963)
                  ·
                    refine ⟨17286113994941382975979445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11524075996627588650652963 17286113994941382975979445)
                    ·
                      refine ⟨1620573187025754653998073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17286113994941382975979445 1620573187025754653998073)
                      ·
                        rfl

theorem cell23_3156055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_3156055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156055 prefixEnd_3156055 := by exact prefixLift 3156055
  have htrace : WordTrace (prefixWord ++ tailWord_3156055) baseStart_3156055 baseEnd_3156055 := by
    simpa [prefixWord, tailWord_3156055, baseEnd_3156055] using wordTrace_append hprefix tailTrace_3156055
  have hstable : (prefixWord ++ tailWord_3156055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156055).length < 2 ^ (prefixWord ++ tailWord_3156055).sum := by decide
  have hdescent : baseEnd_3156055 < baseStart_3156055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156056 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 1, 3, 2]
def baseStart_3156056 : Nat := 118140960795 + 3156056 * 2 ^ 59
def prefixEnd_3156056 : Nat := 4983230072969 + 3 ^ 40 * 3156056 * 2
def baseEnd_3156056 : Nat := 1620573700506409150085569

theorem tailTrace_3156056 : CollatzResearch.WordTrace tailWord_3156056 prefixEnd_3156056 1620573700506409150085569 := by
  unfold tailWord_3156056
  simp only [CollatzResearch.WordTrace]
  refine ⟨57555409527077799148508011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76740546036103732198010681 57555409527077799148508011)
  ·
    refine ⟨86333114290616698722762017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57555409527077799148508011 86333114290616698722762017)
    ·
      refine ⟨64749835717962524042071513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86333114290616698722762017 64749835717962524042071513)
      ·
        refine ⟨48562376788471893031553635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64749835717962524042071513 48562376788471893031553635)
        ·
          refine ⟨72843565182707839547330453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48562376788471893031553635 72843565182707839547330453)
          ·
            refine ⟨3414542117939429978781115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72843565182707839547330453 3414542117939429978781115)
            ·
              refine ⟨5121813176909144968171673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3414542117939429978781115 5121813176909144968171673)
              ·
                refine ⟨3841359882681858726128755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5121813176909144968171673 3841359882681858726128755)
                ·
                  refine ⟨5762039824022788089193133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3841359882681858726128755 5762039824022788089193133)
                  ·
                    refine ⟨2160764934008545533447425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5762039824022788089193133 2160764934008545533447425)
                    ·
                      refine ⟨1620573700506409150085569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160764934008545533447425 1620573700506409150085569)
                      ·
                        rfl

theorem cell23_3156056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_3156056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156056 prefixEnd_3156056 := by exact prefixLift 3156056
  have htrace : WordTrace (prefixWord ++ tailWord_3156056) baseStart_3156056 baseEnd_3156056 := by
    simpa [prefixWord, tailWord_3156056, baseEnd_3156056] using wordTrace_append hprefix tailTrace_3156056
  have hstable : (prefixWord ++ tailWord_3156056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156056).length < 2 ^ (prefixWord ++ tailWord_3156056).sum := by decide
  have hdescent : baseEnd_3156056 < baseStart_3156056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156065 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_3156065 : Nat := 118140960795 + 3156065 * 2 ^ 59
def prefixEnd_3156065 : Nat := 4983230072969 + 3 ^ 40 * 3156065 * 2
def baseEnd_3156065 : Nat := 1620578321832299614873027

theorem tailTrace_3156065 : CollatzResearch.WordTrace tailWord_3156065 prefixEnd_3156065 1620578321832299614873027 := by
  unfold tailWord_3156065
  simp only [CollatzResearch.WordTrace]
  refine ⟨115111147311122992834093649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76740764874081995222729099 115111147311122992834093649)
  ·
    refine ⟨86333360483342244625570237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115111147311122992834093649 86333360483342244625570237)
    ·
      refine ⟨32375010181253341734588839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86333360483342244625570237 32375010181253341734588839)
      ·
        refine ⟨48562515271880012601883259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32375010181253341734588839 48562515271880012601883259)
        ·
          refine ⟨72843772907820018902824889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48562515271880012601883259 72843772907820018902824889)
          ·
            refine ⟨54632829680865014177118667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72843772907820018902824889 54632829680865014177118667)
            ·
              refine ⟨81949244521297521265678001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54632829680865014177118667 81949244521297521265678001)
              ·
                refine ⟨61461933390973140949258501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81949244521297521265678001 61461933390973140949258501)
                ·
                  refine ⟨11524112510807463927985969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61461933390973140949258501 11524112510807463927985969)
                  ·
                    refine ⟨8643084383105597945989477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11524112510807463927985969 8643084383105597945989477)
                    ·
                      refine ⟨1620578321832299614873027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8643084383105597945989477 1620578321832299614873027)
                      ·
                        rfl

theorem cell23_3156065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_3156065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156065 prefixEnd_3156065 := by exact prefixLift 3156065
  have htrace : WordTrace (prefixWord ++ tailWord_3156065) baseStart_3156065 baseEnd_3156065 := by
    simpa [prefixWord, tailWord_3156065, baseEnd_3156065] using wordTrace_append hprefix tailTrace_3156065
  have hstable : (prefixWord ++ tailWord_3156065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156065).length < 2 ^ (prefixWord ++ tailWord_3156065).sum := by decide
  have hdescent : baseEnd_3156065 < baseStart_3156065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156069 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 1, 4, 2]
def baseStart_3156069 : Nat := 118140960795 + 3156069 * 2 ^ 59
def prefixEnd_3156069 : Nat := 4983230072969 + 3 ^ 40 * 3156069 * 2
def baseEnd_3156069 : Nat := 1620580375754917599223009

theorem tailTrace_3156069 : CollatzResearch.WordTrace tailWord_3156069 prefixEnd_3156069 1620580375754917599223009 := by
  unfold tailWord_3156069
  simp only [CollatzResearch.WordTrace]
  refine ⟨115111293203108501517239261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76740862135405667678159507 115111293203108501517239261)
  ·
    refine ⟨43166734951165688068964723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115111293203108501517239261 43166734951165688068964723)
    ·
      refine ⟨64750102426748532103447085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43166734951165688068964723 64750102426748532103447085)
      ·
        refine ⟨24281288410030699538792657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64750102426748532103447085 24281288410030699538792657)
        ·
          refine ⟨18210966307523024654094493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24281288410030699538792657 18210966307523024654094493)
          ·
            refine ⟨6829112365321134245285435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18210966307523024654094493 6829112365321134245285435)
            ·
              refine ⟨10243668547981701367928153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6829112365321134245285435 10243668547981701367928153)
              ·
                refine ⟨7682751410986276025946115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10243668547981701367928153 7682751410986276025946115)
                ·
                  refine ⟨11524127116479414038919173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682751410986276025946115 11524127116479414038919173)
                  ·
                    refine ⟨2160773834339890132297345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11524127116479414038919173 2160773834339890132297345)
                    ·
                      refine ⟨1620580375754917599223009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160773834339890132297345 1620580375754917599223009)
                      ·
                        rfl

theorem cell23_3156069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_3156069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156069 prefixEnd_3156069 := by exact prefixLift 3156069
  have htrace : WordTrace (prefixWord ++ tailWord_3156069) baseStart_3156069 baseEnd_3156069 := by
    simpa [prefixWord, tailWord_3156069, baseEnd_3156069] using wordTrace_append hprefix tailTrace_3156069
  have hstable : (prefixWord ++ tailWord_3156069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156069).length < 2 ^ (prefixWord ++ tailWord_3156069).sum := by decide
  have hdescent : baseEnd_3156069 < baseStart_3156069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156105 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 1, 7]
def baseStart_3156105 : Nat := 118140960795 + 3156105 * 2 ^ 59
def prefixEnd_3156105 : Nat := 4983230072969 + 3 ^ 40 * 3156105 * 2
def baseEnd_3156105 : Nat := 540199620352826486124281

theorem tailTrace_3156105 : CollatzResearch.WordTrace tailWord_3156105 prefixEnd_3156105 540199620352826486124281 := by
  unfold tailWord_3156105
  simp only [CollatzResearch.WordTrace]
  refine ⟨115112606230978079665549769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76741737487318719777033179 115112606230978079665549769)
  ·
    refine ⟨86334454673233559749162327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115112606230978079665549769 86334454673233559749162327)
    ·
      refine ⟨129501682009850339623743491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86334454673233559749162327 129501682009850339623743491)
      ·
        refine ⟨194252523014775509435615237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129501682009850339623743491 194252523014775509435615237)
        ·
          refine ⟨36422348065270408019177857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194252523014775509435615237 36422348065270408019177857)
          ·
            refine ⟨27316761048952806014383393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36422348065270408019177857 27316761048952806014383393)
            ·
              refine ⟨20487570786714604510787545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27316761048952806014383393 20487570786714604510787545)
              ·
                refine ⟨15365678090035953383090659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20487570786714604510787545 15365678090035953383090659)
                ·
                  refine ⟨23048517135053930074635989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15365678090035953383090659 23048517135053930074635989)
                  ·
                    refine ⟨540199620352826486124281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23048517135053930074635989 540199620352826486124281)
                    ·
                      rfl

theorem cell23_3156105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_3156105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156105 prefixEnd_3156105 := by exact prefixLift 3156105
  have htrace : WordTrace (prefixWord ++ tailWord_3156105) baseStart_3156105 baseEnd_3156105 := by
    simpa [prefixWord, tailWord_3156105, baseEnd_3156105] using wordTrace_append hprefix tailTrace_3156105
  have hstable : (prefixWord ++ tailWord_3156105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156105).length < 2 ^ (prefixWord ++ tailWord_3156105).sum := by decide
  have hdescent : baseEnd_3156105 < baseStart_3156105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156112 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 2, 5, 2]
def baseStart_3156112 : Nat := 118140960795 + 3156112 * 2 ^ 59
def prefixEnd_3156112 : Nat := 4983230072969 + 3 ^ 40 * 3156112 * 2
def baseEnd_3156112 : Nat := 1620602455423060930985311

theorem tailTrace_3156112 : CollatzResearch.WordTrace tailWord_3156112 prefixEnd_3156112 1620602455423060930985311 := by
  unfold tailWord_3156112
  simp only [CollatzResearch.WordTrace]
  refine ⟨57556430770976359930527295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76741907694635146574036393 57556430770976359930527295)
  ·
    refine ⟨86334646156464539895790943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57556430770976359930527295 86334646156464539895790943)
    ·
      refine ⟨129501969234696809843686415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86334646156464539895790943 129501969234696809843686415)
      ·
        refine ⟨194252953852045214765529623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129501969234696809843686415 194252953852045214765529623)
        ·
          refine ⟨291379430778067822148294435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194252953852045214765529623 291379430778067822148294435)
          ·
            refine ⟨437069146167101733222441653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291379430778067822148294435 437069146167101733222441653)
            ·
              refine ⟨40975232453165787489603905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 437069146167101733222441653 40975232453165787489603905)
              ·
                refine ⟨30731424339874340617202929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40975232453165787489603905 30731424339874340617202929)
                ·
                  refine ⟨23048568254905755462902197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30731424339874340617202929 23048568254905755462902197)
                  ·
                    refine ⟨2160803273897414574647081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23048568254905755462902197 2160803273897414574647081)
                    ·
                      refine ⟨1620602455423060930985311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160803273897414574647081 1620602455423060930985311)
                      ·
                        rfl

theorem cell23_3156112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 5, 2].length) (baseStart_3156112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156112 prefixEnd_3156112 := by exact prefixLift 3156112
  have htrace : WordTrace (prefixWord ++ tailWord_3156112) baseStart_3156112 baseEnd_3156112 := by
    simpa [prefixWord, tailWord_3156112, baseEnd_3156112] using wordTrace_append hprefix tailTrace_3156112
  have hstable : (prefixWord ++ tailWord_3156112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156112).length < 2 ^ (prefixWord ++ tailWord_3156112).sum := by decide
  have hdescent : baseEnd_3156112 < baseStart_3156112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156155 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 6]
def baseStart_3156155 : Nat := 118140960795 + 3156155 * 2 ^ 59
def prefixEnd_3156155 : Nat := 4983230072969 + 3 ^ 40 * 3156155 * 2
def baseEnd_3156155 : Nat := 1620624535091204262747613

theorem tailTrace_3156155 : CollatzResearch.WordTrace tailWord_3156155 prefixEnd_3156155 1620624535091204262747613 := by
  unfold tailWord_3156155
  simp only [CollatzResearch.WordTrace]
  refine ⟨115114429880796938204869919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76742953253864625469913279 115114429880796938204869919)
  ·
    refine ⟨172671644821195407307304879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115114429880796938204869919 172671644821195407307304879)
    ·
      refine ⟨259007467231793110960957319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172671644821195407307304879 259007467231793110960957319)
      ·
        refine ⟨388511200847689666441435979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259007467231793110960957319 388511200847689666441435979)
        ·
          refine ⟨582766801271534499662153969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388511200847689666441435979 582766801271534499662153969)
          ·
            refine ⟨437075100953650874746615477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582766801271534499662153969 437075100953650874746615477)
            ·
              refine ⟨40975790714404769507495201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 437075100953650874746615477 40975790714404769507495201)
              ·
                refine ⟨30731843035803577130621401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40975790714404769507495201 30731843035803577130621401)
                ·
                  refine ⟨23048882276852682847966051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30731843035803577130621401 23048882276852682847966051)
                  ·
                    refine ⟨34573323415279024271949077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23048882276852682847966051 34573323415279024271949077)
                    ·
                      refine ⟨1620624535091204262747613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34573323415279024271949077 1620624535091204262747613)
                      ·
                        rfl

theorem cell23_3156155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_3156155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156155 prefixEnd_3156155 := by exact prefixLift 3156155
  have htrace : WordTrace (prefixWord ++ tailWord_3156155) baseStart_3156155 baseEnd_3156155 := by
    simpa [prefixWord, tailWord_3156155, baseEnd_3156155] using wordTrace_append hprefix tailTrace_3156155
  have hstable : (prefixWord ++ tailWord_3156155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156155).length < 2 ^ (prefixWord ++ tailWord_3156155).sum := by decide
  have hdescent : baseEnd_3156155 < baseStart_3156155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156186 : List Nat := [3, 1, 1, 2, 2, 1, 5, 3, 1, 4]
def baseStart_3156186 : Nat := 118140960795 + 3156186 * 2 ^ 59
def prefixEnd_3156186 : Nat := 4983230072969 + 3 ^ 40 * 3156186 * 2
def baseEnd_3156186 : Nat := 540213484330497880486657

theorem tailTrace_3156186 : CollatzResearch.WordTrace tailWord_3156186 prefixEnd_3156186 540213484330497880486657 := by
  unfold tailWord_3156186
  simp only [CollatzResearch.WordTrace]
  refine ⟨28778890135921157624812103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76743707029123086999498941 28778890135921157624812103)
  ·
    refine ⟨43168335203881736437218155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28778890135921157624812103 43168335203881736437218155)
    ·
      refine ⟨64752502805822604655827233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43168335203881736437218155 64752502805822604655827233)
      ·
        refine ⟨48564377104366953491870425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64752502805822604655827233 48564377104366953491870425)
        ·
          refine ⟨36423282828275215118902819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48564377104366953491870425 36423282828275215118902819)
          ·
            refine ⟨54634924242412822678354229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36423282828275215118902819 54634924242412822678354229)
            ·
              refine ⟨5122024147726202126095709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54634924242412822678354229 5122024147726202126095709)
              ·
                refine ⟨1920759055397325797285891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5122024147726202126095709 1920759055397325797285891)
                ·
                  refine ⟨2881138583095988695928837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920759055397325797285891 2881138583095988695928837)
                  ·
                    refine ⟨540213484330497880486657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2881138583095988695928837 540213484330497880486657)
                    ·
                      rfl

theorem cell23_3156186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_3156186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156186 prefixEnd_3156186 := by exact prefixLift 3156186
  have htrace : WordTrace (prefixWord ++ tailWord_3156186) baseStart_3156186 baseEnd_3156186 := by
    simpa [prefixWord, tailWord_3156186, baseEnd_3156186] using wordTrace_append hprefix tailTrace_3156186
  have hstable : (prefixWord ++ tailWord_3156186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156186).length < 2 ^ (prefixWord ++ tailWord_3156186).sum := by decide
  have hdescent : baseEnd_3156186 < baseStart_3156186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156236 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 2, 3, 2]
def baseStart_3156236 : Nat := 118140960795 + 3156236 * 2 ^ 59
def prefixEnd_3156236 : Nat := 4983230072969 + 3 ^ 40 * 3156236 * 2
def baseEnd_3156236 : Nat := 1620666127024218445834741

theorem tailTrace_3156236 : CollatzResearch.WordTrace tailWord_3156236 prefixEnd_3156236 1620666127024218445834741 := by
  unfold tailWord_3156236
  simp only [CollatzResearch.WordTrace]
  refine ⟨57558692096751744519284281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76744922795668992692379041 57558692096751744519284281)
  ·
    refine ⟨43169019072563808389463211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57558692096751744519284281 43169019072563808389463211)
    ·
      refine ⟨64753528608845712584194817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43169019072563808389463211 64753528608845712584194817)
      ·
        refine ⟨48565146456634284438146113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64753528608845712584194817 48565146456634284438146113)
        ·
          refine ⟨36423859842475713328609585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48565146456634284438146113 36423859842475713328609585)
          ·
            refine ⟨27317894881856784996457189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36423859842475713328609585 27317894881856784996457189)
            ·
              refine ⟨5122105290348147186835723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27317894881856784996457189 5122105290348147186835723)
              ·
                refine ⟨7683157935522220780253585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122105290348147186835723 7683157935522220780253585)
                ·
                  refine ⟨5762368451641665585190189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7683157935522220780253585 5762368451641665585190189)
                  ·
                    refine ⟨2160888169365624594446321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5762368451641665585190189 2160888169365624594446321)
                    ·
                      refine ⟨1620666127024218445834741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160888169365624594446321 1620666127024218445834741)
                      ·
                        rfl

theorem cell23_3156236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_3156236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156236 prefixEnd_3156236 := by exact prefixLift 3156236
  have htrace : WordTrace (prefixWord ++ tailWord_3156236) baseStart_3156236 baseEnd_3156236 := by
    simpa [prefixWord, tailWord_3156236, baseEnd_3156236] using wordTrace_append hprefix tailTrace_3156236
  have hstable : (prefixWord ++ tailWord_3156236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156236).length < 2 ^ (prefixWord ++ tailWord_3156236).sum := by decide
  have hdescent : baseEnd_3156236 < baseStart_3156236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156260 : List Nat := [2, 3, 1, 3, 1, 2, 4, 2, 1, 1, 3]
def baseStart_3156260 : Nat := 118140960795 + 3156260 * 2 ^ 59
def prefixEnd_3156260 : Nat := 4983230072969 + 3 ^ 40 * 3156260 * 2
def baseEnd_3156260 : Nat := 1620678450559926351934631

theorem tailTrace_3156260 : CollatzResearch.WordTrace tailWord_3156260 prefixEnd_3156260 1620678450559926351934631 := by
  unfold tailWord_3156260
  simp only [CollatzResearch.WordTrace]
  refine ⟨57559129772708270568721117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76745506363611027424961489 57559129772708270568721117)
  ·
    refine ⟨21584673664765601463270419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57559129772708270568721117 21584673664765601463270419)
    ·
      refine ⟨32377010497148402194905629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21584673664765601463270419 32377010497148402194905629)
      ·
        refine ⟨12141378936430650823089611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32377010497148402194905629 12141378936430650823089611)
        ·
          refine ⟨18212068404645976234634417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12141378936430650823089611 18212068404645976234634417)
          ·
            refine ⟨13659051303484482175975813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18212068404645976234634417 13659051303484482175975813)
            ·
              refine ⟨2561072119403340407995465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13659051303484482175975813 2561072119403340407995465)
              ·
                refine ⟨1920804089552505305996599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561072119403340407995465 1920804089552505305996599)
                ·
                  refine ⟨2881206134328757958994899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920804089552505305996599 2881206134328757958994899)
                  ·
                    refine ⟨4321809201493136938492349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2881206134328757958994899 4321809201493136938492349)
                    ·
                      refine ⟨1620678450559926351934631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4321809201493136938492349 1620678450559926351934631)
                      ·
                        rfl

theorem cell23_3156260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_3156260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156260 prefixEnd_3156260 := by exact prefixLift 3156260
  have htrace : WordTrace (prefixWord ++ tailWord_3156260) baseStart_3156260 baseEnd_3156260 := by
    simpa [prefixWord, tailWord_3156260, baseEnd_3156260] using wordTrace_append hprefix tailTrace_3156260
  have hstable : (prefixWord ++ tailWord_3156260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156260).length < 2 ^ (prefixWord ++ tailWord_3156260).sum := by decide
  have hdescent : baseEnd_3156260 < baseStart_3156260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156276 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_3156276 : Nat := 118140960795 + 3156276 * 2 ^ 59
def prefixEnd_3156276 : Nat := 4983230072969 + 3 ^ 40 * 3156276 * 2
def baseEnd_3156276 : Nat := 540228888750132763111519

theorem tailTrace_3156276 : CollatzResearch.WordTrace tailWord_3156276 prefixEnd_3156276 540228888750132763111519 := by
  unfold tailWord_3156276
  simp only [CollatzResearch.WordTrace]
  refine ⟨57559421556679287935012341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76745895408905717246683121 57559421556679287935012341)
  ·
    refine ⟨5396195770938683243907407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57559421556679287935012341 5396195770938683243907407)
    ·
      refine ⟨8094293656408024865861111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5396195770938683243907407 8094293656408024865861111)
      ·
        refine ⟨12141440484612037298791667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8094293656408024865861111 12141440484612037298791667)
        ·
          refine ⟨18212160726918055948187501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12141440484612037298791667 18212160726918055948187501)
          ·
            refine ⟨6829560272594270980570313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18212160726918055948187501 6829560272594270980570313)
            ·
              refine ⟨5122170204445703235427735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6829560272594270980570313 5122170204445703235427735)
              ·
                refine ⟨7683255306668554853141603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122170204445703235427735 7683255306668554853141603)
                ·
                  refine ⟨11524882960002832279712405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7683255306668554853141603 11524882960002832279712405)
                  ·
                    refine ⟨540228888750132763111519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11524882960002832279712405 540228888750132763111519)
                    ·
                      rfl

theorem cell23_3156276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_3156276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156276 prefixEnd_3156276 := by exact prefixLift 3156276
  have htrace : WordTrace (prefixWord ++ tailWord_3156276) baseStart_3156276 baseEnd_3156276 := by
    simpa [prefixWord, tailWord_3156276, baseEnd_3156276] using wordTrace_append hprefix tailTrace_3156276
  have hstable : (prefixWord ++ tailWord_3156276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156276).length < 2 ^ (prefixWord ++ tailWord_3156276).sum := by decide
  have hdescent : baseEnd_3156276 < baseStart_3156276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156286 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_3156286 : Nat := 118140960795 + 3156286 * 2 ^ 59
def prefixEnd_3156286 : Nat := 4983230072969 + 3 ^ 40 * 3156286 * 2
def baseEnd_3156286 : Nat := 1620691801056943250209511

theorem tailTrace_3156286 : CollatzResearch.WordTrace tailWord_3156286 prefixEnd_3156286 1620691801056943250209511 := by
  unfold tailWord_3156286
  simp only [CollatzResearch.WordTrace]
  refine ⟨14389900980415293447236089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76746138562214898385259141 14389900980415293447236089)
  ·
    refine ⟨10792425735311470085427067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14389900980415293447236089 10792425735311470085427067)
    ·
      refine ⟨16188638602967205128140601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10792425735311470085427067 16188638602967205128140601)
      ·
        refine ⟨12141478952225403846105451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16188638602967205128140601 12141478952225403846105451)
        ·
          refine ⟨18212218428338105769158177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12141478952225403846105451 18212218428338105769158177)
          ·
            refine ⟨13659163821253579326868633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18212218428338105769158177 13659163821253579326868633)
            ·
              refine ⟨10244372865940184495151475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13659163821253579326868633 10244372865940184495151475)
              ·
                refine ⟨15366559298910276742727213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10244372865940184495151475 15366559298910276742727213)
                ·
                  refine ⟨5762459737091353778522705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15366559298910276742727213 5762459737091353778522705)
                  ·
                    refine ⟨4321844802818515333892029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5762459737091353778522705 4321844802818515333892029)
                    ·
                      refine ⟨1620691801056943250209511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4321844802818515333892029 1620691801056943250209511)
                      ·
                        rfl

theorem cell23_3156286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_3156286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156286 prefixEnd_3156286 := by exact prefixLift 3156286
  have htrace : WordTrace (prefixWord ++ tailWord_3156286) baseStart_3156286 baseEnd_3156286 := by
    simpa [prefixWord, tailWord_3156286, baseEnd_3156286] using wordTrace_append hprefix tailTrace_3156286
  have hstable : (prefixWord ++ tailWord_3156286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156286).length < 2 ^ (prefixWord ++ tailWord_3156286).sum := by decide
  have hdescent : baseEnd_3156286 < baseStart_3156286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156300 : List Nat := [2, 2, 1, 3, 2, 1, 4, 3, 1, 2, 2]
def baseStart_3156300 : Nat := 118140960795 + 3156300 * 2 ^ 59
def prefixEnd_3156300 : Nat := 4983230072969 + 3 ^ 40 * 3156300 * 2
def baseEnd_3156300 : Nat := 1620698989786106195434447

theorem tailTrace_3156300 : CollatzResearch.WordTrace tailWord_3156300 prefixEnd_3156300 1620698989786106195434447 := by
  unfold tailWord_3156300
  simp only [CollatzResearch.WordTrace]
  refine ⟨57559859232635813984449177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76746478976847751979265569 57559859232635813984449177)
  ·
    refine ⟨43169894424476860488336883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57559859232635813984449177 43169894424476860488336883)
    ·
      refine ⟨64754841636715290732505325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43169894424476860488336883 64754841636715290732505325)
      ·
        refine ⟨24283065613768234024689497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64754841636715290732505325 24283065613768234024689497)
        ·
          refine ⟨18212299210326175518517123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24283065613768234024689497 18212299210326175518517123)
          ·
            refine ⟨27318448815489263277775685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18212299210326175518517123 27318448815489263277775685)
            ·
              refine ⟨5122209152904236864582941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27318448815489263277775685 5122209152904236864582941)
              ·
                refine ⟨1920828432339088824218603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5122209152904236864582941 1920828432339088824218603)
                ·
                  refine ⟨2881242648508633236327905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920828432339088824218603 2881242648508633236327905)
                  ·
                    refine ⟨2160931986381474927245929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2881242648508633236327905 2160931986381474927245929)
                    ·
                      refine ⟨1620698989786106195434447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160931986381474927245929 1620698989786106195434447)
                      ·
                        rfl

theorem cell23_3156300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_3156300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156300 prefixEnd_3156300 := by exact prefixLift 3156300
  have htrace : WordTrace (prefixWord ++ tailWord_3156300) baseStart_3156300 baseEnd_3156300 := by
    simpa [prefixWord, tailWord_3156300, baseEnd_3156300] using wordTrace_append hprefix tailTrace_3156300
  have hstable : (prefixWord ++ tailWord_3156300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156300).length < 2 ^ (prefixWord ++ tailWord_3156300).sum := by decide
  have hdescent : baseEnd_3156300 < baseStart_3156300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156302 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_3156302 : Nat := 118140960795 + 3156302 * 2 ^ 59
def prefixEnd_3156302 : Nat := 4983230072969 + 3 ^ 40 * 3156302 * 2
def baseEnd_3156302 : Nat := 540233338915805062536479

theorem tailTrace_3156302 : CollatzResearch.WordTrace tailWord_3156302 prefixEnd_3156302 540233338915805062536479 := by
  unfold tailWord_3156302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14389973926408047788808895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76746527607509588206980773 14389973926408047788808895)
  ·
    refine ⟨21584960889612071683213343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14389973926408047788808895 21584960889612071683213343)
    ·
      refine ⟨32377441334418107524820015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21584960889612071683213343 32377441334418107524820015)
      ·
        refine ⟨48566162001627161287230023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32377441334418107524820015 48566162001627161287230023)
        ·
          refine ⟨72849243002440741930845035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48566162001627161287230023 72849243002440741930845035)
          ·
            refine ⟨109273864503661112896267553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72849243002440741930845035 109273864503661112896267553)
            ·
              refine ⟨81955398377745834672200665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109273864503661112896267553 81955398377745834672200665)
              ·
                refine ⟨61466548783309376004150499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81955398377745834672200665 61466548783309376004150499)
                ·
                  refine ⟨92199823174964064006225749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61466548783309376004150499 92199823174964064006225749)
                  ·
                    refine ⟨540233338915805062536479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 92199823174964064006225749 540233338915805062536479)
                    ·
                      rfl

theorem cell23_3156302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_3156302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156302 prefixEnd_3156302 := by exact prefixLift 3156302
  have htrace : WordTrace (prefixWord ++ tailWord_3156302) baseStart_3156302 baseEnd_3156302 := by
    simpa [prefixWord, tailWord_3156302, baseEnd_3156302] using wordTrace_append hprefix tailTrace_3156302
  have hstable : (prefixWord ++ tailWord_3156302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156302).length < 2 ^ (prefixWord ++ tailWord_3156302).sum := by decide
  have hdescent : baseEnd_3156302 < baseStart_3156302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156312 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3156312 : Nat := 118140960795 + 3156312 * 2 ^ 59
def prefixEnd_3156312 : Nat := 4983230072969 + 3 ^ 40 * 3156312 * 2
def baseEnd_3156312 : Nat := 1620705151553960148484391

theorem tailTrace_3156312 : CollatzResearch.WordTrace tailWord_3156312 prefixEnd_3156312 1620705151553960148484391 := by
  unfold tailWord_3156312
  simp only [CollatzResearch.WordTrace]
  refine ⟨57560078070614077009167595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76746770760818769345556793 57560078070614077009167595)
  ·
    refine ⟨86340117105921115513751393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57560078070614077009167595 86340117105921115513751393)
    ·
      refine ⟨64755087829440836635313545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86340117105921115513751393 64755087829440836635313545)
      ·
        refine ⟨48566315872080627476485159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64755087829440836635313545 48566315872080627476485159)
        ·
          refine ⟨72849473808120941214727739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48566315872080627476485159 72849473808120941214727739)
          ·
            refine ⟨109274210712181411822091609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72849473808120941214727739 109274210712181411822091609)
            ·
              refine ⟨81955658034136058866568707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109274210712181411822091609 81955658034136058866568707)
              ·
                refine ⟨122933487051204088299853061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81955658034136058866568707 122933487051204088299853061)
                ·
                  refine ⟨23050028822100766556222449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122933487051204088299853061 23050028822100766556222449)
                  ·
                    refine ⟨17287521616575574917166837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23050028822100766556222449 17287521616575574917166837)
                    ·
                      refine ⟨1620705151553960148484391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17287521616575574917166837 1620705151553960148484391)
                      ·
                        rfl

theorem cell23_3156312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3156312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156312 prefixEnd_3156312 := by exact prefixLift 3156312
  have htrace : WordTrace (prefixWord ++ tailWord_3156312) baseStart_3156312 baseEnd_3156312 := by
    simpa [prefixWord, tailWord_3156312, baseEnd_3156312] using wordTrace_append hprefix tailTrace_3156312
  have hstable : (prefixWord ++ tailWord_3156312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156312).length < 2 ^ (prefixWord ++ tailWord_3156312).sum := by decide
  have hdescent : baseEnd_3156312 < baseStart_3156312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156356 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_3156356 : Nat := 118140960795 + 3156356 * 2 ^ 59
def prefixEnd_3156356 : Nat := 4983230072969 + 3 ^ 40 * 3156356 * 2
def baseEnd_3156356 : Nat := 1620727744702757976334189

theorem tailTrace_3156356 : CollatzResearch.WordTrace tailWord_3156356 prefixEnd_3156356 1620727744702757976334189 := by
  unfold tailWord_3156356
  simp only [CollatzResearch.WordTrace]
  refine ⟨57560880476534374766468461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76747840635379166355291281 57560880476534374766468461)
  ·
    refine ⟨21585330178700390537425673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57560880476534374766468461 21585330178700390537425673)
    ·
      refine ⟨16188997634025292903069255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21585330178700390537425673 16188997634025292903069255)
      ·
        refine ⟨24283496451037939354603883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16188997634025292903069255 24283496451037939354603883)
        ·
          refine ⟨36425244676556909031905825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24283496451037939354603883 36425244676556909031905825)
          ·
            refine ⟨27318933507417681773929369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36425244676556909031905825 27318933507417681773929369)
            ·
              refine ⟨20489200130563261330447027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27318933507417681773929369 20489200130563261330447027)
              ·
                refine ⟨30733800195844891995670541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20489200130563261330447027 30733800195844891995670541)
                ·
                  refine ⟨11525175073441834498376453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30733800195844891995670541 11525175073441834498376453)
                  ·
                    refine ⟨2160970326270343968445585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11525175073441834498376453 2160970326270343968445585)
                    ·
                      refine ⟨1620727744702757976334189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160970326270343968445585 1620727744702757976334189)
                      ·
                        rfl

theorem cell23_3156356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_3156356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156356 prefixEnd_3156356 := by exact prefixLift 3156356
  have htrace : WordTrace (prefixWord ++ tailWord_3156356) baseStart_3156356 baseEnd_3156356 := by
    simpa [prefixWord, tailWord_3156356, baseEnd_3156356] using wordTrace_append hprefix tailTrace_3156356
  have hstable : (prefixWord ++ tailWord_3156356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156356).length < 2 ^ (prefixWord ++ tailWord_3156356).sum := by decide
  have hdescent : baseEnd_3156356 < baseStart_3156356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156359 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_3156359 : Nat := 118140960795 + 3156359 * 2 ^ 59
def prefixEnd_3156359 : Nat := 4983230072969 + 3 ^ 40 * 3156359 * 2
def baseEnd_3156359 : Nat := 1620729285144721464596675

theorem tailTrace_3156359 : CollatzResearch.WordTrace tailWord_3156359 prefixEnd_3156359 1620729285144721464596675 := by
  unfold tailWord_3156359
  simp only [CollatzResearch.WordTrace]
  refine ⟨115121870372057881045296131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76747913581371920696864087 115121870372057881045296131)
  ·
    refine ⟨172682805558086821567944197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115121870372057881045296131 172682805558086821567944197)
    ·
      refine ⟨32378026042141279043989537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172682805558086821567944197 32378026042141279043989537)
      ·
        refine ⟨24283519531605959282992153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32378026042141279043989537 24283519531605959282992153)
        ·
          refine ⟨18212639648704469462244115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24283519531605959282992153 18212639648704469462244115)
          ·
            refine ⟨27318959473056704193366173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18212639648704469462244115 27318959473056704193366173)
            ·
              refine ⟨10244609802396264072512315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27318959473056704193366173 10244609802396264072512315)
              ·
                refine ⟨15366914703594396108768473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10244609802396264072512315 15366914703594396108768473)
                ·
                  refine ⟨11525186027695797081576355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15366914703594396108768473 11525186027695797081576355)
                  ·
                    refine ⟨17287779041543695622364533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11525186027695797081576355 17287779041543695622364533)
                    ·
                      refine ⟨1620729285144721464596675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17287779041543695622364533 1620729285144721464596675)
                      ·
                        rfl

theorem cell23_3156359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_3156359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156359 prefixEnd_3156359 := by exact prefixLift 3156359
  have htrace : WordTrace (prefixWord ++ tailWord_3156359) baseStart_3156359 baseEnd_3156359 := by
    simpa [prefixWord, tailWord_3156359, baseEnd_3156359] using wordTrace_append hprefix tailTrace_3156359
  have hstable : (prefixWord ++ tailWord_3156359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156359).length < 2 ^ (prefixWord ++ tailWord_3156359).sum := by decide
  have hdescent : baseEnd_3156359 < baseStart_3156359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156373 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 2, 2, 2]
def baseStart_3156373 : Nat := 118140960795 + 3156373 * 2 ^ 59
def prefixEnd_3156373 : Nat := 4983230072969 + 3 ^ 40 * 3156373 * 2
def baseEnd_3156373 : Nat := 1620736473873884409821611

theorem tailTrace_3156373 : CollatzResearch.WordTrace tailWord_3156373 prefixEnd_3156373 1620736473873884409821611 := by
  unfold tailWord_3156373
  simp only [CollatzResearch.WordTrace]
  refine ⟨115122380994007161436305773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76748253996004774290870515 115122380994007161436305773)
  ·
    refine ⟨43170892872752685538614665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115122380994007161436305773 43170892872752685538614665)
    ·
      refine ⟨32378169654564514153960999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43170892872752685538614665 32378169654564514153960999)
      ·
        refine ⟨48567254481846771230941499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32378169654564514153960999 48567254481846771230941499)
        ·
          refine ⟨72850881722770156846412249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48567254481846771230941499 72850881722770156846412249)
          ·
            refine ⟨54638161292077617634809187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72850881722770156846412249 54638161292077617634809187)
            ·
              refine ⟨81957241938116426452213781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54638161292077617634809187 81957241938116426452213781)
              ·
                refine ⟨3841745715849207489947521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81957241938116426452213781 3841745715849207489947521)
                ·
                  refine ⟨2881309286886905617460641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3841745715849207489947521 2881309286886905617460641)
                  ·
                    refine ⟨2160981965165179213095481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2881309286886905617460641 2160981965165179213095481)
                    ·
                      refine ⟨1620736473873884409821611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2160981965165179213095481 1620736473873884409821611)
                      ·
                        rfl

theorem cell23_3156373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_3156373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156373 prefixEnd_3156373 := by exact prefixLift 3156373
  have htrace : WordTrace (prefixWord ++ tailWord_3156373) baseStart_3156373 baseEnd_3156373 := by
    simpa [prefixWord, tailWord_3156373, baseEnd_3156373] using wordTrace_append hprefix tailTrace_3156373
  have hstable : (prefixWord ++ tailWord_3156373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156373).length < 2 ^ (prefixWord ++ tailWord_3156373).sum := by decide
  have hdescent : baseEnd_3156373 < baseStart_3156373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156389 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 1, 5, 3]
def baseStart_3156389 : Nat := 118140960795 + 3156389 * 2 ^ 59
def prefixEnd_3156389 : Nat := 4983230072969 + 3 ^ 40 * 3156389 * 2
def baseEnd_3156389 : Nat := 1620744689564356347221537

theorem tailTrace_3156389 : CollatzResearch.WordTrace tailWord_3156389 prefixEnd_3156389 1620744689564356347221537 := by
  unfold tailWord_3156389
  simp only [CollatzResearch.WordTrace]
  refine ⟨115122964561949196168888221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76748643041299464112592147 115122964561949196168888221)
  ·
    refine ⟨43171111710730948563333083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115122964561949196168888221 43171111710730948563333083)
    ·
      refine ⟨64756667566096422844999625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43171111710730948563333083 64756667566096422844999625)
      ·
        refine ⟨48567500674572317133749719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64756667566096422844999625 48567500674572317133749719)
        ·
          refine ⟨72851251011858475700624579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48567500674572317133749719 72851251011858475700624579)
          ·
            refine ⟨109276876517787713550936869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72851251011858475700624579 109276876517787713550936869)
            ·
              refine ⟨20489414347085196290800663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109276876517787713550936869 20489414347085196290800663)
              ·
                refine ⟨30734121520627794436200995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20489414347085196290800663 30734121520627794436200995)
                ·
                  refine ⟨46101182280941691654301493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30734121520627794436200995 46101182280941691654301493)
                  ·
                    refine ⟨4321985838838283592590765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46101182280941691654301493 4321985838838283592590765)
                    ·
                      refine ⟨1620744689564356347221537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4321985838838283592590765 1620744689564356347221537)
                      ·
                        rfl

theorem cell23_3156389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_3156389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156389 prefixEnd_3156389 := by exact prefixLift 3156389
  have htrace : WordTrace (prefixWord ++ tailWord_3156389) baseStart_3156389 baseEnd_3156389 := by
    simpa [prefixWord, tailWord_3156389, baseEnd_3156389] using wordTrace_append hprefix tailTrace_3156389
  have hstable : (prefixWord ++ tailWord_3156389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156389).length < 2 ^ (prefixWord ++ tailWord_3156389).sum := by decide
  have hdescent : baseEnd_3156389 < baseStart_3156389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156436 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3156436 : Nat := 118140960795 + 3156436 * 2 ^ 59
def prefixEnd_3156436 : Nat := 4983230072969 + 3 ^ 40 * 3156436 * 2
def baseEnd_3156436 : Nat := 1620768823155117663333821

theorem tailTrace_3156436 : CollatzResearch.WordTrace tailWord_3156436 prefixEnd_3156436 1620768823155117663333821 := by
  unfold tailWord_3156436
  simp only [CollatzResearch.WordTrace]
  refine ⟨57562339396389461597924581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76749785861852615463899441 57562339396389461597924581)
  ·
    refine ⟨10792938636823024049610859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57562339396389461597924581 10792938636823024049610859)
    ·
      refine ⟨16189407955234536074416289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10792938636823024049610859 16189407955234536074416289)
      ·
        refine ⟨12142055966425902055812217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16189407955234536074416289 12142055966425902055812217)
        ·
          refine ⟨9106541974819426541859163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12142055966425902055812217 9106541974819426541859163)
          ·
            refine ⟨13659812962229139812788745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9106541974819426541859163 13659812962229139812788745)
            ·
              refine ⟨10244859721671854859591559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13659812962229139812788745 10244859721671854859591559)
              ·
                refine ⟨15367289582507782289387339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10244859721671854859591559 15367289582507782289387339)
                ·
                  refine ⟨23050934373761673434081009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15367289582507782289387339 23050934373761673434081009)
                  ·
                    refine ⟨17288200780321255075560757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23050934373761673434081009 17288200780321255075560757)
                    ·
                      refine ⟨1620768823155117663333821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17288200780321255075560757 1620768823155117663333821)
                      ·
                        rfl

theorem cell23_3156436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3156436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156436 prefixEnd_3156436 := by exact prefixLift 3156436
  have htrace : WordTrace (prefixWord ++ tailWord_3156436) baseStart_3156436 baseEnd_3156436 := by
    simpa [prefixWord, tailWord_3156436, baseEnd_3156436] using wordTrace_append hprefix tailTrace_3156436
  have hstable : (prefixWord ++ tailWord_3156436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156436).length < 2 ^ (prefixWord ++ tailWord_3156436).sum := by decide
  have hdescent : baseEnd_3156436 < baseStart_3156436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156456 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 5, 4]
def baseStart_3156456 : Nat := 118140960795 + 3156456 * 2 ^ 59
def prefixEnd_3156456 : Nat := 4983230072969 + 3 ^ 40 * 3156456 * 2
def baseEnd_3156456 : Nat := 540259697589402528361243

theorem tailTrace_3156456 : CollatzResearch.WordTrace tailWord_3156456 prefixEnd_3156456 540259697589402528361243 := by
  unfold tailWord_3156456
  simp only [CollatzResearch.WordTrace]
  refine ⟨57562704126353233305788611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76750272168470977741051481 57562704126353233305788611)
  ·
    refine ⟨86344056189529849958682917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57562704126353233305788611 86344056189529849958682917)
    ·
      refine ⟨16189510535536846867253047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86344056189529849958682917 16189510535536846867253047)
      ·
        refine ⟨24284265803305270300879571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16189510535536846867253047 24284265803305270300879571)
        ·
          refine ⟨36426398704957905451319357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24284265803305270300879571 36426398704957905451319357)
          ·
            refine ⟨13659899514359214544244759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36426398704957905451319357 13659899514359214544244759)
            ·
              refine ⟨20489849271538821816367139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13659899514359214544244759 20489849271538821816367139)
              ·
                refine ⟨30734773907308232724550709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20489849271538821816367139 30734773907308232724550709)
                ·
                  refine ⟨2881385053810146817926629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30734773907308232724550709 2881385053810146817926629)
                  ·
                    refine ⟨540259697589402528361243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2881385053810146817926629 540259697589402528361243)
                    ·
                      rfl

theorem cell23_3156456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_3156456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156456 prefixEnd_3156456 := by exact prefixLift 3156456
  have htrace : WordTrace (prefixWord ++ tailWord_3156456) baseStart_3156456 baseEnd_3156456 := by
    simpa [prefixWord, tailWord_3156456, baseEnd_3156456] using wordTrace_append hprefix tailTrace_3156456
  have hstable : (prefixWord ++ tailWord_3156456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156456).length < 2 ^ (prefixWord ++ tailWord_3156456).sum := by decide
  have hdescent : baseEnd_3156456 < baseStart_3156456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156473 : List Nat := [1, 2, 1, 3, 1, 2, 3, 5, 1, 4]
def baseStart_3156473 : Nat := 118140960795 + 3156473 * 2 ^ 59
def prefixEnd_3156473 : Nat := 4983230072969 + 3 ^ 40 * 3156473 * 2
def baseEnd_3156473 : Nat := 540262607313111339523717

theorem tailTrace_3156473 : CollatzResearch.WordTrace tailWord_3156473 prefixEnd_3156473 540262607313111339523717 := by
  unfold tailWord_3156473
  simp only [CollatzResearch.WordTrace]
  refine ⟨115126028293644878514946073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76750685529096585676630715 115126028293644878514946073)
  ·
    refine ⟨86344521220233658886209555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115126028293644878514946073 86344521220233658886209555)
    ·
      refine ⟨129516781830350488329314333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86344521220233658886209555 129516781830350488329314333)
      ·
        refine ⟨48568793186381433123492875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129516781830350488329314333 48568793186381433123492875)
        ·
          refine ⟨72853189779572149685239313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48568793186381433123492875 72853189779572149685239313)
          ·
            refine ⟨54639892334679112263929485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72853189779572149685239313 54639892334679112263929485)
            ·
              refine ⟨20489959625504667098973557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54639892334679112263929485 20489959625504667098973557)
              ·
                refine ⟨1920933714891062540528771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20489959625504667098973557 1920933714891062540528771)
                ·
                  refine ⟨2881400572336593810793157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920933714891062540528771 2881400572336593810793157)
                  ·
                    refine ⟨540262607313111339523717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2881400572336593810793157 540262607313111339523717)
                    ·
                      rfl

theorem cell23_3156473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 1, 4].length) (baseStart_3156473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156473 prefixEnd_3156473 := by exact prefixLift 3156473
  have htrace : WordTrace (prefixWord ++ tailWord_3156473) baseStart_3156473 baseEnd_3156473 := by
    simpa [prefixWord, tailWord_3156473, baseEnd_3156473] using wordTrace_append hprefix tailTrace_3156473
  have hstable : (prefixWord ++ tailWord_3156473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156473).length < 2 ^ (prefixWord ++ tailWord_3156473).sum := by decide
  have hdescent : baseEnd_3156473 < baseStart_3156473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156513 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_3156513 : Nat := 118140960795 + 3156513 * 2 ^ 59
def prefixEnd_3156513 : Nat := 4983230072969 + 3 ^ 40 * 3156513 * 2
def baseEnd_3156513 : Nat := 1620808361165513862070967

theorem tailTrace_3156513 : CollatzResearch.WordTrace tailWord_3156513 prefixEnd_3156513 1620808361165513862070967 := by
  unfold tailWord_3156513
  simp only [CollatzResearch.WordTrace]
  refine ⟨115127487213499965346402193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76751658142333310230934795 115127487213499965346402193)
  ·
    refine ⟨86345615410124974009801645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115127487213499965346402193 86345615410124974009801645)
    ·
      refine ⟨32379605778796865253675617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86345615410124974009801645 32379605778796865253675617)
      ·
        refine ⟨24284704334097648940256713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32379605778796865253675617 24284704334097648940256713)
        ·
          refine ⟨18213528250573236705192535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24284704334097648940256713 18213528250573236705192535)
          ·
            refine ⟨27320292375859855057788803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18213528250573236705192535 27320292375859855057788803)
            ·
              refine ⟨40980438563789782586683205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27320292375859855057788803 40980438563789782586683205)
              ·
                refine ⟨7683832230710584235003101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40980438563789782586683205 7683832230710584235003101)
                ·
                  refine ⟨2881437086516469088126163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7683832230710584235003101 2881437086516469088126163)
                  ·
                    refine ⟨4322155629774703632189245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2881437086516469088126163 4322155629774703632189245)
                    ·
                      refine ⟨1620808361165513862070967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4322155629774703632189245 1620808361165513862070967)
                      ·
                        rfl

theorem cell23_3156513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_3156513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156513 prefixEnd_3156513 := by exact prefixLift 3156513
  have htrace : WordTrace (prefixWord ++ tailWord_3156513) baseStart_3156513 baseEnd_3156513 := by
    simpa [prefixWord, tailWord_3156513, baseEnd_3156513] using wordTrace_append hprefix tailTrace_3156513
  have hstable : (prefixWord ++ tailWord_3156513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156513).length < 2 ^ (prefixWord ++ tailWord_3156513).sum := by decide
  have hdescent : baseEnd_3156513 < baseStart_3156513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156540 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 2, 3, 2]
def baseStart_3156540 : Nat := 118140960795 + 3156540 * 2 ^ 59
def prefixEnd_3156540 : Nat := 4983230072969 + 3 ^ 40 * 3156540 * 2
def baseEnd_3156540 : Nat := 1620822225143185256433343

theorem tailTrace_3156540 : CollatzResearch.WordTrace tailWord_3156540 prefixEnd_3156540 1620822225143185256433343 := by
  unfold tailWord_3156540
  simp only [CollatzResearch.WordTrace]
  refine ⟨57564235992201074478817537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76752314656268099305090049 57564235992201074478817537)
  ·
    refine ⟨43173176994150805859113153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57564235992201074478817537 43173176994150805859113153)
    ·
      refine ⟨32379882745613104394334865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43173176994150805859113153 32379882745613104394334865)
      ·
        refine ⟨24284912059209828295751149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32379882745613104394334865 24284912059209828295751149)
        ·
          refine ⟨9106842022203685610906681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24284912059209828295751149 9106842022203685610906681)
          ·
            refine ⟨6830131516652764208180011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9106842022203685610906681 6830131516652764208180011)
            ·
              refine ⟨10245197274979146312270017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6830131516652764208180011 10245197274979146312270017)
              ·
                refine ⟨7683897956234359734202513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10245197274979146312270017 7683897956234359734202513)
                ·
                  refine ⟨5762923467175769800651885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7683897956234359734202513 5762923467175769800651885)
                  ·
                    refine ⟨2161096300190913675244457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5762923467175769800651885 2161096300190913675244457)
                    ·
                      refine ⟨1620822225143185256433343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2161096300190913675244457 1620822225143185256433343)
                      ·
                        rfl

theorem cell23_3156540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_3156540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156540 prefixEnd_3156540 := by exact prefixLift 3156540
  have htrace : WordTrace (prefixWord ++ tailWord_3156540) baseStart_3156540 baseEnd_3156540 := by
    simpa [prefixWord, tailWord_3156540, baseEnd_3156540] using wordTrace_append hprefix tailTrace_3156540
  have hstable : (prefixWord ++ tailWord_3156540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156540).length < 2 ^ (prefixWord ++ tailWord_3156540).sum := by decide
  have hdescent : baseEnd_3156540 < baseStart_3156540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156556 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3156556 : Nat := 118140960795 + 3156556 * 2 ^ 59
def prefixEnd_3156556 : Nat := 4983230072969 + 3 ^ 40 * 3156556 * 2
def baseEnd_3156556 : Nat := 1620830440833657193833269

theorem tailTrace_3156556 : CollatzResearch.WordTrace tailWord_3156556 prefixEnd_3156556 1620830440833657193833269 := by
  unfold tailWord_3156556
  simp only [CollatzResearch.WordTrace]
  refine ⟨57564527776172091845108761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76752703701562789126811681 57564527776172091845108761)
  ·
    refine ⟨43173395832129068883831571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57564527776172091845108761 43173395832129068883831571)
    ·
      refine ⟨64760093748193603325747357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43173395832129068883831571 64760093748193603325747357)
      ·
        refine ⟨24285035155572601247155259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64760093748193603325747357 24285035155572601247155259)
        ·
          refine ⟨36427552733358901870732889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24285035155572601247155259 36427552733358901870732889)
          ·
            refine ⟨27320664550019176403049667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36427552733358901870732889 27320664550019176403049667)
            ·
              refine ⟨40980996825028764604574501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27320664550019176403049667 40980996825028764604574501)
              ·
                refine ⟨7683936904692893363357719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40980996825028764604574501 7683936904692893363357719)
                ·
                  refine ⟨11525905357039340045036579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7683936904692893363357719 11525905357039340045036579)
                  ·
                    refine ⟨17288858035559010067554869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11525905357039340045036579 17288858035559010067554869)
                    ·
                      refine ⟨1620830440833657193833269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17288858035559010067554869 1620830440833657193833269)
                      ·
                        rfl

theorem cell23_3156556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3156556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156556 prefixEnd_3156556 := by exact prefixLift 3156556
  have htrace : WordTrace (prefixWord ++ tailWord_3156556) baseStart_3156556 baseEnd_3156556 := by
    simpa [prefixWord, tailWord_3156556, baseEnd_3156556] using wordTrace_append hprefix tailTrace_3156556
  have hstable : (prefixWord ++ tailWord_3156556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156556).length < 2 ^ (prefixWord ++ tailWord_3156556).sum := by decide
  have hdescent : baseEnd_3156556 < baseStart_3156556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156559 : List Nat := [1, 1, 2, 1, 1, 2, 5, 10]
def baseStart_3156559 : Nat := 118140960795 + 3156559 * 2 ^ 59
def prefixEnd_3156559 : Nat := 4983230072969 + 3 ^ 40 * 3156559 * 2
def baseEnd_3156559 : Nat := 60030814121319284522065

theorem tailTrace_3156559 : CollatzResearch.WordTrace tailWord_3156559 prefixEnd_3156559 60030814121319284522065 := by
  unfold tailWord_3156559
  simp only [CollatzResearch.WordTrace]
  refine ⟨115129164971333315202576731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76752776647555543468384487 115129164971333315202576731)
  ·
    refine ⟨172693747456999972803865097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115129164971333315202576731 172693747456999972803865097)
    ·
      refine ⟨129520310592749979602898823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172693747456999972803865097 129520310592749979602898823)
      ·
        refine ⟨194280465889124969404348235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129520310592749979602898823 194280465889124969404348235)
        ·
          refine ⟨291420698833687454106522353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194280465889124969404348235 291420698833687454106522353)
          ·
            refine ⟨218565524125265590579891765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291420698833687454106522353 218565524125265590579891765)
            ·
              refine ⟨20490517886743649116864853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218565524125265590579891765 20490517886743649116864853)
              ·
                refine ⟨60030814121319284522065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20490517886743649116864853 60030814121319284522065)
                ·
                  rfl

theorem cell23_3156559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 10].length) (baseStart_3156559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156559 prefixEnd_3156559 := by exact prefixLift 3156559
  have htrace : WordTrace (prefixWord ++ tailWord_3156559) baseStart_3156559 baseEnd_3156559 := by
    simpa [prefixWord, tailWord_3156559, baseEnd_3156559] using wordTrace_append hprefix tailTrace_3156559
  have hstable : (prefixWord ++ tailWord_3156559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156559).length < 2 ^ (prefixWord ++ tailWord_3156559).sum := by decide
  have hdescent : baseEnd_3156559 < baseStart_3156559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156590 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_3156590 : Nat := 118140960795 + 3156590 * 2 ^ 59
def prefixEnd_3156590 : Nat := 4983230072969 + 3 ^ 40 * 3156590 * 2
def baseEnd_3156590 : Nat := 1620847899175910060808113

theorem tailTrace_3156590 : CollatzResearch.WordTrace tailWord_3156590 prefixEnd_3156590 1620847899175910060808113 := by
  unfold tailWord_3156590
  simp only [CollatzResearch.WordTrace]
  refine ⟨14391286954277625937119403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76753530422814004997970149 14391286954277625937119403)
  ·
    refine ⟨21586930431416438905679105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14391286954277625937119403 21586930431416438905679105)
    ·
      refine ⟨16190197823562329179259329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21586930431416438905679105 16190197823562329179259329)
      ·
        refine ⟨12142648367671746884444497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16190197823562329179259329 12142648367671746884444497)
        ·
          refine ⟨9106986275753810163333373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12142648367671746884444497 9106986275753810163333373)
          ·
            refine ⟨3415119853407678811250015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9106986275753810163333373 3415119853407678811250015)
            ·
              refine ⟨5122679780111518216875023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415119853407678811250015 5122679780111518216875023)
              ·
                refine ⟨7684019670167277325312535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122679780111518216875023 7684019670167277325312535)
                ·
                  refine ⟨11526029505250915987968803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7684019670167277325312535 11526029505250915987968803)
                  ·
                    refine ⟨17289044257876373981953205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11526029505250915987968803 17289044257876373981953205)
                    ·
                      refine ⟨1620847899175910060808113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17289044257876373981953205 1620847899175910060808113)
                      ·
                        rfl

theorem cell23_3156590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_3156590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156590 prefixEnd_3156590 := by exact prefixLift 3156590
  have htrace : WordTrace (prefixWord ++ tailWord_3156590) baseStart_3156590 baseEnd_3156590 := by
    simpa [prefixWord, tailWord_3156590, baseEnd_3156590] using wordTrace_append hprefix tailTrace_3156590
  have hstable : (prefixWord ++ tailWord_3156590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156590).length < 2 ^ (prefixWord ++ tailWord_3156590).sum := by decide
  have hdescent : baseEnd_3156590 < baseStart_3156590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156597 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3156597 : Nat := 118140960795 + 3156597 * 2 ^ 59
def prefixEnd_3156597 : Nat := 4983230072969 + 3 ^ 40 * 3156597 * 2
def baseEnd_3156597 : Nat := 540283831180163844473527

theorem tailTrace_3156597 : CollatzResearch.WordTrace tailWord_3156597 prefixEnd_3156597 540283831180163844473527 := by
  unfold tailWord_3156597
  simp only [CollatzResearch.WordTrace]
  refine ⟨115130550945195647692460045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76753700630130431794973363 115130550945195647692460045)
  ·
    refine ⟨43173956604448367884672517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115130550945195647692460045 43173956604448367884672517)
    ·
      refine ⟨8095116863334068978376097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43173956604448367884672517 8095116863334068978376097)
      ·
        refine ⟨6071337647500551733782073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8095116863334068978376097 6071337647500551733782073)
        ·
          refine ⟨4553503235625413800336555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6071337647500551733782073 4553503235625413800336555)
          ·
            refine ⟨6830254853438120700504833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553503235625413800336555 6830254853438120700504833)
            ·
              refine ⟨5122691140078590525378625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6830254853438120700504833 5122691140078590525378625)
              ·
                refine ⟨3842018355058942894033969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5122691140078590525378625 3842018355058942894033969)
                ·
                  refine ⟨2881513766294207170525477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3842018355058942894033969 2881513766294207170525477)
                  ·
                    refine ⟨540283831180163844473527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2881513766294207170525477 540283831180163844473527)
                    ·
                      rfl

theorem cell23_3156597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3156597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156597 prefixEnd_3156597 := by exact prefixLift 3156597
  have htrace : WordTrace (prefixWord ++ tailWord_3156597) baseStart_3156597 baseEnd_3156597 := by
    simpa [prefixWord, tailWord_3156597, baseEnd_3156597] using wordTrace_append hprefix tailTrace_3156597
  have hstable : (prefixWord ++ tailWord_3156597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156597).length < 2 ^ (prefixWord ++ tailWord_3156597).sum := by decide
  have hdescent : baseEnd_3156597 < baseStart_3156597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156598 : List Nat := [5, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_3156598 : Nat := 118140960795 + 3156598 * 2 ^ 59
def prefixEnd_3156598 : Nat := 4983230072969 + 3 ^ 40 * 3156598 * 2
def baseEnd_3156598 : Nat := 1620852007021146029508077

theorem tailTrace_3156598 : CollatzResearch.WordTrace tailWord_3156598 prefixEnd_3156598 1620852007021146029508077 := by
  unfold tailWord_3156598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7195661713637001553952903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76753724945461349908830965 7195661713637001553952903)
  ·
    refine ⟨10793492570455502330929355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7195661713637001553952903 10793492570455502330929355)
    ·
      refine ⟨16190238855683253496394033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10793492570455502330929355 16190238855683253496394033)
      ·
        refine ⟨12142679141762440122295525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16190238855683253496394033 12142679141762440122295525)
        ·
          refine ⟨2276752339080457522930411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12142679141762440122295525 2276752339080457522930411)
          ·
            refine ⟨3415128508620686284395617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276752339080457522930411 3415128508620686284395617)
            ·
              refine ⟨2561346381465514713296713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3415128508620686284395617 2561346381465514713296713)
              ·
                refine ⟨1921009786099136034972535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561346381465514713296713 1921009786099136034972535)
                ·
                  refine ⟨2881514679148704052458803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921009786099136034972535 2881514679148704052458803)
                  ·
                    refine ⟨4322272018723056078688205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2881514679148704052458803 4322272018723056078688205)
                    ·
                      refine ⟨1620852007021146029508077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4322272018723056078688205 1620852007021146029508077)
                      ·
                        rfl

theorem cell23_3156598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_3156598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156598 prefixEnd_3156598 := by exact prefixLift 3156598
  have htrace : WordTrace (prefixWord ++ tailWord_3156598) baseStart_3156598 baseEnd_3156598 := by
    simpa [prefixWord, tailWord_3156598, baseEnd_3156598] using wordTrace_append hprefix tailTrace_3156598
  have hstable : (prefixWord ++ tailWord_3156598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156598).length < 2 ^ (prefixWord ++ tailWord_3156598).sum := by decide
  have hdescent : baseEnd_3156598 < baseStart_3156598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156604 : List Nat := [2, 2, 2, 1, 1, 2, 6, 2, 1, 2, 2]
def baseStart_3156604 : Nat := 118140960795 + 3156604 * 2 ^ 59
def prefixEnd_3156604 : Nat := 4983230072969 + 3 ^ 40 * 3156604 * 2
def baseEnd_3156604 : Nat := 1620855087905073006033049

theorem tailTrace_3156604 : CollatzResearch.WordTrace tailWord_3156604 prefixEnd_3156604 1620855087905073006033049 := by
  unfold tailWord_3156604
  simp only [CollatzResearch.WordTrace]
  refine ⟨57565403128085143943982433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76753870837446858591976577 57565403128085143943982433)
  ·
    refine ⟨43174052346063857957986825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57565403128085143943982433 43174052346063857957986825)
    ·
      refine ⟨32380539259547893468490119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43174052346063857957986825 32380539259547893468490119)
      ·
        refine ⟨48570808889321840202735179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32380539259547893468490119 48570808889321840202735179)
        ·
          refine ⟨72856213333982760304102769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48570808889321840202735179 72856213333982760304102769)
          ·
            refine ⟨54642160000487070228077077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72856213333982760304102769 54642160000487070228077077)
            ·
              refine ⟨2561351250022831416941113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54642160000487070228077077 2561351250022831416941113)
              ·
                refine ⟨1921013437517123562705835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561351250022831416941113 1921013437517123562705835)
                ·
                  refine ⟨2881520156275685344058753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921013437517123562705835 2881520156275685344058753)
                  ·
                    refine ⟨2161140117206764008044065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2881520156275685344058753 2161140117206764008044065)
                    ·
                      refine ⟨1620855087905073006033049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2161140117206764008044065 1620855087905073006033049)
                      ·
                        rfl

theorem cell23_3156604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_3156604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156604 prefixEnd_3156604 := by exact prefixLift 3156604
  have htrace : WordTrace (prefixWord ++ tailWord_3156604) baseStart_3156604 baseEnd_3156604 := by
    simpa [prefixWord, tailWord_3156604, baseEnd_3156604] using wordTrace_append hprefix tailTrace_3156604
  have hstable : (prefixWord ++ tailWord_3156604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156604).length < 2 ^ (prefixWord ++ tailWord_3156604).sum := by decide
  have hdescent : baseEnd_3156604 < baseStart_3156604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156643 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 3, 4, 2]
def baseStart_3156643 : Nat := 118140960795 + 3156643 * 2 ^ 59
def prefixEnd_3156643 : Nat := 4983230072969 + 3 ^ 40 * 3156643 * 2
def baseEnd_3156643 : Nat := 1620875113650598353445369

theorem tailTrace_3156643 : CollatzResearch.WordTrace tailWord_3156643 prefixEnd_3156643 1620875113650598353445369 := by
  unfold tailWord_3156643
  simp only [CollatzResearch.WordTrace]
  refine ⟨115132228703028997548634583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76754819135352665032423055 115132228703028997548634583)
  ·
    refine ⟨172698343054543496322951875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115132228703028997548634583 172698343054543496322951875)
    ·
      refine ⟨259047514581815244484427813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172698343054543496322951875 259047514581815244484427813)
      ·
        refine ⟨48571408984090358340830215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259047514581815244484427813 48571408984090358340830215)
        ·
          refine ⟨72857113476135537511245323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48571408984090358340830215 72857113476135537511245323)
          ·
            refine ⟨109285670214203306266867985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72857113476135537511245323 109285670214203306266867985)
            ·
              refine ⟨81964252660652479700150989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109285670214203306266867985 81964252660652479700150989)
              ·
                refine ⟨30736594747744679887556621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81964252660652479700150989 30736594747744679887556621)
                ·
                  refine ⟨11526223030404254957833733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30736594747744679887556621 11526223030404254957833733)
                  ·
                    refine ⟨2161166818200797804593825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11526223030404254957833733 2161166818200797804593825)
                    ·
                      refine ⟨1620875113650598353445369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2161166818200797804593825 1620875113650598353445369)
                      ·
                        rfl

theorem cell23_3156643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_3156643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156643 prefixEnd_3156643 := by exact prefixLift 3156643
  have htrace : WordTrace (prefixWord ++ tailWord_3156643) baseStart_3156643 baseEnd_3156643 := by
    simpa [prefixWord, tailWord_3156643, baseEnd_3156643] using wordTrace_append hprefix tailTrace_3156643
  have hstable : (prefixWord ++ tailWord_3156643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156643).length < 2 ^ (prefixWord ++ tailWord_3156643).sum := by decide
  have hdescent : baseEnd_3156643 < baseStart_3156643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156653 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_3156653 : Nat := 118140960795 + 3156653 * 2 ^ 59
def prefixEnd_3156653 : Nat := 4983230072969 + 3 ^ 40 * 3156653 * 2
def baseEnd_3156653 : Nat := 540293416152381104773441

theorem tailTrace_3156653 : CollatzResearch.WordTrace tailWord_3156653 prefixEnd_3156653 540293416152381104773441 := by
  unfold tailWord_3156653
  simp only [CollatzResearch.WordTrace]
  refine ⟨115132593432992769256498613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76755062288661846170999075 115132593432992769256498613)
  ·
    refine ⟨10793680634343072117796745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115132593432992769256498613 10793680634343072117796745)
    ·
      refine ⟨8095260475757304088347559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10793680634343072117796745 8095260475757304088347559)
      ·
        refine ⟨12142890713635956132521339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8095260475757304088347559 12142890713635956132521339)
        ·
          refine ⟨18214336070453934198782009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12142890713635956132521339 18214336070453934198782009)
          ·
            refine ⟨13660752052840450649086507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18214336070453934198782009 13660752052840450649086507)
            ·
              refine ⟨20491128079260675973629761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13660752052840450649086507 20491128079260675973629761)
              ·
                refine ⟨15368346059445506980222321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20491128079260675973629761 15368346059445506980222321)
                ·
                  refine ⟨11526259544584130235166741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15368346059445506980222321 11526259544584130235166741)
                  ·
                    refine ⟨540293416152381104773441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11526259544584130235166741 540293416152381104773441)
                    ·
                      rfl

theorem cell23_3156653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_3156653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156653 prefixEnd_3156653 := by exact prefixLift 3156653
  have htrace : WordTrace (prefixWord ++ tailWord_3156653) baseStart_3156653 baseEnd_3156653 := by
    simpa [prefixWord, tailWord_3156653, baseEnd_3156653] using wordTrace_append hprefix tailTrace_3156653
  have hstable : (prefixWord ++ tailWord_3156653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156653).length < 2 ^ (prefixWord ++ tailWord_3156653).sum := by decide
  have hdescent : baseEnd_3156653 < baseStart_3156653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156654 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3156654 : Nat := 118140960795 + 3156654 * 2 ^ 59
def prefixEnd_3156654 : Nat := 4983230072969 + 3 ^ 40 * 3156654 * 2
def baseEnd_3156654 : Nat := 1620880761937797810407819

theorem tailTrace_3156654 : CollatzResearch.WordTrace tailWord_3156654 prefixEnd_3156654 1620880761937797810407819 := by
  unfold tailWord_3156654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14391578738248643303410627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76755086603992764284856677 14391578738248643303410627)
  ·
    refine ⟨21587368107372964955115941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14391578738248643303410627 21587368107372964955115941)
    ·
      refine ⟨4047631520132430929084239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21587368107372964955115941 4047631520132430929084239)
      ·
        refine ⟨6071447280198646393626359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4047631520132430929084239 6071447280198646393626359)
        ·
          refine ⟨9107170920297969590439539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6071447280198646393626359 9107170920297969590439539)
          ·
            refine ⟨13660756380446954385659309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9107170920297969590439539 13660756380446954385659309)
            ·
              refine ⟨5122783642667607894622241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13660756380446954385659309 5122783642667607894622241)
              ·
                refine ⟨3842087732000705920966681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5122783642667607894622241 3842087732000705920966681)
                ·
                  refine ⟨2881565799000529440725011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3842087732000705920966681 2881565799000529440725011)
                  ·
                    refine ⟨4322348698500794161087517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2881565799000529440725011 4322348698500794161087517)
                    ·
                      refine ⟨1620880761937797810407819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4322348698500794161087517 1620880761937797810407819)
                      ·
                        rfl

theorem cell23_3156654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3156654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156654 prefixEnd_3156654 := by exact prefixLift 3156654
  have htrace : WordTrace (prefixWord ++ tailWord_3156654) baseStart_3156654 baseEnd_3156654 := by
    simpa [prefixWord, tailWord_3156654, baseEnd_3156654] using wordTrace_append hprefix tailTrace_3156654
  have hstable : (prefixWord ++ tailWord_3156654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156654).length < 2 ^ (prefixWord ++ tailWord_3156654).sum := by decide
  have hdescent : baseEnd_3156654 < baseStart_3156654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156717 : List Nat := [1, 5, 1, 2, 1, 1, 5, 2, 5]
def baseStart_3156717 : Nat := 118140960795 + 3156717 * 2 ^ 59
def prefixEnd_3156717 : Nat := 4983230072969 + 3 ^ 40 * 3156717 * 2
def baseEnd_3156717 : Nat := 180101456802114562657781

theorem tailTrace_3156717 : CollatzResearch.WordTrace tailWord_3156717 prefixEnd_3156717 180101456802114562657781 := by
  unfold tailWord_3156717
  simp only [CollatzResearch.WordTrace]
  refine ⟨115134927704760908186828405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76756618469840605457885603 115134927704760908186828405)
  ·
    refine ⟨10793899472321335142515163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115134927704760908186828405 10793899472321335142515163)
    ·
      refine ⟨16190849208482002713772745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10793899472321335142515163 16190849208482002713772745)
      ·
        refine ⟨12143136906361502035329559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16190849208482002713772745 12143136906361502035329559)
        ·
          refine ⟨18214705359542253052994339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12143136906361502035329559 18214705359542253052994339)
          ·
            refine ⟨27322058039313379579491509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18214705359542253052994339 27322058039313379579491509)
            ·
              refine ⟨2561442941185629335577329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27322058039313379579491509 2561442941185629335577329)
              ·
                refine ⟨1921082205889222001682997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561442941185629335577329 1921082205889222001682997)
                ·
                  refine ⟨180101456802114562657781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1921082205889222001682997 180101456802114562657781)
                  ·
                    rfl

theorem cell23_3156717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_3156717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156717 prefixEnd_3156717 := by exact prefixLift 3156717
  have htrace : WordTrace (prefixWord ++ tailWord_3156717) baseStart_3156717 baseEnd_3156717 := by
    simpa [prefixWord, tailWord_3156717, baseEnd_3156717] using wordTrace_append hprefix tailTrace_3156717
  have hstable : (prefixWord ++ tailWord_3156717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156717).length < 2 ^ (prefixWord ++ tailWord_3156717).sum := by decide
  have hdescent : baseEnd_3156717 < baseStart_3156717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156733 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_3156733 : Nat := 118140960795 + 3156733 * 2 ^ 59
def prefixEnd_3156733 : Nat := 4983230072969 + 3 ^ 40 * 3156733 * 2
def baseEnd_3156733 : Nat := 1620921326909503001319955

theorem tailTrace_3156733 : CollatzResearch.WordTrace tailWord_3156733 prefixEnd_3156733 1620921326909503001319955 := by
  unfold tailWord_3156733
  simp only [CollatzResearch.WordTrace]
  refine ⟨115135511272702942919410853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76757007515135295279607235 115135511272702942919410853)
  ·
    refine ⟨21587908363631801797389535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115135511272702942919410853 21587908363631801797389535)
    ·
      refine ⟨32381862545447702696084303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21587908363631801797389535 32381862545447702696084303)
      ·
        refine ⟨48572793818171554044126455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32381862545447702696084303 48572793818171554044126455)
        ·
          refine ⟨72859190727257331066189683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48572793818171554044126455 72859190727257331066189683)
          ·
            refine ⟨109288786090885996599284525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72859190727257331066189683 109288786090885996599284525)
            ·
              refine ⟨40983294784082248724731697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109288786090885996599284525 40983294784082248724731697)
              ·
                refine ⟨30737471088061686543548773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40983294784082248724731697 30737471088061686543548773)
                ·
                  refine ⟨5763275829011566226915395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30737471088061686543548773 5763275829011566226915395)
                  ·
                    refine ⟨8644913743517349340373093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5763275829011566226915395 8644913743517349340373093)
                    ·
                      refine ⟨1620921326909503001319955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8644913743517349340373093 1620921326909503001319955)
                      ·
                        rfl

theorem cell23_3156733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_3156733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156733 prefixEnd_3156733 := by exact prefixLift 3156733
  have htrace : WordTrace (prefixWord ++ tailWord_3156733) baseStart_3156733 baseEnd_3156733 := by
    simpa [prefixWord, tailWord_3156733, baseEnd_3156733] using wordTrace_append hprefix tailTrace_3156733
  have hstable : (prefixWord ++ tailWord_3156733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156733).length < 2 ^ (prefixWord ++ tailWord_3156733).sum := by decide
  have hdescent : baseEnd_3156733 < baseStart_3156733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156750 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2]
def baseStart_3156750 : Nat := 118140960795 + 3156750 * 2 ^ 59
def prefixEnd_3156750 : Nat := 4983230072969 + 3 ^ 40 * 3156750 * 2
def baseEnd_3156750 : Nat := 1620930056080629434807377

theorem tailTrace_3156750 : CollatzResearch.WordTrace tailWord_3156750 prefixEnd_3156750 1620930056080629434807377 := by
  unfold tailWord_3156750
  simp only [CollatzResearch.WordTrace]
  refine ⟨14392016414205169352847463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76757420875760903215186469 14392016414205169352847463)
  ·
    refine ⟨21588024621307754029271195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14392016414205169352847463 21588024621307754029271195)
    ·
      refine ⟨32382036931961631043906793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21588024621307754029271195 32382036931961631043906793)
      ·
        refine ⟨24286527698971223282930095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32382036931961631043906793 24286527698971223282930095)
        ·
          refine ⟨36429791548456834924395143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24286527698971223282930095 36429791548456834924395143)
          ·
            refine ⟨54644687322685252386592715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36429791548456834924395143 54644687322685252386592715)
            ·
              refine ⟨81967030984027878579889073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54644687322685252386592715 81967030984027878579889073)
              ·
                refine ⟨61475273238020908934916805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81967030984027878579889073 61475273238020908934916805)
                ·
                  refine ⟨11526613732128920425296901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61475273238020908934916805 11526613732128920425296901)
                  ·
                    refine ⟨2161240074774172579743169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11526613732128920425296901 2161240074774172579743169)
                    ·
                      refine ⟨1620930056080629434807377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2161240074774172579743169 1620930056080629434807377)
                      ·
                        rfl

theorem cell23_3156750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_3156750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156750 prefixEnd_3156750 := by exact prefixLift 3156750
  have htrace : WordTrace (prefixWord ++ tailWord_3156750) baseStart_3156750 baseEnd_3156750 := by
    simpa [prefixWord, tailWord_3156750, baseEnd_3156750] using wordTrace_append hprefix tailTrace_3156750
  have hstable : (prefixWord ++ tailWord_3156750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156750).length < 2 ^ (prefixWord ++ tailWord_3156750).sum := by decide
  have hdescent : baseEnd_3156750 < baseStart_3156750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156753 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 3]
def baseStart_3156753 : Nat := 118140960795 + 3156753 * 2 ^ 59
def prefixEnd_3156753 : Nat := 4983230072969 + 3 ^ 40 * 3156753 * 2
def baseEnd_3156753 : Nat := 1620931596522592923069863

theorem tailTrace_3156753 : CollatzResearch.WordTrace tailWord_3156753 prefixEnd_3156753 1620931596522592923069863 := by
  unfold tailWord_3156753
  simp only [CollatzResearch.WordTrace]
  refine ⟨115136240732630486335138913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76757493821753657556759275 115136240732630486335138913)
  ·
    refine ⟨86352180549472864751354185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115136240732630486335138913 86352180549472864751354185)
    ·
      refine ⟨64764135412104648563515639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86352180549472864751354185 64764135412104648563515639)
      ·
        refine ⟨97146203118156972845273459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64764135412104648563515639 97146203118156972845273459)
        ·
          refine ⟨145719304677235459267910189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97146203118156972845273459 145719304677235459267910189)
          ·
            refine ⟨54644739253963297225466321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145719304677235459267910189 54644739253963297225466321)
            ·
              refine ⟨40983554440472472919099741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54644739253963297225466321 40983554440472472919099741)
              ·
                refine ⟨15368832915177177344662403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40983554440472472919099741 15368832915177177344662403)
                ·
                  refine ⟨23053249372765766016993605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15368832915177177344662403 23053249372765766016993605)
                  ·
                    refine ⟨4322484257393581128186301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23053249372765766016993605 4322484257393581128186301)
                    ·
                      refine ⟨1620931596522592923069863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4322484257393581128186301 1620931596522592923069863)
                      ·
                        rfl

theorem cell23_3156753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_3156753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156753 prefixEnd_3156753 := by exact prefixLift 3156753
  have htrace : WordTrace (prefixWord ++ tailWord_3156753) baseStart_3156753 baseEnd_3156753 := by
    simpa [prefixWord, tailWord_3156753, baseEnd_3156753] using wordTrace_append hprefix tailTrace_3156753
  have hstable : (prefixWord ++ tailWord_3156753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156753).length < 2 ^ (prefixWord ++ tailWord_3156753).sum := by decide
  have hdescent : baseEnd_3156753 < baseStart_3156753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156801 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3156801 : Nat := 118140960795 + 3156801 * 2 ^ 59
def prefixEnd_3156801 : Nat := 4983230072969 + 3 ^ 40 * 3156801 * 2
def baseEnd_3156801 : Nat := 1620956243594008735269643

theorem tailTrace_3156801 : CollatzResearch.WordTrace tailWord_3156801 prefixEnd_3156801 1620956243594008735269643 := by
  unfold tailWord_3156801
  simp only [CollatzResearch.WordTrace]
  refine ⟨115137991436456590532886257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76758660957637727021924171 115137991436456590532886257)
  ·
    refine ⟨86353493577342442899664693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115137991436456590532886257 86353493577342442899664693)
    ·
      refine ⟨8095640022875854021843565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86353493577342442899664693 8095640022875854021843565)
      ·
        refine ⟨3035865008578445258191337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8095640022875854021843565 3035865008578445258191337)
        ·
          refine ⟨2276898756433833943643503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3035865008578445258191337 2276898756433833943643503)
          ·
            refine ⟨3415348134650750915465255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276898756433833943643503 3415348134650750915465255)
            ·
              refine ⟨5123022201976126373197883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415348134650750915465255 5123022201976126373197883)
              ·
                refine ⟨7684533302964189559796825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5123022201976126373197883 7684533302964189559796825)
                ·
                  refine ⟨5763399977223142169847619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7684533302964189559796825 5763399977223142169847619)
                  ·
                    refine ⟨8645099965834713254771429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5763399977223142169847619 8645099965834713254771429)
                    ·
                      refine ⟨1620956243594008735269643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8645099965834713254771429 1620956243594008735269643)
                      ·
                        rfl

theorem cell23_3156801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3156801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156801 prefixEnd_3156801 := by exact prefixLift 3156801
  have htrace : WordTrace (prefixWord ++ tailWord_3156801) baseStart_3156801 baseEnd_3156801 := by
    simpa [prefixWord, tailWord_3156801, baseEnd_3156801] using wordTrace_append hprefix tailTrace_3156801
  have hstable : (prefixWord ++ tailWord_3156801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156801).length < 2 ^ (prefixWord ++ tailWord_3156801).sum := by decide
  have hdescent : baseEnd_3156801 < baseStart_3156801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156803 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 3, 5]
def baseStart_3156803 : Nat := 118140960795 + 3156803 * 2 ^ 59
def prefixEnd_3156803 : Nat := 4983230072969 + 3 ^ 40 * 3156803 * 2
def baseEnd_3156803 : Nat := 540319090185105909148211

theorem tailTrace_3156803 : CollatzResearch.WordTrace tailWord_3156803 prefixEnd_3156803 540319090185105909148211 := by
  unfold tailWord_3156803
  simp only [CollatzResearch.WordTrace]
  refine ⟨115138064382449344874459063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76758709588299563249639375 115138064382449344874459063)
  ·
    refine ⟨172707096573674017311688595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115138064382449344874459063 172707096573674017311688595)
    ·
      refine ⟨259060644860511025967532893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172707096573674017311688595 259060644860511025967532893)
      ·
        refine ⟨97147741822691634737824835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259060644860511025967532893 97147741822691634737824835)
        ·
          refine ⟨145721612734037452106737253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97147741822691634737824835 145721612734037452106737253)
          ·
            refine ⟨27322802387632022270013235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145721612734037452106737253 27322802387632022270013235)
            ·
              refine ⟨40984203581448033405019853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27322802387632022270013235 40984203581448033405019853)
              ·
                refine ⟨15369076343043012526882445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40984203581448033405019853 15369076343043012526882445)
                ·
                  refine ⟨5763403628641129697580917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15369076343043012526882445 5763403628641129697580917)
                  ·
                    refine ⟨540319090185105909148211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5763403628641129697580917 540319090185105909148211)
                    ·
                      rfl

theorem cell23_3156803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 5].length) (baseStart_3156803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156803 prefixEnd_3156803 := by exact prefixLift 3156803
  have htrace : WordTrace (prefixWord ++ tailWord_3156803) baseStart_3156803 baseEnd_3156803 := by
    simpa [prefixWord, tailWord_3156803, baseEnd_3156803] using wordTrace_append hprefix tailTrace_3156803
  have hstable : (prefixWord ++ tailWord_3156803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156803).length < 2 ^ (prefixWord ++ tailWord_3156803).sum := by decide
  have hdescent : baseEnd_3156803 < baseStart_3156803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156804 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3156804 : Nat := 118140960795 + 3156804 * 2 ^ 59
def prefixEnd_3156804 : Nat := 4983230072969 + 3 ^ 40 * 3156804 * 2
def baseEnd_3156804 : Nat := 1620957784035972223532129

theorem tailTrace_3156804 : CollatzResearch.WordTrace tailWord_3156804 prefixEnd_3156804 1620957784035972223532129 := by
  unfold tailWord_3156804
  simp only [CollatzResearch.WordTrace]
  refine ⟨57569050427722861022622733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76758733903630481363496977 57569050427722861022622733)
  ·
    refine ⟨21588393910396072883483525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57569050427722861022622733 21588393910396072883483525)
    ·
      refine ⟨4047823858199263665653161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21588393910396072883483525 4047823858199263665653161)
      ·
        refine ⟨3035867893649447749239871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4047823858199263665653161 3035867893649447749239871)
        ·
          refine ⟨4553801840474171623859807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3035867893649447749239871 4553801840474171623859807)
          ·
            refine ⟨6830702760711257435789711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553801840474171623859807 6830702760711257435789711)
            ·
              refine ⟨10246054141066886153684567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6830702760711257435789711 10246054141066886153684567)
              ·
                refine ⟨15369081211600329230526851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10246054141066886153684567 15369081211600329230526851)
                ·
                  refine ⟨23053621817400493845790277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15369081211600329230526851 23053621817400493845790277)
                  ·
                    refine ⟨4322554090762592596085677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23053621817400493845790277 4322554090762592596085677)
                    ·
                      refine ⟨1620957784035972223532129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4322554090762592596085677 1620957784035972223532129)
                      ·
                        rfl

theorem cell23_3156804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3156804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156804 prefixEnd_3156804 := by exact prefixLift 3156804
  have htrace : WordTrace (prefixWord ++ tailWord_3156804) baseStart_3156804 baseEnd_3156804 := by
    simpa [prefixWord, tailWord_3156804, baseEnd_3156804] using wordTrace_append hprefix tailTrace_3156804
  have hstable : (prefixWord ++ tailWord_3156804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156804).length < 2 ^ (prefixWord ++ tailWord_3156804).sum := by decide
  have hdescent : baseEnd_3156804 < baseStart_3156804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156843 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 5]
def baseStart_3156843 : Nat := 118140960795 + 3156843 * 2 ^ 59
def prefixEnd_3156843 : Nat := 4983230072969 + 3 ^ 40 * 3156843 * 2
def baseEnd_3156843 : Nat := 1620977809781497570944449

theorem tailTrace_3156843 : CollatzResearch.WordTrace tailWord_3156843 prefixEnd_3156843 1620977809781497570944449 := by
  unfold tailWord_3156843
  simp only [CollatzResearch.WordTrace]
  refine ⟨115139523302304431705915183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76759682201536287803943455 115139523302304431705915183)
  ·
    refine ⟨172709284953456647558872775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115139523302304431705915183 172709284953456647558872775)
    ·
      refine ⟨259063927430184971338309163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172709284953456647558872775 259063927430184971338309163)
      ·
        refine ⟨388595891145277457007463745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259063927430184971338309163 388595891145277457007463745)
        ·
          refine ⟨291446918358958092755597809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388595891145277457007463745 291446918358958092755597809)
          ·
            refine ⟨218585188769218569566698357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291446918358958092755597809 218585188769218569566698357)
            ·
              refine ⟨20492361447114240896877971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218585188769218569566698357 20492361447114240896877971)
              ·
                refine ⟨30738542170671361345316957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20492361447114240896877971 30738542170671361345316957)
                ·
                  refine ⟨11526953314001760504493859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30738542170671361345316957 11526953314001760504493859)
                  ·
                    refine ⟨17290429971002640756740789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11526953314001760504493859 17290429971002640756740789)
                    ·
                      refine ⟨1620977809781497570944449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17290429971002640756740789 1620977809781497570944449)
                      ·
                        rfl

theorem cell23_3156843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 5].length) (baseStart_3156843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156843 prefixEnd_3156843 := by exact prefixLift 3156843
  have htrace : WordTrace (prefixWord ++ tailWord_3156843) baseStart_3156843 baseEnd_3156843 := by
    simpa [prefixWord, tailWord_3156843, baseEnd_3156843] using wordTrace_append hprefix tailTrace_3156843
  have hstable : (prefixWord ++ tailWord_3156843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156843).length < 2 ^ (prefixWord ++ tailWord_3156843).sum := by decide
  have hdescent : baseEnd_3156843 < baseStart_3156843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156850 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_3156850 : Nat := 118140960795 + 3156850 * 2 ^ 59
def prefixEnd_3156850 : Nat := 4983230072969 + 3 ^ 40 * 3156850 * 2
def baseEnd_3156850 : Nat := 540327134715359681185639

theorem tailTrace_3156850 : CollatzResearch.WordTrace tailWord_3156850 prefixEnd_3156850 540327134715359681185639 := by
  unfold tailWord_3156850
  simp only [CollatzResearch.WordTrace]
  refine ⟨28784944653319767975355001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76759852408852714600946669 28784944653319767975355001)
  ·
    refine ⟨21588708489989825981516251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28784944653319767975355001 21588708489989825981516251)
    ·
      refine ⟨32383062734984738972274377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21588708489989825981516251 32383062734984738972274377)
      ·
        refine ⟨24287297051238554229205783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32383062734984738972274377 24287297051238554229205783)
        ·
          refine ⟨36430945576857831343808675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24287297051238554229205783 36430945576857831343808675)
          ·
            refine ⟨54646418365286747015713013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36430945576857831343808675 54646418365286747015713013)
            ·
              refine ⟨5123101721745632532723095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54646418365286747015713013 5123101721745632532723095)
              ·
                refine ⟨7684652582618448799084643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5123101721745632532723095 7684652582618448799084643)
                ·
                  refine ⟨11526978873927673198626965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7684652582618448799084643 11526978873927673198626965)
                  ·
                    refine ⟨540327134715359681185639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11526978873927673198626965 540327134715359681185639)
                    ·
                      rfl

theorem cell23_3156850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_3156850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156850 prefixEnd_3156850 := by exact prefixLift 3156850
  have htrace : WordTrace (prefixWord ++ tailWord_3156850) baseStart_3156850 baseEnd_3156850 := by
    simpa [prefixWord, tailWord_3156850, baseEnd_3156850] using wordTrace_append hprefix tailTrace_3156850
  have hstable : (prefixWord ++ tailWord_3156850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156850).length < 2 ^ (prefixWord ++ tailWord_3156850).sum := by decide
  have hdescent : baseEnd_3156850 < baseStart_3156850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156854 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_3156854 : Nat := 118140960795 + 3156854 * 2 ^ 59
def prefixEnd_3156854 : Nat := 4983230072969 + 3 ^ 40 * 3156854 * 2
def baseEnd_3156854 : Nat := 540327819356232342635633

theorem tailTrace_3156854 : CollatzResearch.WordTrace tailWord_3156854 prefixEnd_3156854 540327819356232342635633 := by
  unfold tailWord_3156854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7196245281579036286535351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76759949670176387056377077 7196245281579036286535351)
  ·
    refine ⟨10794367922368554429803027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7196245281579036286535351 10794367922368554429803027)
    ·
      refine ⟨16191551883552831644704541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10794367922368554429803027 16191551883552831644704541)
      ·
        refine ⟨6071831956332311866764203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16191551883552831644704541 6071831956332311866764203)
        ·
          refine ⟨9107747934498467800146305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6071831956332311866764203 9107747934498467800146305)
          ·
            refine ⟨6830810950873850850109729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9107747934498467800146305 6830810950873850850109729)
            ·
              refine ⟨5123108213155388137582297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6830810950873850850109729 5123108213155388137582297)
              ·
                refine ⟨3842331159866541103186723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5123108213155388137582297 3842331159866541103186723)
                ·
                  refine ⟨5763496739799811654780085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3842331159866541103186723 5763496739799811654780085)
                  ·
                    refine ⟨540327819356232342635633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5763496739799811654780085 540327819356232342635633)
                    ·
                      rfl

theorem cell23_3156854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_3156854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156854 prefixEnd_3156854 := by exact prefixLift 3156854
  have htrace : WordTrace (prefixWord ++ tailWord_3156854) baseStart_3156854 baseEnd_3156854 := by
    simpa [prefixWord, tailWord_3156854, baseEnd_3156854] using wordTrace_append hprefix tailTrace_3156854
  have hstable : (prefixWord ++ tailWord_3156854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156854).length < 2 ^ (prefixWord ++ tailWord_3156854).sum := by decide
  have hdescent : baseEnd_3156854 < baseStart_3156854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156857 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 4]
def baseStart_3156857 : Nat := 118140960795 + 3156857 * 2 ^ 59
def prefixEnd_3156857 : Nat := 4983230072969 + 3 ^ 40 * 3156857 * 2
def baseEnd_3156857 : Nat := 1620984998510660516169385

theorem tailTrace_3156857 : CollatzResearch.WordTrace tailWord_3156857 prefixEnd_3156857 1620984998510660516169385 := by
  unfold tailWord_3156857
  simp only [CollatzResearch.WordTrace]
  refine ⟨115140033924253712096924825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76760022616169141397949883 115140033924253712096924825)
  ·
    refine ⟨86355025443190284072693619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115140033924253712096924825 86355025443190284072693619)
    ·
      refine ⟨129532538164785426109040429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86355025443190284072693619 129532538164785426109040429)
      ·
        refine ⟨48574701811794534790890161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129532538164785426109040429 48574701811794534790890161)
        ·
          refine ⟨36431026358845901093167621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48574701811794534790890161 36431026358845901093167621)
          ·
            refine ⟨6830817442283606454968929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36431026358845901093167621 6830817442283606454968929)
            ·
              refine ⟨5123113081712704841226697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6830817442283606454968929 5123113081712704841226697)
              ·
                refine ⟨3842334811284528630920023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5123113081712704841226697 3842334811284528630920023)
                ·
                  refine ⟨5763502216926792946380035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3842334811284528630920023 5763502216926792946380035)
                  ·
                    refine ⟨8645253325390189419570053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5763502216926792946380035 8645253325390189419570053)
                    ·
                      refine ⟨1620984998510660516169385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8645253325390189419570053 1620984998510660516169385)
                      ·
                        rfl

theorem cell23_3156857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_3156857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156857 prefixEnd_3156857 := by exact prefixLift 3156857
  have htrace : WordTrace (prefixWord ++ tailWord_3156857) baseStart_3156857 baseEnd_3156857 := by
    simpa [prefixWord, tailWord_3156857, baseEnd_3156857] using wordTrace_append hprefix tailTrace_3156857
  have hstable : (prefixWord ++ tailWord_3156857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156857).length < 2 ^ (prefixWord ++ tailWord_3156857).sum := by decide
  have hdescent : baseEnd_3156857 < baseStart_3156857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156860 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_3156860 : Nat := 118140960795 + 3156860 * 2 ^ 59
def prefixEnd_3156860 : Nat := 4983230072969 + 3 ^ 40 * 3156860 * 2
def baseEnd_3156860 : Nat := 1620986538952624004431871

theorem tailTrace_3156860 : CollatzResearch.WordTrace tailWord_3156860 prefixEnd_3156860 1620986538952624004431871 := by
  unfold tailWord_3156860
  simp only [CollatzResearch.WordTrace]
  refine ⟨57570071671621421804642017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76760095562161895739522689 57570071671621421804642017)
  ·
    refine ⟨43177553753716066353481513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57570071671621421804642017 43177553753716066353481513)
    ·
      refine ⟨32383165315287049765111135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43177553753716066353481513 32383165315287049765111135)
      ·
        refine ⟨48574747972930574647666703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32383165315287049765111135 48574747972930574647666703)
        ·
          refine ⟨72862121959395861971500055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48574747972930574647666703 72862121959395861971500055)
          ·
            refine ⟨109293182939093792957250083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72862121959395861971500055 109293182939093792957250083)
            ·
              refine ⟨163939774408640689435875125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109293182939093792957250083 163939774408640689435875125)
              ·
                refine ⟨15369353850810064634613293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163939774408640689435875125 15369353850810064634613293)
                ·
                  refine ⟨5763507694053774237979985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15369353850810064634613293 5763507694053774237979985)
                  ·
                    refine ⟨4322630770540330678484989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5763507694053774237979985 4322630770540330678484989)
                    ·
                      refine ⟨1620986538952624004431871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4322630770540330678484989 1620986538952624004431871)
                      ·
                        rfl

theorem cell23_3156860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_3156860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156860 prefixEnd_3156860 := by exact prefixLift 3156860
  have htrace : WordTrace (prefixWord ++ tailWord_3156860) baseStart_3156860 baseEnd_3156860 := by
    simpa [prefixWord, tailWord_3156860, baseEnd_3156860] using wordTrace_append hprefix tailTrace_3156860
  have hstable : (prefixWord ++ tailWord_3156860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156860).length < 2 ^ (prefixWord ++ tailWord_3156860).sum := by decide
  have hdescent : baseEnd_3156860 < baseStart_3156860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156907 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 2, 1, 3]
def baseStart_3156907 : Nat := 118140960795 + 3156907 * 2 ^ 59
def prefixEnd_3156907 : Nat := 4983230072969 + 3 ^ 40 * 3156907 * 2
def baseEnd_3156907 : Nat := 1621010672543385320544155

theorem tailTrace_3156907 : CollatzResearch.WordTrace tailWord_3156907 prefixEnd_3156907 1621010672543385320544155 := by
  unfold tailWord_3156907
  simp only [CollatzResearch.WordTrace]
  refine ⟨115141857574072570636244975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76761238382715047090829983 115141857574072570636244975)
  ·
    refine ⟨172712786361108855954367463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115141857574072570636244975 172712786361108855954367463)
    ·
      refine ⟨259069179541663283931551195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172712786361108855954367463 259069179541663283931551195)
      ·
        refine ⟨388603769312494925897326793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259069179541663283931551195 388603769312494925897326793)
        ·
          refine ⟨291452826984371194422995095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388603769312494925897326793 291452826984371194422995095)
          ·
            refine ⟨437179240476556791634492643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291452826984371194422995095 437179240476556791634492643)
            ·
              refine ⟨655768860714835187451738965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437179240476556791634492643 655768860714835187451738965)
              ·
                refine ⟨3842395668250987426475033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 655768860714835187451738965 3842395668250987426475033)
                ·
                  refine ⟨2881796751188240569856275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3842395668250987426475033 2881796751188240569856275)
                  ·
                    refine ⟨4322695126782360854784413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2881796751188240569856275 4322695126782360854784413)
                    ·
                      refine ⟨1621010672543385320544155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4322695126782360854784413 1621010672543385320544155)
                      ·
                        rfl

theorem cell23_3156907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 1, 3].length) (baseStart_3156907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156907 prefixEnd_3156907 := by exact prefixLift 3156907
  have htrace : WordTrace (prefixWord ++ tailWord_3156907) baseStart_3156907 baseEnd_3156907 := by
    simpa [prefixWord, tailWord_3156907, baseEnd_3156907] using wordTrace_append hprefix tailTrace_3156907
  have hstable : (prefixWord ++ tailWord_3156907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156907).length < 2 ^ (prefixWord ++ tailWord_3156907).sum := by decide
  have hdescent : baseEnd_3156907 < baseStart_3156907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156940 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_3156940 : Nat := 118140960795 + 3156940 * 2 ^ 59
def prefixEnd_3156940 : Nat := 4983230072969 + 3 ^ 40 * 3156940 * 2
def baseEnd_3156940 : Nat := 540342539134994563810501

theorem tailTrace_3156940 : CollatzResearch.WordTrace tailWord_3156940 prefixEnd_3156940 540342539134994563810501 := by
  unfold tailWord_3156940
  simp only [CollatzResearch.WordTrace]
  refine ⟨57571530591476508636098137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76762040788635344848130849 57571530591476508636098137)
  ·
    refine ⟨43178647943607381477073603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57571530591476508636098137 43178647943607381477073603)
    ·
      refine ⟨64767971915411072215610405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43178647943607381477073603 64767971915411072215610405)
      ·
        refine ⟨12143994734139576040426951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64767971915411072215610405 12143994734139576040426951)
        ·
          refine ⟨18215992101209364060640427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12143994734139576040426951 18215992101209364060640427)
          ·
            refine ⟨27323988151814046090960641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18215992101209364060640427 27323988151814046090960641)
            ·
              refine ⟨20492991113860534568220481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27323988151814046090960641 20492991113860534568220481)
              ·
                refine ⟨15369743335395400926165361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20492991113860534568220481 15369743335395400926165361)
                ·
                  refine ⟨11527307501546550694624021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15369743335395400926165361 11527307501546550694624021)
                  ·
                    refine ⟨540342539134994563810501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11527307501546550694624021 540342539134994563810501)
                    ·
                      rfl

theorem cell23_3156940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_3156940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156940 prefixEnd_3156940 := by exact prefixLift 3156940
  have htrace : WordTrace (prefixWord ++ tailWord_3156940) baseStart_3156940 baseEnd_3156940 := by
    simpa [prefixWord, tailWord_3156940, baseEnd_3156940] using wordTrace_append hprefix tailTrace_3156940
  have hstable : (prefixWord ++ tailWord_3156940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156940).length < 2 ^ (prefixWord ++ tailWord_3156940).sum := by decide
  have hdescent : baseEnd_3156940 < baseStart_3156940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
