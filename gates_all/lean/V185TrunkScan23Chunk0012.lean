import V185TrunkScan23Chunk0011

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_70279 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 1, 3, 2]
def baseStart_70279 : Nat := 118140960795 + 70279 * 2 ^ 59
def prefixEnd_70279 : Nat := 4983230072969 + 3 ^ 40 * 70279 * 2
def baseEnd_70279 : Nat := 36086906917435766789299

theorem tailTrace_70279 : CollatzResearch.WordTrace tailWord_70279 prefixEnd_70279 36086906917435766789299 := by
  unfold tailWord_70279
  simp only [CollatzResearch.WordTrace]
  refine ⟨2563285712398660542725891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1708857141599107028483927 2563285712398660542725891)
  ·
    refine ⟨3844928568597990814088837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2563285712398660542725891 3844928568597990814088837)
    ·
      refine ⟨720924106612123277641657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3844928568597990814088837 720924106612123277641657)
      ·
        refine ⟨540693079959092458231243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 720924106612123277641657 540693079959092458231243)
        ·
          refine ⟨811039619938638687346865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540693079959092458231243 811039619938638687346865)
          ·
            refine ⟨608279714953979015510149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811039619938638687346865 608279714953979015510149)
            ·
              refine ⟨114052446553871065408153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 608279714953979015510149 114052446553871065408153)
              ·
                refine ⟨85539334915403299056115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114052446553871065408153 85539334915403299056115)
                ·
                  refine ⟨128309002373104948584173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85539334915403299056115 128309002373104948584173)
                  ·
                    refine ⟨48115875889914355719065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128309002373104948584173 48115875889914355719065)
                    ·
                      refine ⟨36086906917435766789299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48115875889914355719065 36086906917435766789299)
                      ·
                        rfl

theorem cell23_70279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_70279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70279 prefixEnd_70279 := by exact prefixLift 70279
  have htrace : WordTrace (prefixWord ++ tailWord_70279) baseStart_70279 baseEnd_70279 := by
    simpa [prefixWord, tailWord_70279, baseEnd_70279] using wordTrace_append hprefix tailTrace_70279
  have hstable : (prefixWord ++ tailWord_70279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70279).length < 2 ^ (prefixWord ++ tailWord_70279).sum := by decide
  have hdescent : baseEnd_70279 < baseStart_70279 := by decide
  rcases family_descends (prefixWord ++ tailWord_70279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70295 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_70295 : Nat := 118140960795 + 70295 * 2 ^ 59
def prefixEnd_70295 : Nat := 4983230072969 + 3 ^ 40 * 70295 * 2
def baseEnd_70295 : Nat := 36095122607907704189225

theorem tailTrace_70295 : CollatzResearch.WordTrace tailWord_70295 prefixEnd_70295 36095122607907704189225 := by
  unfold tailWord_70295
  simp only [CollatzResearch.WordTrace]
  refine ⟨2563869280340695275308339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1709246186893796850205559 2563869280340695275308339)
  ·
    refine ⟨3845803920511042912962509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2563869280340695275308339 3845803920511042912962509)
    ·
      refine ⟨1442176470191641092360941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3845803920511042912962509 1442176470191641092360941)
      ·
        refine ⟨540816176321865409635353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1442176470191641092360941 540816176321865409635353)
        ·
          refine ⟨405612132241399057226515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540816176321865409635353 405612132241399057226515)
          ·
            refine ⟨608418198362098585839773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405612132241399057226515 608418198362098585839773)
            ·
              refine ⟨228156824385786969689915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 608418198362098585839773 228156824385786969689915)
              ·
                refine ⟨342235236578680454534873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228156824385786969689915 342235236578680454534873)
                ·
                  refine ⟨256676427434010340901155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342235236578680454534873 256676427434010340901155)
                  ·
                    refine ⟨385014641151015511351733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 256676427434010340901155 385014641151015511351733)
                    ·
                      refine ⟨36095122607907704189225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 385014641151015511351733 36095122607907704189225)
                      ·
                        rfl

theorem cell23_70295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_70295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70295 prefixEnd_70295 := by exact prefixLift 70295
  have htrace : WordTrace (prefixWord ++ tailWord_70295) baseStart_70295 baseEnd_70295 := by
    simpa [prefixWord, tailWord_70295, baseEnd_70295] using wordTrace_append hprefix tailTrace_70295
  have hstable : (prefixWord ++ tailWord_70295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70295).length < 2 ^ (prefixWord ++ tailWord_70295).sum := by decide
  have hdescent : baseEnd_70295 < baseStart_70295 := by decide
  rcases family_descends (prefixWord ++ tailWord_70295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70309 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 2, 2, 2]
def baseStart_70309 : Nat := 118140960795 + 70309 * 2 ^ 59
def prefixEnd_70309 : Nat := 4983230072969 + 3 ^ 40 * 70309 * 2
def baseEnd_70309 : Nat := 36102311337070649414161

theorem tailTrace_70309 : CollatzResearch.WordTrace tailWord_70309 prefixEnd_70309 36102311337070649414161 := by
  unfold tailWord_70309
  simp only [CollatzResearch.WordTrace]
  refine ⟨2564379902289975666317981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1709586601526650444211987 2564379902289975666317981)
  ·
    refine ⟨961642463358740874869243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2564379902289975666317981 961642463358740874869243)
    ·
      refine ⟨1442463695038111312303865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 961642463358740874869243 1442463695038111312303865)
      ·
        refine ⟨1081847771278583484227899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1442463695038111312303865 1081847771278583484227899)
        ·
          refine ⟨1622771656917875226341849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081847771278583484227899 1622771656917875226341849)
          ·
            refine ⟨1217078742688406419756387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1622771656917875226341849 1217078742688406419756387)
            ·
              refine ⟨1825618114032609629634581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217078742688406419756387 1825618114032609629634581)
              ·
                refine ⟨85575849095278576389121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1825618114032609629634581 85575849095278576389121)
                ·
                  refine ⟨64181886821458932291841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85575849095278576389121 64181886821458932291841)
                  ·
                    refine ⟨48136415116094199218881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64181886821458932291841 48136415116094199218881)
                    ·
                      refine ⟨36102311337070649414161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48136415116094199218881 36102311337070649414161)
                      ·
                        rfl

theorem cell23_70309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_70309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70309 prefixEnd_70309 := by exact prefixLift 70309
  have htrace : WordTrace (prefixWord ++ tailWord_70309) baseStart_70309 baseEnd_70309 := by
    simpa [prefixWord, tailWord_70309, baseEnd_70309] using wordTrace_append hprefix tailTrace_70309
  have hstable : (prefixWord ++ tailWord_70309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70309).length < 2 ^ (prefixWord ++ tailWord_70309).sum := by decide
  have hdescent : baseEnd_70309 < baseStart_70309 := by decide
  rcases family_descends (prefixWord ++ tailWord_70309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70392 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 3, 4]
def baseStart_70392 : Nat := 118140960795 + 70392 * 2 ^ 59
def prefixEnd_70392 : Nat := 4983230072969 + 3 ^ 40 * 70392 * 2
def baseEnd_70392 : Nat := 12048310077131274892093

theorem tailTrace_70392 : CollatzResearch.WordTrace tailWord_70392 prefixEnd_70392 12048310077131274892093 := by
  unfold tailWord_70392
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283703580494640420794715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1711604773992853894392953 1283703580494640420794715)
  ·
    refine ⟨1925555370741960631192073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1283703580494640420794715 1925555370741960631192073)
    ·
      refine ⟨1444166528056470473394055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1925555370741960631192073 1444166528056470473394055)
      ·
        refine ⟨2166249792084705710091083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444166528056470473394055 2166249792084705710091083)
        ·
          refine ⟨3249374688127058565136625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166249792084705710091083 3249374688127058565136625)
          ·
            refine ⟨2437031016095293923852469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3249374688127058565136625 2437031016095293923852469)
            ·
              refine ⟨228471657758933805361169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2437031016095293923852469 228471657758933805361169)
              ·
                refine ⟨171353743319200354020877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228471657758933805361169 171353743319200354020877)
                ·
                  refine ⟨64257653744700132757829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171353743319200354020877 64257653744700132757829)
                  ·
                    refine ⟨12048310077131274892093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64257653744700132757829 12048310077131274892093)
                    ·
                      rfl

theorem cell23_70392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_70392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70392 prefixEnd_70392 := by exact prefixLift 70392
  have htrace : WordTrace (prefixWord ++ tailWord_70392) baseStart_70392 baseEnd_70392 := by
    simpa [prefixWord, tailWord_70392, baseEnd_70392] using wordTrace_append hprefix tailTrace_70392
  have hstable : (prefixWord ++ tailWord_70392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70392).length < 2 ^ (prefixWord ++ tailWord_70392).sum := by decide
  have hdescent : baseEnd_70392 < baseStart_70392 := by decide
  rcases family_descends (prefixWord ++ tailWord_70392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70409 : List Nat := [1, 2, 1, 1, 3, 2, 3, 5, 1, 4]
def baseStart_70409 : Nat := 118140960795 + 70409 * 2 ^ 59
def prefixEnd_70409 : Nat := 4983230072969 + 3 ^ 40 * 70409 * 2
def baseEnd_70409 : Nat := 12051219800840086054567

theorem tailTrace_70409 : CollatzResearch.WordTrace tailWord_70409 prefixEnd_70409 12051219800840086054567 := by
  unfold tailWord_70409
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568027201927692744958281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1712018134618461829972187 2568027201927692744958281)
  ·
    refine ⟨1926020401445769558718711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2568027201927692744958281 1926020401445769558718711)
    ·
      refine ⟨2889030602168654338078067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1926020401445769558718711 2889030602168654338078067)
      ·
        refine ⟨4333545903252981507117101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889030602168654338078067 4333545903252981507117101)
        ·
          refine ⟨1625079713719868065168913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4333545903252981507117101 1625079713719868065168913)
          ·
            refine ⟨1218809785289901048876685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1625079713719868065168913 1218809785289901048876685)
            ·
              refine ⟨457053669483712893328757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1218809785289901048876685 457053669483712893328757)
              ·
                refine ⟨42848781514098083749571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 457053669483712893328757 42848781514098083749571)
                ·
                  refine ⟨64273172271147125624357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42848781514098083749571 64273172271147125624357)
                  ·
                    refine ⟨12051219800840086054567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64273172271147125624357 12051219800840086054567)
                    ·
                      rfl

theorem cell23_70409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 1, 4].length) (baseStart_70409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70409 prefixEnd_70409 := by exact prefixLift 70409
  have htrace : WordTrace (prefixWord ++ tailWord_70409) baseStart_70409 baseEnd_70409 := by
    simpa [prefixWord, tailWord_70409, baseEnd_70409] using wordTrace_append hprefix tailTrace_70409
  have hstable : (prefixWord ++ tailWord_70409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70409).length < 2 ^ (prefixWord ++ tailWord_70409).sum := by decide
  have hdescent : baseEnd_70409 < baseStart_70409 := by decide
  rcases family_descends (prefixWord ++ tailWord_70409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70449 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 3, 1, 3]
def baseStart_70449 : Nat := 118140960795 + 70449 * 2 ^ 59
def prefixEnd_70449 : Nat := 4983230072969 + 3 ^ 40 * 70449 * 2
def baseEnd_70449 : Nat := 36174198628700101663517

theorem tailTrace_70449 : CollatzResearch.WordTrace tailWord_70449 prefixEnd_70449 36174198628700101663517 := by
  unfold tailWord_70449
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569486121782779576414401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1712990747855186384276267 2569486121782779576414401)
  ·
    refine ⟨1927114591337084682310801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2569486121782779576414401 1927114591337084682310801)
    ·
      refine ⟨1445335943502813511733101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1927114591337084682310801 1445335943502813511733101)
      ·
        refine ⟨542000978813555066899913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1445335943502813511733101 542000978813555066899913)
        ·
          refine ⟨406500734110166300174935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542000978813555066899913 406500734110166300174935)
          ·
            refine ⟨609751101165249450262403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406500734110166300174935 609751101165249450262403)
            ·
              refine ⟨914626651747874175393605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609751101165249450262403 914626651747874175393605)
              ·
                refine ⟨171492497202726407886301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 914626651747874175393605 171492497202726407886301)
                ·
                  refine ⟨64309686451022402957363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171492497202726407886301 64309686451022402957363)
                  ·
                    refine ⟨96464529676533604436045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64309686451022402957363 96464529676533604436045)
                    ·
                      refine ⟨36174198628700101663517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 96464529676533604436045 36174198628700101663517)
                      ·
                        rfl

theorem cell23_70449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_70449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70449 prefixEnd_70449 := by exact prefixLift 70449
  have htrace : WordTrace (prefixWord ++ tailWord_70449) baseStart_70449 baseEnd_70449 := by
    simpa [prefixWord, tailWord_70449, baseEnd_70449] using wordTrace_append hprefix tailTrace_70449
  have hstable : (prefixWord ++ tailWord_70449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70449).length < 2 ^ (prefixWord ++ tailWord_70449).sum := by decide
  have hdescent : baseEnd_70449 < baseStart_70449 := by decide
  rcases family_descends (prefixWord ++ tailWord_70449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70476 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 2, 3, 2]
def baseStart_70476 : Nat := 118140960795 + 70476 * 2 ^ 59
def prefixEnd_70476 : Nat := 4983230072969 + 3 ^ 40 * 70476 * 2
def baseEnd_70476 : Nat := 36188062606371496025893

theorem tailTrace_70476 : CollatzResearch.WordTrace tailWord_70476 prefixEnd_70476 36188062606371496025893 := by
  unfold tailWord_70476
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285235446342481593823641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1713647261789975458431521 1285235446342481593823641)
  ·
    refine ⟨963926584756861195367731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1285235446342481593823641 963926584756861195367731)
    ·
      refine ⟨1445889877135291793051597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 963926584756861195367731 1445889877135291793051597)
      ·
        refine ⟨542208703925734422394349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1445889877135291793051597 542208703925734422394349)
        ·
          refine ⟨203328263972150408397881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 542208703925734422394349 203328263972150408397881)
          ·
            refine ⟨152496197979112806298411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203328263972150408397881 152496197979112806298411)
            ·
              refine ⟨228744296968669209447617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152496197979112806298411 228744296968669209447617)
              ·
                refine ⟨171558222726501907085713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228744296968669209447617 171558222726501907085713)
                ·
                  refine ⟨128668667044876430314285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171558222726501907085713 128668667044876430314285)
                  ·
                    refine ⟨48250750141828661367857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128668667044876430314285 48250750141828661367857)
                    ·
                      refine ⟨36188062606371496025893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48250750141828661367857 36188062606371496025893)
                      ·
                        rfl

theorem cell23_70476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_70476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70476 prefixEnd_70476 := by exact prefixLift 70476
  have htrace : WordTrace (prefixWord ++ tailWord_70476) baseStart_70476 baseEnd_70476 := by
    simpa [prefixWord, tailWord_70476, baseEnd_70476] using wordTrace_append hprefix tailTrace_70476
  have hstable : (prefixWord ++ tailWord_70476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70476).length < 2 ^ (prefixWord ++ tailWord_70476).sum := by decide
  have hdescent : baseEnd_70476 < baseStart_70476 := by decide
  rcases family_descends (prefixWord ++ tailWord_70476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70539 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 4, 1, 3]
def baseStart_70539 : Nat := 118140960795 + 70539 * 2 ^ 59
def prefixEnd_70539 : Nat := 4983230072969 + 3 ^ 40 * 70539 * 2
def baseEnd_70539 : Nat := 36220411887604749538103

theorem tailTrace_70539 : CollatzResearch.WordTrace tailWord_70539 prefixEnd_70539 36220411887604749538103 := by
  unfold tailWord_70539
  simp only [CollatzResearch.WordTrace]
  refine ⟨2572768691456724947190671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1715179127637816631460447 2572768691456724947190671)
  ·
    refine ⟨3859153037185087420786007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2572768691456724947190671 3859153037185087420786007)
    ·
      refine ⟨5788729555777631131179011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3859153037185087420786007 5788729555777631131179011)
      ·
        refine ⟨8683094333666446696768517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5788729555777631131179011 8683094333666446696768517)
        ·
          refine ⟨1628080187562458755644097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8683094333666446696768517 1628080187562458755644097)
          ·
            refine ⟨1221060140671844066733073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1628080187562458755644097 1221060140671844066733073)
            ·
              refine ⟨915795105503883050049805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1221060140671844066733073 915795105503883050049805)
              ·
                refine ⟨343423164563956143768677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 915795105503883050049805 343423164563956143768677)
                ·
                  refine ⟨64391843355741776956627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343423164563956143768677 64391843355741776956627)
                  ·
                    refine ⟨96587765033612665434941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64391843355741776956627 96587765033612665434941)
                    ·
                      refine ⟨36220411887604749538103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 96587765033612665434941 36220411887604749538103)
                      ·
                        rfl

theorem cell23_70539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 1, 3].length) (baseStart_70539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70539 prefixEnd_70539 := by exact prefixLift 70539
  have htrace : WordTrace (prefixWord ++ tailWord_70539) baseStart_70539 baseEnd_70539 := by
    simpa [prefixWord, tailWord_70539, baseEnd_70539] using wordTrace_append hprefix tailTrace_70539
  have hstable : (prefixWord ++ tailWord_70539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70539).length < 2 ^ (prefixWord ++ tailWord_70539).sum := by decide
  have hdescent : baseEnd_70539 < baseStart_70539 := by decide
  rcases family_descends (prefixWord ++ tailWord_70539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70540 : List Nat := [2, 2, 1, 2, 1, 2, 6, 2, 1, 2, 2]
def baseStart_70540 : Nat := 118140960795 + 70540 * 2 ^ 59
def prefixEnd_70540 : Nat := 4983230072969 + 3 ^ 40 * 70540 * 2
def baseEnd_70540 : Nat := 36220925368259245625599

theorem tailTrace_70540 : CollatzResearch.WordTrace tailWord_70540 prefixEnd_70540 36220925368259245625599 := by
  unfold tailWord_70540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1286402582226551058988537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1715203442968734745318049 1286402582226551058988537)
  ·
    refine ⟨964801936669913294241403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1286402582226551058988537 964801936669913294241403)
    ·
      refine ⟨1447202905004869941362105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 964801936669913294241403 1447202905004869941362105)
      ·
        refine ⟨1085402178753652456021579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1447202905004869941362105 1085402178753652456021579)
        ·
          refine ⟨1628103268130478684032369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085402178753652456021579 1628103268130478684032369)
          ·
            refine ⟨1221077451097859013024277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1628103268130478684032369 1221077451097859013024277)
            ·
              refine ⟨57238005520212141235513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1221077451097859013024277 57238005520212141235513)
              ·
                refine ⟨42928504140159105926635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57238005520212141235513 42928504140159105926635)
                ·
                  refine ⟨64392756210238658889953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42928504140159105926635 64392756210238658889953)
                  ·
                    refine ⟨48294567157678994167465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64392756210238658889953 48294567157678994167465)
                    ·
                      refine ⟨36220925368259245625599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48294567157678994167465 36220925368259245625599)
                      ·
                        rfl

theorem cell23_70540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_70540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70540 prefixEnd_70540 := by exact prefixLift 70540
  have htrace : WordTrace (prefixWord ++ tailWord_70540) baseStart_70540 baseEnd_70540 := by
    simpa [prefixWord, tailWord_70540, baseEnd_70540] using wordTrace_append hprefix tailTrace_70540
  have hstable : (prefixWord ++ tailWord_70540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70540).length < 2 ^ (prefixWord ++ tailWord_70540).sum := by decide
  have hdescent : baseEnd_70540 < baseStart_70540 := by decide
  rcases family_descends (prefixWord ++ tailWord_70540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70546 : List Nat := [3, 2, 3, 2, 2, 2, 1, 8]
def baseStart_70546 : Nat := 118140960795 + 70546 * 2 ^ 59
def prefixEnd_70546 : Nat := 4983230072969 + 3 ^ 40 * 70546 * 2
def baseEnd_70546 : Nat := 1341629861192082301873

theorem tailTrace_70546 : CollatzResearch.WordTrace tailWord_70546 prefixEnd_70546 1341629861192082301873 := by
  unfold tailWord_70546
  simp only [CollatzResearch.WordTrace]
  refine ⟨643256000607841285673873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1715349334954243428463661 643256000607841285673873)
  ·
    refine ⟨482442000455880964255405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 643256000607841285673873 482442000455880964255405)
    ·
      refine ⟨180915750170955361595777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 482442000455880964255405 180915750170955361595777)
      ·
        refine ⟨135686812628216521196833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180915750170955361595777 135686812628216521196833)
        ·
          refine ⟨101765109471162390897625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135686812628216521196833 101765109471162390897625)
          ·
            refine ⟨76323832103371793173219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101765109471162390897625 76323832103371793173219)
            ·
              refine ⟨114485748155057689759829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76323832103371793173219 114485748155057689759829)
              ·
                refine ⟨1341629861192082301873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 114485748155057689759829 1341629861192082301873)
                ·
                  rfl

theorem cell23_70546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 8].length) (baseStart_70546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70546 prefixEnd_70546 := by exact prefixLift 70546
  have htrace : WordTrace (prefixWord ++ tailWord_70546) baseStart_70546 baseEnd_70546 := by
    simpa [prefixWord, tailWord_70546, baseEnd_70546] using wordTrace_append hprefix tailTrace_70546
  have hstable : (prefixWord ++ tailWord_70546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70546).length < 2 ^ (prefixWord ++ tailWord_70546).sum := by decide
  have hdescent : baseEnd_70546 < baseStart_70546 := by decide
  rcases family_descends (prefixWord ++ tailWord_70546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70550 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_70550 : Nat := 118140960795 + 70550 * 2 ^ 59
def prefixEnd_70550 : Nat := 4983230072969 + 3 ^ 40 * 70550 * 2
def baseEnd_70550 : Nat := 12075353391601402166851

theorem tailTrace_70550 : CollatzResearch.WordTrace tailWord_70550 prefixEnd_70550 12075353391601402166851 := by
  unfold tailWord_70550
  simp only [CollatzResearch.WordTrace]
  refine ⟨160823118401054614115069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1715446596277915883894069 160823118401054614115069)
  ·
    refine ⟨60308669400395480293151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160823118401054614115069 60308669400395480293151)
    ·
      refine ⟨90463004100593220439727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60308669400395480293151 90463004100593220439727)
      ·
        refine ⟨135694506150889830659591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90463004100593220439727 135694506150889830659591)
        ·
          refine ⟨203541759226334745989387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135694506150889830659591 203541759226334745989387)
          ·
            refine ⟨305312638839502118984081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203541759226334745989387 305312638839502118984081)
            ·
              refine ⟨228984479129626589238061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305312638839502118984081 228984479129626589238061)
              ·
                refine ⟨85869179673609970964273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228984479129626589238061 85869179673609970964273)
                ·
                  refine ⟨64401884755207478223205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85869179673609970964273 64401884755207478223205)
                  ·
                    refine ⟨12075353391601402166851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64401884755207478223205 12075353391601402166851)
                    ·
                      rfl

theorem cell23_70550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_70550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70550 prefixEnd_70550 := by exact prefixLift 70550
  have htrace : WordTrace (prefixWord ++ tailWord_70550) baseStart_70550 baseEnd_70550 := by
    simpa [prefixWord, tailWord_70550, baseEnd_70550] using wordTrace_append hprefix tailTrace_70550
  have hstable : (prefixWord ++ tailWord_70550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70550).length < 2 ^ (prefixWord ++ tailWord_70550).sum := by decide
  have hdescent : baseEnd_70550 < baseStart_70550 := by decide
  rcases family_descends (prefixWord ++ tailWord_70550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70579 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 3, 4, 2]
def baseStart_70579 : Nat := 118140960795 + 70579 * 2 ^ 59
def prefixEnd_70579 : Nat := 4983230072969 + 3 ^ 40 * 70579 * 2
def baseEnd_70579 : Nat := 36240951113784593037919

theorem tailTrace_70579 : CollatzResearch.WordTrace tailWord_70579 prefixEnd_70579 36240951113784593037919 := by
  unfold tailWord_70579
  simp only [CollatzResearch.WordTrace]
  refine ⟨2574227611311811778646791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1716151740874541185764527 2574227611311811778646791)
  ·
    refine ⟨3861341416967717667970187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2574227611311811778646791 3861341416967717667970187)
    ·
      refine ⟨5792012125451576501955281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3861341416967717667970187 5792012125451576501955281)
      ·
        refine ⟨4344009094088682376466461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5792012125451576501955281 4344009094088682376466461)
        ·
          refine ⟨1629003410283255891174923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4344009094088682376466461 1629003410283255891174923)
          ·
            refine ⟨2443505115424883836762385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629003410283255891174923 2443505115424883836762385)
            ·
              refine ⟨1832628836568662877571789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2443505115424883836762385 1832628836568662877571789)
              ·
                refine ⟨687235813713248579089421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1832628836568662877571789 687235813713248579089421)
                ·
                  refine ⟨257713430142468217158533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 687235813713248579089421 257713430142468217158533)
                  ·
                    refine ⟨48321268151712790717225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 257713430142468217158533 48321268151712790717225)
                    ·
                      refine ⟨36240951113784593037919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48321268151712790717225 36240951113784593037919)
                      ·
                        rfl

theorem cell23_70579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 4, 2].length) (baseStart_70579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70579 prefixEnd_70579 := by exact prefixLift 70579
  have htrace : WordTrace (prefixWord ++ tailWord_70579) baseStart_70579 baseEnd_70579 := by
    simpa [prefixWord, tailWord_70579, baseEnd_70579] using wordTrace_append hprefix tailTrace_70579
  have hstable : (prefixWord ++ tailWord_70579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70579).length < 2 ^ (prefixWord ++ tailWord_70579).sum := by decide
  have hdescent : baseEnd_70579 < baseStart_70579 := by decide
  rcases family_descends (prefixWord ++ tailWord_70579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70583 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 1, 3, 2]
def baseStart_70583 : Nat := 118140960795 + 70583 * 2 ^ 59
def prefixEnd_70583 : Nat := 4983230072969 + 3 ^ 40 * 70583 * 2
def baseEnd_70583 : Nat := 36243005036402577387901

theorem tailTrace_70583 : CollatzResearch.WordTrace tailWord_70583 prefixEnd_70583 36243005036402577387901 := by
  unfold tailWord_70583
  simp only [CollatzResearch.WordTrace]
  refine ⟨2574373503297320461792403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1716249002198213641194935 2574373503297320461792403)
  ·
    refine ⟨3861560254945980692688605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2574373503297320461792403 3861560254945980692688605)
    ·
      refine ⟨1448085095604742759758227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3861560254945980692688605 1448085095604742759758227)
      ·
        refine ⟨2172127643407114139637341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448085095604742759758227 2172127643407114139637341)
        ·
          refine ⟨814547866277667802364003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2172127643407114139637341 814547866277667802364003)
          ·
            refine ⟨1221821799416501703546005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814547866277667802364003 1221821799416501703546005)
            ·
              refine ⟨57272896847648517353719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1221821799416501703546005 57272896847648517353719)
              ·
                refine ⟨85909345271472776030579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57272896847648517353719 85909345271472776030579)
                ·
                  refine ⟨128864017907209164045869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85909345271472776030579 128864017907209164045869)
                  ·
                    refine ⟨48324006715203436517201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128864017907209164045869 48324006715203436517201)
                    ·
                      refine ⟨36243005036402577387901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48324006715203436517201 36243005036402577387901)
                      ·
                        rfl

theorem cell23_70583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 3, 2].length) (baseStart_70583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70583 prefixEnd_70583 := by exact prefixLift 70583
  have htrace : WordTrace (prefixWord ++ tailWord_70583) baseStart_70583 baseEnd_70583 := by
    simpa [prefixWord, tailWord_70583, baseEnd_70583] using wordTrace_append hprefix tailTrace_70583
  have hstable : (prefixWord ++ tailWord_70583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70583).length < 2 ^ (prefixWord ++ tailWord_70583).sum := by decide
  have hdescent : baseEnd_70583 < baseStart_70583 := by decide
  rcases family_descends (prefixWord ++ tailWord_70583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70649 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 2, 5]
def baseStart_70649 : Nat := 118140960795 + 70649 * 2 ^ 59
def prefixEnd_70649 : Nat := 4983230072969 + 3 ^ 40 * 70649 * 2
def baseEnd_70649 : Nat := 12092298253199773054199

theorem tailTrace_70649 : CollatzResearch.WordTrace tailWord_70649 prefixEnd_70649 12092298253199773054199 := by
  unfold tailWord_70649
  simp only [CollatzResearch.WordTrace]
  refine ⟨2576780721058213733695001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1717853814038809155796667 2576780721058213733695001)
  ·
    refine ⟨1932585540793660300271251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2576780721058213733695001 1932585540793660300271251)
    ·
      refine ⟨2898878311190490450406877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1932585540793660300271251 2898878311190490450406877)
      ·
        refine ⟨1087079366696433918902579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2898878311190490450406877 1087079366696433918902579)
        ·
          refine ⟨1630619050044650878353869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087079366696433918902579 1630619050044650878353869)
          ·
            refine ⟨611482143766744079382701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1630619050044650878353869 611482143766744079382701)
            ·
              refine ⟨229305803912529029768513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 611482143766744079382701 229305803912529029768513)
              ·
                refine ⟨171979352934396772326385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229305803912529029768513 171979352934396772326385)
                ·
                  refine ⟨128984514700797579244789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171979352934396772326385 128984514700797579244789)
                  ·
                    refine ⟨12092298253199773054199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 128984514700797579244789 12092298253199773054199)
                    ·
                      rfl

theorem cell23_70649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_70649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70649 prefixEnd_70649 := by exact prefixLift 70649
  have htrace : WordTrace (prefixWord ++ tailWord_70649) baseStart_70649 baseEnd_70649 := by
    simpa [prefixWord, tailWord_70649, baseEnd_70649] using wordTrace_append hprefix tailTrace_70649
  have hstable : (prefixWord ++ tailWord_70649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70649).length < 2 ^ (prefixWord ++ tailWord_70649).sum := by decide
  have hdescent : baseEnd_70649 < baseStart_70649 := by decide
  rcases family_descends (prefixWord ++ tailWord_70649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70706 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_70706 : Nat := 118140960795 + 70706 * 2 ^ 59
def prefixEnd_70706 : Nat := 4983230072969 + 3 ^ 40 * 70706 * 2
def baseEnd_70706 : Nat := 36306163156905596149835

theorem tailTrace_70706 : CollatzResearch.WordTrace tailWord_70706 prefixEnd_70706 36306163156905596149835 := by
  unfold tailWord_70706
  simp only [CollatzResearch.WordTrace]
  refine ⟨644714920462928117129993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1719239787901141645679981 644714920462928117129993)
  ·
    refine ⟨483536190347196087847495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 644714920462928117129993 483536190347196087847495)
    ·
      refine ⟨725304285520794131771243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483536190347196087847495 725304285520794131771243)
      ·
        refine ⟨1087956428281191197656865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725304285520794131771243 1087956428281191197656865)
        ·
          refine ⟨815967321210893398242649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087956428281191197656865 815967321210893398242649)
          ·
            refine ⟨611975490908170048681987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 815967321210893398242649 611975490908170048681987)
            ·
              refine ⟨917963236362255073022981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611975490908170048681987 917963236362255073022981)
              ·
                refine ⟨172118106817922826191809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 917963236362255073022981 172118106817922826191809)
                ·
                  refine ⟨129088580113442119643857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172118106817922826191809 129088580113442119643857)
                  ·
                    refine ⟨96816435085081589732893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129088580113442119643857 96816435085081589732893)
                    ·
                      refine ⟨36306163156905596149835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 96816435085081589732893 36306163156905596149835)
                      ·
                        rfl

theorem cell23_70706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_70706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70706 prefixEnd_70706 := by exact prefixLift 70706
  have htrace : WordTrace (prefixWord ++ tailWord_70706) baseStart_70706 baseEnd_70706 := by
    simpa [prefixWord, tailWord_70706, baseEnd_70706] using wordTrace_append hprefix tailTrace_70706
  have hstable : (prefixWord ++ tailWord_70706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70706).length < 2 ^ (prefixWord ++ tailWord_70706).sum := by decide
  have hdescent : baseEnd_70706 < baseStart_70706 := by decide
  rcases family_descends (prefixWord ++ tailWord_70706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70719 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 3]
def baseStart_70719 : Nat := 118140960795 + 70719 * 2 ^ 59
def prefixEnd_70719 : Nat := 4983230072969 + 3 ^ 40 * 70719 * 2
def baseEnd_70719 : Nat := 36312838405414045287275

theorem tailTrace_70719 : CollatzResearch.WordTrace tailWord_70719 prefixEnd_70719 36312838405414045287275 := by
  unfold tailWord_70719
  simp only [CollatzResearch.WordTrace]
  refine ⟨2579333830804615688743211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1719555887203077125828807 2579333830804615688743211)
  ·
    refine ⟨3869000746206923533114817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2579333830804615688743211 3869000746206923533114817)
    ·
      refine ⟨2901750559655192649836113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3869000746206923533114817 2901750559655192649836113)
      ·
        refine ⟨2176312919741394487377085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2901750559655192649836113 2176312919741394487377085)
        ·
          refine ⟨816117344903022932766407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2176312919741394487377085 816117344903022932766407)
          ·
            refine ⟨1224176017354534399149611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816117344903022932766407 1224176017354534399149611)
            ·
              refine ⟨1836264026031801598724417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224176017354534399149611 1836264026031801598724417)
              ·
                refine ⟨1377198019523851199043313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836264026031801598724417 1377198019523851199043313)
                ·
                  refine ⟨1032898514642888399282485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1377198019523851199043313 1032898514642888399282485)
                  ·
                    refine ⟨96834235747770787432733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1032898514642888399282485 96834235747770787432733)
                    ·
                      refine ⟨36312838405414045287275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 96834235747770787432733 36312838405414045287275)
                      ·
                        rfl

theorem cell23_70719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_70719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70719 prefixEnd_70719 := by exact prefixLift 70719
  have htrace : WordTrace (prefixWord ++ tailWord_70719) baseStart_70719 baseEnd_70719 := by
    simpa [prefixWord, tailWord_70719, baseEnd_70719] using wordTrace_append hprefix tailTrace_70719
  have hstable : (prefixWord ++ tailWord_70719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70719).length < 2 ^ (prefixWord ++ tailWord_70719).sum := by decide
  have hdescent : baseEnd_70719 < baseStart_70719 := by decide
  rcases family_descends (prefixWord ++ tailWord_70719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70760 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 6]
def baseStart_70760 : Nat := 118140960795 + 70760 * 2 ^ 59
def prefixEnd_70760 : Nat := 4983230072969 + 3 ^ 40 * 70760 * 2
def baseEnd_70760 : Nat := 4037099012472042763843

theorem tailTrace_70760 : CollatzResearch.WordTrace tailWord_70760 prefixEnd_70760 4037099012472042763843 := by
  unfold tailWord_70760
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290414611828039845492867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1720552815770719793990489 1290414611828039845492867)
  ·
    refine ⟨1935621917742059768239301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290414611828039845492867 1935621917742059768239301)
    ·
      refine ⟨362929109576636206544869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1935621917742059768239301 362929109576636206544869)
      ·
        refine ⟨68049208045619288727163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 362929109576636206544869 68049208045619288727163)
        ·
          refine ⟨102073812068428933090745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68049208045619288727163 102073812068428933090745)
          ·
            refine ⟨76555359051321699818059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102073812068428933090745 76555359051321699818059)
            ·
              refine ⟨114833038576982549727089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76555359051321699818059 114833038576982549727089)
              ·
                refine ⟨86124778932736912295317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114833038576982549727089 86124778932736912295317)
                ·
                  refine ⟨4037099012472042763843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86124778932736912295317 4037099012472042763843)
                  ·
                    rfl

theorem cell23_70760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 6].length) (baseStart_70760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70760 prefixEnd_70760 := by exact prefixLift 70760
  have htrace : WordTrace (prefixWord ++ tailWord_70760) baseStart_70760 baseEnd_70760 := by
    simpa [prefixWord, tailWord_70760, baseEnd_70760] using wordTrace_append hprefix tailTrace_70760
  have hstable : (prefixWord ++ tailWord_70760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70760).length < 2 ^ (prefixWord ++ tailWord_70760).sum := by decide
  have hdescent : baseEnd_70760 < baseStart_70760 := by decide
  rcases family_descends (prefixWord ++ tailWord_70760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70770 : List Nat := [3, 2, 1, 2, 2, 1, 1, 6, 1, 1, 3]
def baseStart_70770 : Nat := 118140960795 + 70770 * 2 ^ 59
def prefixEnd_70770 : Nat := 4983230072969 + 3 ^ 40 * 70770 * 2
def baseEnd_70770 : Nat := 36339025918793345749541

theorem tailTrace_70770 : CollatzResearch.WordTrace tailWord_70770 prefixEnd_70770 36339025918793345749541 := by
  unfold tailWord_70770
  simp only [CollatzResearch.WordTrace]
  refine ⟨645298488404962849712441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1720795969079900932566509 645298488404962849712441)
  ·
    refine ⟨483973866303722137284331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 645298488404962849712441 483973866303722137284331)
    ·
      refine ⟨725960799455583205926497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483973866303722137284331 725960799455583205926497)
      ·
        refine ⟨544470599591687404444873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 725960799455583205926497 544470599591687404444873)
        ·
          refine ⟨408352949693765553333655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544470599591687404444873 408352949693765553333655)
          ·
            refine ⟨612529424540648330000483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408352949693765553333655 612529424540648330000483)
            ·
              refine ⟨918794136810972495000725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612529424540648330000483 918794136810972495000725)
              ·
                refine ⟨43068475163014335703159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 918794136810972495000725 43068475163014335703159)
                ·
                  refine ⟨64602712744521503554739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43068475163014335703159 64602712744521503554739)
                  ·
                    refine ⟨96904069116782255332109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64602712744521503554739 96904069116782255332109)
                    ·
                      refine ⟨36339025918793345749541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 96904069116782255332109 36339025918793345749541)
                      ·
                        rfl

theorem cell23_70770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_70770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70770 prefixEnd_70770 := by exact prefixLift 70770
  have htrace : WordTrace (prefixWord ++ tailWord_70770) baseStart_70770 baseEnd_70770 := by
    simpa [prefixWord, tailWord_70770, baseEnd_70770] using wordTrace_append hprefix tailTrace_70770
  have hstable : (prefixWord ++ tailWord_70770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70770).length < 2 ^ (prefixWord ++ tailWord_70770).sum := by decide
  have hdescent : baseEnd_70770 < baseStart_70770 := by decide
  rcases family_descends (prefixWord ++ tailWord_70770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70793 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 4]
def baseStart_70793 : Nat := 118140960795 + 70793 * 2 ^ 59
def prefixEnd_70793 : Nat := 4983230072969 + 3 ^ 40 * 70793 * 2
def baseEnd_70793 : Nat := 36350835973846755761935

theorem tailTrace_70793 : CollatzResearch.WordTrace tailWord_70793 prefixEnd_70793 36350835973846755761935 := by
  unfold tailWord_70793
  simp only [CollatzResearch.WordTrace]
  refine ⟨2582032832536526326937033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1721355221691017551291355 2582032832536526326937033)
  ·
    refine ⟨1936524624402394745202775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2582032832536526326937033 1936524624402394745202775)
    ·
      refine ⟨2904786936603592117804163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936524624402394745202775 2904786936603592117804163)
      ·
        refine ⟨4357180404905388176706245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2904786936603592117804163 4357180404905388176706245)
        ·
          refine ⟨816971325919760283132421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4357180404905388176706245 816971325919760283132421)
          ·
            refine ⟨153182123609955053087329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 816971325919760283132421 153182123609955053087329)
            ·
              refine ⟨114886592707466289815497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153182123609955053087329 114886592707466289815497)
              ·
                refine ⟨86164944530599717361623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114886592707466289815497 86164944530599717361623)
                ·
                  refine ⟨129247416795899576042435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86164944530599717361623 129247416795899576042435)
                  ·
                    refine ⟨193871125193849364063653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129247416795899576042435 193871125193849364063653)
                    ·
                      refine ⟨36350835973846755761935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 193871125193849364063653 36350835973846755761935)
                      ·
                        rfl

theorem cell23_70793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 4].length) (baseStart_70793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70793 prefixEnd_70793 := by exact prefixLift 70793
  have htrace : WordTrace (prefixWord ++ tailWord_70793) baseStart_70793 baseEnd_70793 := by
    simpa [prefixWord, tailWord_70793, baseEnd_70793] using wordTrace_append hprefix tailTrace_70793
  have hstable : (prefixWord ++ tailWord_70793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70793).length < 2 ^ (prefixWord ++ tailWord_70793).sum := by decide
  have hdescent : baseEnd_70793 < baseStart_70793 := by decide
  rcases family_descends (prefixWord ++ tailWord_70793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70796 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 3, 2, 3]
def baseStart_70796 : Nat := 118140960795 + 70796 * 2 ^ 59
def prefixEnd_70796 : Nat := 4983230072969 + 3 ^ 40 * 70796 * 2
def baseEnd_70796 : Nat := 36352376415810244024421

theorem tailTrace_70796 : CollatzResearch.WordTrace tailWord_70796 prefixEnd_70796 36352376415810244024421 := by
  unfold tailWord_70796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1291071125762828919648121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1721428167683771892864161 1291071125762828919648121)
  ·
    refine ⟨968303344322121689736091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1291071125762828919648121 968303344322121689736091)
    ·
      refine ⟨1452455016483182534604137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 968303344322121689736091 1452455016483182534604137)
      ·
        refine ⟨1089341262362386900953103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1452455016483182534604137 1089341262362386900953103)
        ·
          refine ⟨1634011893543580351429655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089341262362386900953103 1634011893543580351429655)
          ·
            refine ⟨2451017840315370527144483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634011893543580351429655 2451017840315370527144483)
            ·
              refine ⟨3676526760473055790716725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451017840315370527144483 3676526760473055790716725)
              ·
                refine ⟨344674383794348980379693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3676526760473055790716725 344674383794348980379693)
                ·
                  refine ⟨129252893922880867642385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344674383794348980379693 129252893922880867642385)
                  ·
                    refine ⟨96939670442160650731789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129252893922880867642385 96939670442160650731789)
                    ·
                      refine ⟨36352376415810244024421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 96939670442160650731789 36352376415810244024421)
                      ·
                        rfl

theorem cell23_70796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_70796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70796 prefixEnd_70796 := by exact prefixLift 70796
  have htrace : WordTrace (prefixWord ++ tailWord_70796) baseStart_70796 baseEnd_70796 := by
    simpa [prefixWord, tailWord_70796, baseEnd_70796] using wordTrace_append hprefix tailTrace_70796
  have hstable : (prefixWord ++ tailWord_70796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70796).length < 2 ^ (prefixWord ++ tailWord_70796).sum := by decide
  have hdescent : baseEnd_70796 < baseStart_70796 := by decide
  rcases family_descends (prefixWord ++ tailWord_70796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70813 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_70813 : Nat := 118140960795 + 70813 * 2 ^ 59
def prefixEnd_70813 : Nat := 4983230072969 + 3 ^ 40 * 70813 * 2
def baseEnd_70813 : Nat := 36361105586936677511843

theorem tailTrace_70813 : CollatzResearch.WordTrace tailWord_70813 prefixEnd_70813 36361105586936677511843 := by
  unfold tailWord_70813
  simp only [CollatzResearch.WordTrace]
  refine ⟨2582762292464069742665093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1721841528309379828443395 2582762292464069742665093)
  ·
    refine ⟨484267929837013076749705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2582762292464069742665093 484267929837013076749705)
    ·
      refine ⟨363200947377759807562279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 484267929837013076749705 363200947377759807562279)
      ·
        refine ⟨544801421066639711343419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363200947377759807562279 544801421066639711343419)
        ·
          refine ⟨817202131599959567015129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544801421066639711343419 817202131599959567015129)
          ·
            refine ⟨612901598699969675261347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817202131599959567015129 612901598699969675261347)
            ·
              refine ⟨919352398049954512892021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612901598699969675261347 919352398049954512892021)
              ·
                refine ⟨86189287317183235583627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 919352398049954512892021 86189287317183235583627)
                ·
                  refine ⟨129283930975774853375441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86189287317183235583627 129283930975774853375441)
                  ·
                    refine ⟨96962948231831140031581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129283930975774853375441 96962948231831140031581)
                    ·
                      refine ⟨36361105586936677511843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 96962948231831140031581 36361105586936677511843)
                      ·
                        rfl

theorem cell23_70813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_70813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70813 prefixEnd_70813 := by exact prefixLift 70813
  have htrace : WordTrace (prefixWord ++ tailWord_70813) baseStart_70813 baseEnd_70813 := by
    simpa [prefixWord, tailWord_70813, baseEnd_70813] using wordTrace_append hprefix tailTrace_70813
  have hstable : (prefixWord ++ tailWord_70813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70813).length < 2 ^ (prefixWord ++ tailWord_70813).sum := by decide
  have hdescent : baseEnd_70813 < baseStart_70813 := by decide
  rcases family_descends (prefixWord ++ tailWord_70813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70859 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 3, 8]
def baseStart_70859 : Nat := 118140960795 + 70859 * 2 ^ 59
def prefixEnd_70859 : Nat := 4983230072969 + 3 ^ 40 * 70859 * 2
def baseEnd_70859 : Nat := 12128241899014499178877

theorem tailTrace_70859 : CollatzResearch.WordTrace tailWord_70859 prefixEnd_70859 12128241899014499178877 := by
  unfold tailWord_70859
  simp only [CollatzResearch.WordTrace]
  refine ⟨2584440050297419598839631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1722960033531613065893087 2584440050297419598839631)
  ·
    refine ⟨3876660075446129398259447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2584440050297419598839631 3876660075446129398259447)
    ·
      refine ⟨5814990113169194097389171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3876660075446129398259447 5814990113169194097389171)
      ·
        refine ⟨8722485169753791146083757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5814990113169194097389171 8722485169753791146083757)
        ·
          refine ⟨3270931938657671679781409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8722485169753791146083757 3270931938657671679781409)
          ·
            refine ⟨2453198953993253759836057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270931938657671679781409 2453198953993253759836057)
            ·
              refine ⟨1839899215494940319877043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2453198953993253759836057 1839899215494940319877043)
              ·
                refine ⟨2759848823242410479815565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839899215494940319877043 2759848823242410479815565)
                ·
                  refine ⟨1034943308715903929930837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2759848823242410479815565 1034943308715903929930837)
                  ·
                    refine ⟨12128241899014499178877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1034943308715903929930837 12128241899014499178877)
                    ·
                      rfl

theorem cell23_70859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 8].length) (baseStart_70859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70859 prefixEnd_70859 := by exact prefixLift 70859
  have htrace : WordTrace (prefixWord ++ tailWord_70859) baseStart_70859 baseEnd_70859 := by
    simpa [prefixWord, tailWord_70859, baseEnd_70859] using wordTrace_append hprefix tailTrace_70859
  have hstable : (prefixWord ++ tailWord_70859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70859).length < 2 ^ (prefixWord ++ tailWord_70859).sum := by decide
  have hdescent : baseEnd_70859 < baseStart_70859 := by decide
  rcases family_descends (prefixWord ++ tailWord_70859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70893 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_70893 : Nat := 118140960795 + 70893 * 2 ^ 59
def prefixEnd_70893 : Nat := 4983230072969 + 3 ^ 40 * 70893 * 2
def baseEnd_70893 : Nat := 12134061346432121503825

theorem tailTrace_70893 : CollatzResearch.WordTrace tailWord_70893 prefixEnd_70893 12134061346432121503825 := by
  unfold tailWord_70893
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585680132174243405577333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1723786754782828937051555 2585680132174243405577333)
  ·
    refine ⟨242407512391335319272875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2585680132174243405577333 242407512391335319272875)
    ·
      refine ⟨363611268587002978909313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242407512391335319272875 363611268587002978909313)
      ·
        refine ⟨272708451440252234181985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 363611268587002978909313 272708451440252234181985)
        ·
          refine ⟨204531338580189175636489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272708451440252234181985 204531338580189175636489)
          ·
            refine ⟨153398503935141881727367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204531338580189175636489 153398503935141881727367)
            ·
              refine ⟨230097755902712822591051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153398503935141881727367 230097755902712822591051)
              ·
                refine ⟨345146633854069233886577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230097755902712822591051 345146633854069233886577)
                ·
                  refine ⟨258859975390551925414933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 345146633854069233886577 258859975390551925414933)
                  ·
                    refine ⟨12134061346432121503825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 258859975390551925414933 12134061346432121503825)
                    ·
                      rfl

theorem cell23_70893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_70893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70893 prefixEnd_70893 := by exact prefixLift 70893
  have htrace : WordTrace (prefixWord ++ tailWord_70893) baseStart_70893 baseEnd_70893 := by
    simpa [prefixWord, tailWord_70893, baseEnd_70893] using wordTrace_append hprefix tailTrace_70893
  have hstable : (prefixWord ++ tailWord_70893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70893).length < 2 ^ (prefixWord ++ tailWord_70893).sum := by decide
  have hdescent : baseEnd_70893 < baseStart_70893 := by decide
  rcases family_descends (prefixWord ++ tailWord_70893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70906 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 7]
def baseStart_70906 : Nat := 118140960795 + 70906 * 2 ^ 59
def prefixEnd_70906 : Nat := 4983230072969 + 3 ^ 40 * 70906 * 2
def baseEnd_70906 : Nat := 4045428809756090405435

theorem tailTrace_70906 : CollatzResearch.WordTrace tailWord_70906 prefixEnd_70906 4045428809756090405435 := by
  unfold tailWord_70906
  simp only [CollatzResearch.WordTrace]
  refine ⟨646538570281786656450143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1724102854084764417200381 646538570281786656450143)
  ·
    refine ⟨969807855422679984675215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 646538570281786656450143 969807855422679984675215)
    ·
      refine ⟨1454711783134019977012823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 969807855422679984675215 1454711783134019977012823)
      ·
        refine ⟨2182067674701029965519235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454711783134019977012823 2182067674701029965519235)
        ·
          refine ⟨3273101512051544948278853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2182067674701029965519235 3273101512051544948278853)
          ·
            refine ⟨613706533509664677802285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3273101512051544948278853 613706533509664677802285)
            ·
              refine ⟨230139950066124254175857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 613706533509664677802285 230139950066124254175857)
              ·
                refine ⟨172604962549593190631893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230139950066124254175857 172604962549593190631893)
                ·
                  refine ⟨4045428809756090405435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 172604962549593190631893 4045428809756090405435)
                  ·
                    rfl

theorem cell23_70906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_70906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70906 prefixEnd_70906 := by exact prefixLift 70906
  have htrace : WordTrace (prefixWord ++ tailWord_70906) baseStart_70906 baseEnd_70906 := by
    simpa [prefixWord, tailWord_70906, baseEnd_70906] using wordTrace_append hprefix tailTrace_70906
  have hstable : (prefixWord ++ tailWord_70906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70906).length < 2 ^ (prefixWord ++ tailWord_70906).sum := by decide
  have hdescent : baseEnd_70906 < baseStart_70906 := by decide
  rcases family_descends (prefixWord ++ tailWord_70906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70923 : List Nat := [1, 1, 1, 1, 5, 3, 1, 5, 5]
def baseStart_70923 : Nat := 118140960795 + 70923 * 2 ^ 59
def prefixEnd_70923 : Nat := 4983230072969 + 3 ^ 40 * 70923 * 2
def baseEnd_70923 : Nat := 4046398717659027459593

theorem tailTrace_70923 : CollatzResearch.WordTrace tailWord_70923 prefixEnd_70923 4046398717659027459593 := by
  unfold tailWord_70923
  simp only [CollatzResearch.WordTrace]
  refine ⟨2586774322065558529169423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1724516214710372352779615 2586774322065558529169423)
  ·
    refine ⟨3880161483098337793754135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2586774322065558529169423 3880161483098337793754135)
    ·
      refine ⟨5820242224647506690631203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3880161483098337793754135 5820242224647506690631203)
      ·
        refine ⟨8730363336971260035946805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5820242224647506690631203 8730363336971260035946805)
        ·
          refine ⟨818471562841055628370013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8730363336971260035946805 818471562841055628370013)
          ·
            refine ⟨306926836065395860638755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 818471562841055628370013 306926836065395860638755)
            ·
              refine ⟨460390254098093790958133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306926836065395860638755 460390254098093790958133)
              ·
                refine ⟨43161586321696292902325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 460390254098093790958133 43161586321696292902325)
                ·
                  refine ⟨4046398717659027459593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43161586321696292902325 4046398717659027459593)
                  ·
                    rfl

theorem cell23_70923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 5].length) (baseStart_70923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70923 prefixEnd_70923 := by exact prefixLift 70923
  have htrace : WordTrace (prefixWord ++ tailWord_70923) baseStart_70923 baseEnd_70923 := by
    simpa [prefixWord, tailWord_70923, baseEnd_70923] using wordTrace_append hprefix tailTrace_70923
  have hstable : (prefixWord ++ tailWord_70923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70923).length < 2 ^ (prefixWord ++ tailWord_70923).sum := by decide
  have hdescent : baseEnd_70923 < baseStart_70923 := by decide
  rcases family_descends (prefixWord ++ tailWord_70923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70986 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_70986 : Nat := 118140960795 + 70986 * 2 ^ 59
def prefixEnd_70986 : Nat := 4983230072969 + 3 ^ 40 * 70986 * 2
def baseEnd_70986 : Nat := 36449937740164500648547

theorem tailTrace_70986 : CollatzResearch.WordTrace tailWord_70986 prefixEnd_70986 36449937740164500648547 := by
  unfold tailWord_70986
  simp only [CollatzResearch.WordTrace]
  refine ⟨647268030209330072178203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1726048080558213525808541 647268030209330072178203)
  ·
    refine ⟨970902045313995108267305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 647268030209330072178203 970902045313995108267305)
    ·
      refine ⟨728176533985496331200479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 970902045313995108267305 728176533985496331200479)
      ·
        refine ⟨1092264800978244496800719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728176533985496331200479 1092264800978244496800719)
        ·
          refine ⟨1638397201467366745201079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092264800978244496800719 1638397201467366745201079)
          ·
            refine ⟨2457595802201050117801619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638397201467366745201079 2457595802201050117801619)
            ·
              refine ⟨3686393703301575176702429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2457595802201050117801619 3686393703301575176702429)
              ·
                refine ⟨1382397638738090691263411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3686393703301575176702429 1382397638738090691263411)
                ·
                  refine ⟨2073596458107136036895117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382397638738090691263411 2073596458107136036895117)
                  ·
                    refine ⟨777598671790176013835669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2073596458107136036895117 777598671790176013835669)
                    ·
                      refine ⟨36449937740164500648547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 777598671790176013835669 36449937740164500648547)
                      ·
                        rfl

theorem cell23_70986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_70986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70986 prefixEnd_70986 := by exact prefixLift 70986
  have htrace : WordTrace (prefixWord ++ tailWord_70986) baseStart_70986 baseEnd_70986 := by
    simpa [prefixWord, tailWord_70986, baseEnd_70986] using wordTrace_append hprefix tailTrace_70986
  have hstable : (prefixWord ++ tailWord_70986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70986).length < 2 ^ (prefixWord ++ tailWord_70986).sum := by decide
  have hdescent : baseEnd_70986 < baseStart_70986 := by decide
  rcases family_descends (prefixWord ++ tailWord_70986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71010 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_71010 : Nat := 118140960795 + 71010 * 2 ^ 59
def prefixEnd_71010 : Nat := 4983230072969 + 3 ^ 40 * 71010 * 2
def baseEnd_71010 : Nat := 36462261275872406748437

theorem tailTrace_71010 : CollatzResearch.WordTrace tailWord_71010 prefixEnd_71010 36462261275872406748437 := by
  unfold tailWord_71010
  simp only [CollatzResearch.WordTrace]
  refine ⟨647486868187593096896621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1726631648500248258390989 647486868187593096896621)
  ·
    refine ⟨242807575570347411336233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 647486868187593096896621 242807575570347411336233)
    ·
      refine ⟨182105681677760558502175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242807575570347411336233 182105681677760558502175)
      ·
        refine ⟨273158522516640837753263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182105681677760558502175 273158522516640837753263)
        ·
          refine ⟨409737783774961256629895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273158522516640837753263 409737783774961256629895)
          ·
            refine ⟨614606675662441884944843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409737783774961256629895 614606675662441884944843)
            ·
              refine ⟨921910013493662827417265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614606675662441884944843 921910013493662827417265)
              ·
                refine ⟨691432510120247120562949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921910013493662827417265 691432510120247120562949)
                ·
                  refine ⟨129643595647546335105553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 691432510120247120562949 129643595647546335105553)
                  ·
                    refine ⟨97232696735659751329165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129643595647546335105553 97232696735659751329165)
                    ·
                      refine ⟨36462261275872406748437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 97232696735659751329165 36462261275872406748437)
                      ·
                        rfl

theorem cell23_71010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_71010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71010 prefixEnd_71010 := by exact prefixLift 71010
  have htrace : WordTrace (prefixWord ++ tailWord_71010) baseStart_71010 baseEnd_71010 := by
    simpa [prefixWord, tailWord_71010, baseEnd_71010] using wordTrace_append hprefix tailTrace_71010
  have hstable : (prefixWord ++ tailWord_71010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71010).length < 2 ^ (prefixWord ++ tailWord_71010).sum := by decide
  have hdescent : baseEnd_71010 < baseStart_71010 := by decide
  rcases family_descends (prefixWord ++ tailWord_71010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71013 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 6]
def baseStart_71013 : Nat := 118140960795 + 71013 * 2 ^ 59
def prefixEnd_71013 : Nat := 4983230072969 + 3 ^ 40 * 71013 * 2
def baseEnd_71013 : Nat := 4051533524203988334547

theorem tailTrace_71013 : CollatzResearch.WordTrace tailWord_71013 prefixEnd_71013 4051533524203988334547 := by
  unfold tailWord_71013
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590056891739503899945693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1726704594493002599963795 2590056891739503899945693)
  ·
    refine ⟨971271334402313962479635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2590056891739503899945693 971271334402313962479635)
    ·
      refine ⟨1456907001603470943719453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 971271334402313962479635 1456907001603470943719453)
      ·
        refine ⟨546340125601301603894795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1456907001603470943719453 546340125601301603894795)
        ·
          refine ⟨819510188401952405842193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546340125601301603894795 819510188401952405842193)
          ·
            refine ⟨614632641301464304381645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 819510188401952405842193 614632641301464304381645)
            ·
              refine ⟨230487240488049114143117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 614632641301464304381645 230487240488049114143117)
              ·
                refine ⟨86432715183018417803669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230487240488049114143117 86432715183018417803669)
                ·
                  refine ⟨4051533524203988334547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86432715183018417803669 4051533524203988334547)
                  ·
                    rfl

theorem cell23_71013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_71013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71013 prefixEnd_71013 := by exact prefixLift 71013
  have htrace : WordTrace (prefixWord ++ tailWord_71013) baseStart_71013 baseEnd_71013 := by
    simpa [prefixWord, tailWord_71013, baseEnd_71013] using wordTrace_append hprefix tailTrace_71013
  have hstable : (prefixWord ++ tailWord_71013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71013).length < 2 ^ (prefixWord ++ tailWord_71013).sum := by decide
  have hdescent : baseEnd_71013 < baseStart_71013 := by decide
  rcases family_descends (prefixWord ++ tailWord_71013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71056 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 1, 12]
def baseStart_71056 : Nat := 118140960795 + 71056 * 2 ^ 59
def prefixEnd_71056 : Nat := 4983230072969 + 3 ^ 40 * 71056 * 2
def baseEnd_71056 : Nat := 12161960461993075591075

theorem tailTrace_71056 : CollatzResearch.WordTrace tailWord_71056 prefixEnd_71056 12161960461993075591075 := by
  unfold tailWord_71056
  simp only [CollatzResearch.WordTrace]
  refine ⟨1295812615291861121880511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1727750153722481495840681 1295812615291861121880511)
  ·
    refine ⟨1943718922937791682820767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1295812615291861121880511 1943718922937791682820767)
    ·
      refine ⟨2915578384406687524231151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943718922937791682820767 2915578384406687524231151)
      ·
        refine ⟨4373367576610031286346727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2915578384406687524231151 4373367576610031286346727)
        ·
          refine ⟨6560051364915046929520091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373367576610031286346727 6560051364915046929520091)
          ·
            refine ⟨9840077047372570394280137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560051364915046929520091 9840077047372570394280137)
            ·
              refine ⟨7380057785529427795710103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9840077047372570394280137 7380057785529427795710103)
              ·
                refine ⟨11070086678294141693565155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7380057785529427795710103 11070086678294141693565155)
                ·
                  refine ⟨16605130017441212540347733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11070086678294141693565155 16605130017441212540347733)
                  ·
                    refine ⟨12161960461993075591075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 16605130017441212540347733 12161960461993075591075)
                    ·
                      rfl

theorem cell23_71056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_71056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71056 prefixEnd_71056 := by exact prefixLift 71056
  have htrace : WordTrace (prefixWord ++ tailWord_71056) baseStart_71056 baseEnd_71056 := by
    simpa [prefixWord, tailWord_71056, baseEnd_71056] using wordTrace_append hprefix tailTrace_71056
  have hstable : (prefixWord ++ tailWord_71056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71056).length < 2 ^ (prefixWord ++ tailWord_71056).sum := by decide
  have hdescent : baseEnd_71056 < baseStart_71056 := by decide
  rcases family_descends (prefixWord ++ tailWord_71056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71057 : List Nat := [1, 2, 2, 1, 1, 1, 2, 8, 1, 1, 3]
def baseStart_71057 : Nat := 118140960795 + 71057 * 2 ^ 59
def prefixEnd_71057 : Nat := 4983230072969 + 3 ^ 40 * 71057 * 2
def baseEnd_71057 : Nat := 36486394866633722860721

theorem tailTrace_71057 : CollatzResearch.WordTrace tailWord_71057 prefixEnd_71057 36486394866633722860721 := by
  unfold tailWord_71057
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591661703580099414547425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1727774469053399609698283 2591661703580099414547425)
  ·
    refine ⟨1943746277685074560910569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2591661703580099414547425 1943746277685074560910569)
    ·
      refine ⟨1457809708263805920682927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1943746277685074560910569 1457809708263805920682927)
      ·
        refine ⟨2186714562395708881024391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457809708263805920682927 2186714562395708881024391)
        ·
          refine ⟨3280071843593563321536587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186714562395708881024391 3280071843593563321536587)
          ·
            refine ⟨4920107765390344982304881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3280071843593563321536587 4920107765390344982304881)
            ·
              refine ⟨3690080824042758736728661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4920107765390344982304881 3690080824042758736728661)
              ·
                refine ⟨43243134656751078946039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3690080824042758736728661 43243134656751078946039)
                ·
                  refine ⟨64864701985126618419059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43243134656751078946039 64864701985126618419059)
                  ·
                    refine ⟨97297052977689927628589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64864701985126618419059 97297052977689927628589)
                    ·
                      refine ⟨36486394866633722860721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 97297052977689927628589 36486394866633722860721)
                      ·
                        rfl

theorem cell23_71057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 1, 1, 3].length) (baseStart_71057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71057 prefixEnd_71057 := by exact prefixLift 71057
  have htrace : WordTrace (prefixWord ++ tailWord_71057) baseStart_71057 baseEnd_71057 := by
    simpa [prefixWord, tailWord_71057, baseEnd_71057] using wordTrace_append hprefix tailTrace_71057
  have hstable : (prefixWord ++ tailWord_71057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71057).length < 2 ^ (prefixWord ++ tailWord_71057).sum := by decide
  have hdescent : baseEnd_71057 < baseStart_71057 := by decide
  rcases family_descends (prefixWord ++ tailWord_71057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71060 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_71060 : Nat := 118140960795 + 71060 * 2 ^ 59
def prefixEnd_71060 : Nat := 4983230072969 + 3 ^ 40 * 71060 * 2
def baseEnd_71060 : Nat := 12162645102865737041069

theorem tailTrace_71060 : CollatzResearch.WordTrace tailWord_71060 prefixEnd_71060 12162645102865737041069 := by
  unfold tailWord_71060
  simp only [CollatzResearch.WordTrace]
  refine ⟨1295885561284615463453317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1727847415046153951271089 1295885561284615463453317)
  ·
    refine ⟨242978542740865399397497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1295885561284615463453317 242978542740865399397497)
    ·
      refine ⟨182233907055649049548123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242978542740865399397497 182233907055649049548123)
      ·
        refine ⟨273350860583473574322185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182233907055649049548123 273350860583473574322185)
        ·
          refine ⟨205013145437605180741639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273350860583473574322185 205013145437605180741639)
          ·
            refine ⟨307519718156407771112459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205013145437605180741639 307519718156407771112459)
            ·
              refine ⟨461279577234611656668689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307519718156407771112459 461279577234611656668689)
              ·
                refine ⟨345959682925958742501517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461279577234611656668689 345959682925958742501517)
                ·
                  refine ⟨129734881097234528438069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345959682925958742501517 129734881097234528438069)
                  ·
                    refine ⟨12162645102865737041069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 129734881097234528438069 12162645102865737041069)
                    ·
                      rfl

theorem cell23_71060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_71060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71060 prefixEnd_71060 := by exact prefixLift 71060
  have htrace : WordTrace (prefixWord ++ tailWord_71060) baseStart_71060 baseEnd_71060 := by
    simpa [prefixWord, tailWord_71060, baseEnd_71060] using wordTrace_append hprefix tailTrace_71060
  have hstable : (prefixWord ++ tailWord_71060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71060).length < 2 ^ (prefixWord ++ tailWord_71060).sum := by decide
  have hdescent : baseEnd_71060 < baseStart_71060 := by decide
  rcases family_descends (prefixWord ++ tailWord_71060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71097 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 4]
def baseStart_71097 : Nat := 118140960795 + 71097 * 2 ^ 59
def prefixEnd_71097 : Nat := 4983230072969 + 3 ^ 40 * 71097 * 2
def baseEnd_71097 : Nat := 36506934092813566360537

theorem tailTrace_71097 : CollatzResearch.WordTrace tailWord_71097 prefixEnd_71097 36506934092813566360537 := by
  unfold tailWord_71097
  simp only [CollatzResearch.WordTrace]
  refine ⟨2593120623435186246003545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1728747082290124164002363 2593120623435186246003545)
  ·
    refine ⟨1944840467576389684502659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2593120623435186246003545 1944840467576389684502659)
    ·
      refine ⟨2917260701364584526753989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1944840467576389684502659 2917260701364584526753989)
      ·
        refine ⟨546986381505859598766373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2917260701364584526753989 546986381505859598766373)
        ·
          refine ⟨102559946532348674768695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 546986381505859598766373 102559946532348674768695)
          ·
            refine ⟨153839919798523012153043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102559946532348674768695 153839919798523012153043)
            ·
              refine ⟨230759879697784518229565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153839919798523012153043 230759879697784518229565)
              ·
                refine ⟨86534954886669194336087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230759879697784518229565 86534954886669194336087)
                ·
                  refine ⟨129802432330003791504131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86534954886669194336087 129802432330003791504131)
                  ·
                    refine ⟨194703648495005687256197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129802432330003791504131 194703648495005687256197)
                    ·
                      refine ⟨36506934092813566360537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 194703648495005687256197 36506934092813566360537)
                      ·
                        rfl

theorem cell23_71097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_71097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71097 prefixEnd_71097 := by exact prefixLift 71097
  have htrace : WordTrace (prefixWord ++ tailWord_71097) baseStart_71097 baseEnd_71097 := by
    simpa [prefixWord, tailWord_71097, baseEnd_71097] using wordTrace_append hprefix tailTrace_71097
  have hstable : (prefixWord ++ tailWord_71097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71097).length < 2 ^ (prefixWord ++ tailWord_71097).sum := by decide
  have hdescent : baseEnd_71097 < baseStart_71097 := by decide
  rcases family_descends (prefixWord ++ tailWord_71097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71114 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2]
def baseStart_71114 : Nat := 118140960795 + 71114 * 2 ^ 59
def prefixEnd_71114 : Nat := 4983230072969 + 3 ^ 40 * 71114 * 2
def baseEnd_71114 : Nat := 36515663263939999847959

theorem tailTrace_71114 : CollatzResearch.WordTrace tailWord_71114 prefixEnd_71114 36515663263939999847959 := by
  unfold tailWord_71114
  simp only [CollatzResearch.WordTrace]
  refine ⟨648435166093399537343099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1729160442915732099581597 648435166093399537343099)
  ·
    refine ⟨972652749140099306014649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 648435166093399537343099 972652749140099306014649)
    ·
      refine ⟨729489561855074479510987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 972652749140099306014649 729489561855074479510987)
      ·
        refine ⟨1094234342782611719266481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 729489561855074479510987 1094234342782611719266481)
        ·
          refine ⟨820675757086958789449861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1094234342782611719266481 820675757086958789449861)
          ·
            refine ⟨153876704453804773021849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 820675757086958789449861 153876704453804773021849)
            ·
              refine ⟨115407528340353579766387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153876704453804773021849 115407528340353579766387)
              ·
                refine ⟨173111292510530369649581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115407528340353579766387 173111292510530369649581)
                ·
                  refine ⟨64916734691448888618593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173111292510530369649581 64916734691448888618593)
                  ·
                    refine ⟨48687551018586666463945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64916734691448888618593 48687551018586666463945)
                    ·
                      refine ⟨36515663263939999847959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48687551018586666463945 36515663263939999847959)
                      ·
                        rfl

theorem cell23_71114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_71114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71114 prefixEnd_71114 := by exact prefixLift 71114
  have htrace : WordTrace (prefixWord ++ tailWord_71114) baseStart_71114 baseEnd_71114 := by
    simpa [prefixWord, tailWord_71114, baseEnd_71114] using wordTrace_append hprefix tailTrace_71114
  have hstable : (prefixWord ++ tailWord_71114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71114).length < 2 ^ (prefixWord ++ tailWord_71114).sum := by decide
  have hdescent : baseEnd_71114 < baseStart_71114 := by decide
  rcases family_descends (prefixWord ++ tailWord_71114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71124 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_71124 : Nat := 118140960795 + 71124 * 2 ^ 59
def prefixEnd_71124 : Nat := 4983230072969 + 3 ^ 40 * 71124 * 2
def baseEnd_71124 : Nat := 12173599356828320240971

theorem tailTrace_71124 : CollatzResearch.WordTrace tailWord_71124 prefixEnd_71124 12173599356828320240971 := by
  unfold tailWord_71124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297052697168684928618213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1729403596224913238157617 1297052697168684928618213)
  ·
    refine ⟨243197380719128424115915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1297052697168684928618213 243197380719128424115915)
    ·
      refine ⟨364796071078692636173873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243197380719128424115915 364796071078692636173873)
      ·
        refine ⟨273597053309019477130405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364796071078692636173873 273597053309019477130405)
        ·
          refine ⟨51299447495441151961951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 273597053309019477130405 51299447495441151961951)
          ·
            refine ⟨76949171243161727942927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51299447495441151961951 76949171243161727942927)
            ·
              refine ⟨115423756864742591914391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76949171243161727942927 115423756864742591914391)
              ·
                refine ⟨173135635297113887871587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115423756864742591914391 173135635297113887871587)
                ·
                  refine ⟨259703452945670831807381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173135635297113887871587 259703452945670831807381)
                  ·
                    refine ⟨12173599356828320240971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 259703452945670831807381 12173599356828320240971)
                    ·
                      rfl

theorem cell23_71124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_71124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71124 prefixEnd_71124 := by exact prefixLift 71124
  have htrace : WordTrace (prefixWord ++ tailWord_71124) baseStart_71124 baseEnd_71124 := by
    simpa [prefixWord, tailWord_71124, baseEnd_71124] using wordTrace_append hprefix tailTrace_71124
  have hstable : (prefixWord ++ tailWord_71124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71124).length < 2 ^ (prefixWord ++ tailWord_71124).sum := by decide
  have hdescent : baseEnd_71124 < baseStart_71124 := by decide
  rcases family_descends (prefixWord ++ tailWord_71124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71140 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 2, 7, 2]
def baseStart_71140 : Nat := 118140960795 + 71140 * 2 ^ 59
def prefixEnd_71140 : Nat := 4983230072969 + 3 ^ 40 * 71140 * 2
def baseEnd_71140 : Nat := 36529013760956898122839

theorem tailTrace_71140 : CollatzResearch.WordTrace tailWord_71140 prefixEnd_71140 36529013760956898122839 := by
  unfold tailWord_71140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297344481139702294909437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1729792641519603059879249 1297344481139702294909437)
  ·
    refine ⟨486504180427388360591039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1297344481139702294909437 486504180427388360591039)
    ·
      refine ⟨729756270641082540886559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 486504180427388360591039 729756270641082540886559)
      ·
        refine ⟨1094634405961623811329839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 729756270641082540886559 1094634405961623811329839)
        ·
          refine ⟨1641951608942435716994759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094634405961623811329839 1641951608942435716994759)
          ·
            refine ⟨2462927413413653575492139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641951608942435716994759 2462927413413653575492139)
            ·
              refine ⟨3694391120120480363238209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462927413413653575492139 3694391120120480363238209)
              ·
                refine ⟨2770793340090360272428657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3694391120120480363238209 2770793340090360272428657)
                ·
                  refine ⟨2078095005067770204321493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2770793340090360272428657 2078095005067770204321493)
                  ·
                    refine ⟨48705351681275864163785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2078095005067770204321493 48705351681275864163785)
                    ·
                      refine ⟨36529013760956898122839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48705351681275864163785 36529013760956898122839)
                      ·
                        rfl

theorem cell23_71140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_71140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71140 prefixEnd_71140 := by exact prefixLift 71140
  have htrace : WordTrace (prefixWord ++ tailWord_71140) baseStart_71140 baseEnd_71140 := by
    simpa [prefixWord, tailWord_71140, baseEnd_71140] using wordTrace_append hprefix tailTrace_71140
  have hstable : (prefixWord ++ tailWord_71140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71140).length < 2 ^ (prefixWord ++ tailWord_71140).sum := by decide
  have hdescent : baseEnd_71140 < baseStart_71140 := by decide
  rcases family_descends (prefixWord ++ tailWord_71140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71173 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_71173 : Nat := 118140960795 + 71173 * 2 ^ 59
def prefixEnd_71173 : Nat := 4983230072969 + 3 ^ 40 * 71173 * 2
def baseEnd_71173 : Nat := 36545958622555269010187

theorem tailTrace_71173 : CollatzResearch.WordTrace tailWord_71173 prefixEnd_71173 36545958622555269010187 := by
  unfold tailWord_71173
  simp only [CollatzResearch.WordTrace]
  refine ⟨2595892571159851225770173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1730595047439900817180115 2595892571159851225770173)
  ·
    refine ⟨973459714184944209663815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2595892571159851225770173 973459714184944209663815)
    ·
      refine ⟨1460189571277416314495723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 973459714184944209663815 1460189571277416314495723)
      ·
        refine ⟨2190284356916124471743585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1460189571277416314495723 2190284356916124471743585)
        ·
          refine ⟨1642713267687093353807689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2190284356916124471743585 1642713267687093353807689)
          ·
            refine ⟨1232034950765320015355767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1642713267687093353807689 1232034950765320015355767)
            ·
              refine ⟨1848052426147980023033651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232034950765320015355767 1848052426147980023033651)
              ·
                refine ⟨2772078639221970034550477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848052426147980023033651 2772078639221970034550477)
                ·
                  refine ⟨1039529489708238762956429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2772078639221970034550477 1039529489708238762956429)
                  ·
                    refine ⟨389823558640589536108661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1039529489708238762956429 389823558640589536108661)
                    ·
                      refine ⟨36545958622555269010187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 389823558640589536108661 36545958622555269010187)
                      ·
                        rfl

theorem cell23_71173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_71173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71173 prefixEnd_71173 := by exact prefixLift 71173
  have htrace : WordTrace (prefixWord ++ tailWord_71173) baseStart_71173 baseEnd_71173 := by
    simpa [prefixWord, tailWord_71173, baseEnd_71173] using wordTrace_append hprefix tailTrace_71173
  have hstable : (prefixWord ++ tailWord_71173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71173).length < 2 ^ (prefixWord ++ tailWord_71173).sum := by decide
  have hdescent : baseEnd_71173 < baseStart_71173 := by decide
  rcases family_descends (prefixWord ++ tailWord_71173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71198 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_71198 : Nat := 118140960795 + 71198 * 2 ^ 59
def prefixEnd_71198 : Nat := 4983230072969 + 3 ^ 40 * 71198 * 2
def baseEnd_71198 : Nat := 36558795638917671197573

theorem tailTrace_71198 : CollatzResearch.WordTrace tailWord_71198 prefixEnd_71198 36558795638917671197573 := by
  unfold tailWord_71198
  simp only [CollatzResearch.WordTrace]
  refine ⟨324600549508660061928781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1731202930712853663620165 324600549508660061928781)
  ·
    refine ⟨121725206065747523223293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 324600549508660061928781 121725206065747523223293)
    ·
      refine ⟨45646952274655321208735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121725206065747523223293 45646952274655321208735)
      ·
        refine ⟨68470428411982981813103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45646952274655321208735 68470428411982981813103)
        ·
          refine ⟨102705642617974472719655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68470428411982981813103 102705642617974472719655)
          ·
            refine ⟨154058463926961709079483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102705642617974472719655 154058463926961709079483)
            ·
              refine ⟨231087695890442563619225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154058463926961709079483 231087695890442563619225)
              ·
                refine ⟨173315771917831922714419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231087695890442563619225 173315771917831922714419)
                ·
                  refine ⟨259973657876747884071629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173315771917831922714419 259973657876747884071629)
                  ·
                    refine ⟨97490121703780456526861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 259973657876747884071629 97490121703780456526861)
                    ·
                      refine ⟨36558795638917671197573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 97490121703780456526861 36558795638917671197573)
                      ·
                        rfl

theorem cell23_71198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_71198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71198 prefixEnd_71198 := by exact prefixLift 71198
  have htrace : WordTrace (prefixWord ++ tailWord_71198) baseStart_71198 baseEnd_71198 := by
    simpa [prefixWord, tailWord_71198, baseEnd_71198] using wordTrace_append hprefix tailTrace_71198
  have hstable : (prefixWord ++ tailWord_71198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71198).length < 2 ^ (prefixWord ++ tailWord_71198).sum := by decide
  have hdescent : baseEnd_71198 < baseStart_71198 := by decide
  rcases family_descends (prefixWord ++ tailWord_71198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71208 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_71208 : Nat := 118140960795 + 71208 * 2 ^ 59
def prefixEnd_71208 : Nat := 4983230072969 + 3 ^ 40 * 71208 * 2
def baseEnd_71208 : Nat := 36563930445462632072527

theorem tailTrace_71208 : CollatzResearch.WordTrace tailWord_71208 prefixEnd_71208 36563930445462632072527 := by
  unfold tailWord_71208
  simp only [CollatzResearch.WordTrace]
  refine ⟨1298584563016526101647139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1731446084022034802196185 1298584563016526101647139)
  ·
    refine ⟨1947876844524789152470709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1298584563016526101647139 1947876844524789152470709)
    ·
      refine ⟨182613454174198983044129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1947876844524789152470709 182613454174198983044129)
      ·
        refine ⟨136960090630649237283097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182613454174198983044129 136960090630649237283097)
        ·
          refine ⟨102720067972986927962323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136960090630649237283097 102720067972986927962323)
          ·
            refine ⟨154080101959480391943485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102720067972986927962323 154080101959480391943485)
            ·
              refine ⟨57780038234805146978807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154080101959480391943485 57780038234805146978807)
              ·
                refine ⟨86670057352207720468211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57780038234805146978807 86670057352207720468211)
                ·
                  refine ⟨130005086028311580702317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86670057352207720468211 130005086028311580702317)
                  ·
                    refine ⟨48751907260616842763369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 130005086028311580702317 48751907260616842763369)
                    ·
                      refine ⟨36563930445462632072527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48751907260616842763369 36563930445462632072527)
                      ·
                        rfl

theorem cell23_71208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_71208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71208 prefixEnd_71208 := by exact prefixLift 71208
  have htrace : WordTrace (prefixWord ++ tailWord_71208) baseStart_71208 baseEnd_71208 := by
    simpa [prefixWord, tailWord_71208, baseEnd_71208] using wordTrace_append hprefix tailTrace_71208
  have hstable : (prefixWord ++ tailWord_71208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71208).length < 2 ^ (prefixWord ++ tailWord_71208).sum := by decide
  have hdescent : baseEnd_71208 < baseStart_71208 := by decide
  rcases family_descends (prefixWord ++ tailWord_71208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71221 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_71221 : Nat := 118140960795 + 71221 * 2 ^ 59
def prefixEnd_71221 : Nat := 4983230072969 + 3 ^ 40 * 71221 * 2
def baseEnd_71221 : Nat := 36570605693971081209967

theorem tailTrace_71221 : CollatzResearch.WordTrace tailWord_71221 prefixEnd_71221 36570605693971081209967 := by
  unfold tailWord_71221
  simp only [CollatzResearch.WordTrace]
  refine ⟨2597643274985955423517517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1731762183323970282345011 2597643274985955423517517)
  ·
    refine ⟨974116228119733283819069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2597643274985955423517517 974116228119733283819069)
    ·
      refine ⟨365293585544899981432151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 974116228119733283819069 365293585544899981432151)
      ·
        refine ⟨547940378317349972148227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365293585544899981432151 547940378317349972148227)
        ·
          refine ⟨821910567476024958222341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547940378317349972148227 821910567476024958222341)
          ·
            refine ⟨154108231401754679666689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 821910567476024958222341 154108231401754679666689)
            ·
              refine ⟨115581173551316009750017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154108231401754679666689 115581173551316009750017)
              ·
                refine ⟨86685880163487007312513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115581173551316009750017 86685880163487007312513)
                ·
                  refine ⟨65014410122615255484385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86685880163487007312513 65014410122615255484385)
                  ·
                    refine ⟨48760807591961441613289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65014410122615255484385 48760807591961441613289)
                    ·
                      refine ⟨36570605693971081209967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48760807591961441613289 36570605693971081209967)
                      ·
                        rfl

theorem cell23_71221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_71221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71221 prefixEnd_71221 := by exact prefixLift 71221
  have htrace : WordTrace (prefixWord ++ tailWord_71221) baseStart_71221 baseEnd_71221 := by
    simpa [prefixWord, tailWord_71221, baseEnd_71221] using wordTrace_append hprefix tailTrace_71221
  have hstable : (prefixWord ++ tailWord_71221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71221).length < 2 ^ (prefixWord ++ tailWord_71221).sum := by decide
  have hdescent : baseEnd_71221 < baseStart_71221 := by decide
  rcases family_descends (prefixWord ++ tailWord_71221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71238 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_71238 : Nat := 118140960795 + 71238 * 2 ^ 59
def prefixEnd_71238 : Nat := 4983230072969 + 3 ^ 40 * 71238 * 2
def baseEnd_71238 : Nat := 36579334865097514697389

theorem tailTrace_71238 : CollatzResearch.WordTrace tailWord_71238 prefixEnd_71238 36579334865097514697389 := by
  unfold tailWord_71238
  simp only [CollatzResearch.WordTrace]
  refine ⟨81195728622636478965199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1732175543949578217924245 81195728622636478965199)
  ·
    refine ⟨121793592933954718447799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81195728622636478965199 121793592933954718447799)
    ·
      refine ⟨182690389400932077671699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121793592933954718447799 182690389400932077671699)
      ·
        refine ⟨274035584101398116507549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182690389400932077671699 274035584101398116507549)
        ·
          refine ⟨102763344038024293690331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274035584101398116507549 102763344038024293690331)
          ·
            refine ⟨154145016057036440535497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102763344038024293690331 154145016057036440535497)
            ·
              refine ⟨115608762042777330401623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154145016057036440535497 115608762042777330401623)
              ·
                refine ⟨173413143064165995602435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115608762042777330401623 173413143064165995602435)
                ·
                  refine ⟨260119714596248993403653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173413143064165995602435 260119714596248993403653)
                  ·
                    refine ⟨48772446486796686263185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 260119714596248993403653 48772446486796686263185)
                    ·
                      refine ⟨36579334865097514697389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48772446486796686263185 36579334865097514697389)
                      ·
                        rfl

theorem cell23_71238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_71238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71238 prefixEnd_71238 := by exact prefixLift 71238
  have htrace : WordTrace (prefixWord ++ tailWord_71238) baseStart_71238 baseEnd_71238 := by
    simpa [prefixWord, tailWord_71238, baseEnd_71238] using wordTrace_append hprefix tailTrace_71238
  have hstable : (prefixWord ++ tailWord_71238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71238).length < 2 ^ (prefixWord ++ tailWord_71238).sum := by decide
  have hdescent : baseEnd_71238 < baseStart_71238 := by decide
  rcases family_descends (prefixWord ++ tailWord_71238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71297 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_71297 : Nat := 118140960795 + 71297 * 2 ^ 59
def prefixEnd_71297 : Nat := 4983230072969 + 3 ^ 40 * 71297 * 2
def baseEnd_71297 : Nat := 36609630223712783859617

theorem tailTrace_71297 : CollatzResearch.WordTrace tailWord_71297 prefixEnd_71297 36609630223712783859617 := by
  unfold tailWord_71297
  simp only [CollatzResearch.WordTrace]
  refine ⟨2600415222710620403284145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1733610148473746935522763 2600415222710620403284145)
  ·
    refine ⟨1950311417032965302463109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2600415222710620403284145 1950311417032965302463109)
    ·
      refine ⟨365683390693680994211833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1950311417032965302463109 365683390693680994211833)
      ·
        refine ⟨274262543020260745658875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 365683390693680994211833 274262543020260745658875)
        ·
          refine ⟨411393814530391118488313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274262543020260745658875 411393814530391118488313)
          ·
            refine ⟨308545360897793338866235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411393814530391118488313 308545360897793338866235)
            ·
              refine ⟨462818041346690008299353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308545360897793338866235 462818041346690008299353)
              ·
                refine ⟨347113531010017506224515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462818041346690008299353 347113531010017506224515)
                ·
                  refine ⟨520670296515026259336773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347113531010017506224515 520670296515026259336773)
                  ·
                    refine ⟨97625680596567423625645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 520670296515026259336773 97625680596567423625645)
                    ·
                      refine ⟨36609630223712783859617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 97625680596567423625645 36609630223712783859617)
                      ·
                        rfl

theorem cell23_71297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_71297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71297 prefixEnd_71297 := by exact prefixLift 71297
  have htrace : WordTrace (prefixWord ++ tailWord_71297) baseStart_71297 baseEnd_71297 := by
    simpa [prefixWord, tailWord_71297, baseEnd_71297] using wordTrace_append hprefix tailTrace_71297
  have hstable : (prefixWord ++ tailWord_71297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71297).length < 2 ^ (prefixWord ++ tailWord_71297).sum := by decide
  have hdescent : baseEnd_71297 < baseStart_71297 := by decide
  rcases family_descends (prefixWord ++ tailWord_71297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71344 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 3, 1, 3]
def baseStart_71344 : Nat := 118140960795 + 71344 * 2 ^ 59
def prefixEnd_71344 : Nat := 4983230072969 + 3 ^ 40 * 71344 * 2
def baseEnd_71344 : Nat := 36633763814474099971901

theorem tailTrace_71344 : CollatzResearch.WordTrace tailWord_71344 prefixEnd_71344 36633763814474099971901 := by
  unfold tailWord_71344
  simp only [CollatzResearch.WordTrace]
  refine ⟨1301064726770173715122543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1734752969026898286830057 1301064726770173715122543)
  ·
    refine ⟨1951597090155260572683815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1301064726770173715122543 1951597090155260572683815)
    ·
      refine ⟨2927395635232890859025723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951597090155260572683815 2927395635232890859025723)
      ·
        refine ⟨4391093452849336288538585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927395635232890859025723 4391093452849336288538585)
        ·
          refine ⟨3293320089637002216403939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4391093452849336288538585 3293320089637002216403939)
          ·
            refine ⟨4939980134455503324605909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3293320089637002216403939 4939980134455503324605909)
            ·
              refine ⟨115780784401300859170451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4939980134455503324605909 115780784401300859170451)
              ·
                refine ⟨173671176601951288755677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115780784401300859170451 173671176601951288755677)
                ·
                  refine ⟨65126691225731733283379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173671176601951288755677 65126691225731733283379)
                  ·
                    refine ⟨97690036838597599925069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65126691225731733283379 97690036838597599925069)
                    ·
                      refine ⟨36633763814474099971901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 97690036838597599925069 36633763814474099971901)
                      ·
                        rfl

theorem cell23_71344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3, 1, 3].length) (baseStart_71344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71344 prefixEnd_71344 := by exact prefixLift 71344
  have htrace : WordTrace (prefixWord ++ tailWord_71344) baseStart_71344 baseEnd_71344 := by
    simpa [prefixWord, tailWord_71344, baseEnd_71344] using wordTrace_append hprefix tailTrace_71344
  have hstable : (prefixWord ++ tailWord_71344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71344).length < 2 ^ (prefixWord ++ tailWord_71344).sum := by decide
  have hdescent : baseEnd_71344 < baseStart_71344 := by decide
  rcases family_descends (prefixWord ++ tailWord_71344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71367 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_71367 : Nat := 118140960795 + 71367 * 2 ^ 59
def prefixEnd_71367 : Nat := 4983230072969 + 3 ^ 40 * 71367 * 2
def baseEnd_71367 : Nat := 36645573869527509984295

theorem tailTrace_71367 : CollatzResearch.WordTrace tailWord_71367 prefixEnd_71367 36645573869527509984295 := by
  unfold tailWord_71367
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602968332457022358332355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1735312221638014905554903 2602968332457022358332355)
  ·
    refine ⟨3904452498685533537498533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2602968332457022358332355 3904452498685533537498533)
    ·
      refine ⟨732084843503537538280975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3904452498685533537498533 732084843503537538280975)
      ·
        refine ⟨1098127265255306307421463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732084843503537538280975 1098127265255306307421463)
        ·
          refine ⟨1647190897882959461132195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098127265255306307421463 1647190897882959461132195)
          ·
            refine ⟨2470786346824439191698293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647190897882959461132195 2470786346824439191698293)
            ·
              refine ⟨231636220014791174221715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2470786346824439191698293 231636220014791174221715)
              ·
                refine ⟨347454330022186761332573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231636220014791174221715 347454330022186761332573)
                ·
                  refine ⟨130295373758320035499715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347454330022186761332573 130295373758320035499715)
                  ·
                    refine ⟨195443060637480053249573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 130295373758320035499715 195443060637480053249573)
                    ·
                      refine ⟨36645573869527509984295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 195443060637480053249573 36645573869527509984295)
                      ·
                        rfl

theorem cell23_71367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_71367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71367 prefixEnd_71367 := by exact prefixLift 71367
  have htrace : WordTrace (prefixWord ++ tailWord_71367) baseStart_71367 baseEnd_71367 := by
    simpa [prefixWord, tailWord_71367, baseEnd_71367] using wordTrace_append hprefix tailTrace_71367
  have hstable : (prefixWord ++ tailWord_71367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71367).length < 2 ^ (prefixWord ++ tailWord_71367).sum := by decide
  have hdescent : baseEnd_71367 < baseStart_71367 := by decide
  rcases family_descends (prefixWord ++ tailWord_71367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71377 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 1, 6]
def baseStart_71377 : Nat := 118140960795 + 71377 * 2 ^ 59
def prefixEnd_71377 : Nat := 4983230072969 + 3 ^ 40 * 71377 * 2
def baseEnd_71377 : Nat := 12216902892024156953083

theorem tailTrace_71377 : CollatzResearch.WordTrace tailWord_71377 prefixEnd_71377 12216902892024156953083 := by
  unfold tailWord_71377
  simp only [CollatzResearch.WordTrace]
  refine ⟨2603333062420794066196385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1735555374947196044130923 2603333062420794066196385)
  ·
    refine ⟨1952499796815595549647289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2603333062420794066196385 1952499796815595549647289)
    ·
      refine ⟨1464374847611696662235467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1952499796815595549647289 1464374847611696662235467)
      ·
        refine ⟨2196562271417544993353201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464374847611696662235467 2196562271417544993353201)
        ·
          refine ⟨1647421703563158745014901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2196562271417544993353201 1647421703563158745014901)
          ·
            refine ⟨154445784709046132345147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1647421703563158745014901 154445784709046132345147)
            ·
              refine ⟨231668677063569198517721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154445784709046132345147 231668677063569198517721)
              ·
                refine ⟨173751507797676898888291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231668677063569198517721 173751507797676898888291)
                ·
                  refine ⟨260627261696515348332437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173751507797676898888291 260627261696515348332437)
                  ·
                    refine ⟨12216902892024156953083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 260627261696515348332437 12216902892024156953083)
                    ·
                      rfl

theorem cell23_71377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_71377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71377 prefixEnd_71377 := by exact prefixLift 71377
  have htrace : WordTrace (prefixWord ++ tailWord_71377) baseStart_71377 baseEnd_71377 := by
    simpa [prefixWord, tailWord_71377, baseEnd_71377] using wordTrace_append hprefix tailTrace_71377
  have hstable : (prefixWord ++ tailWord_71377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71377).length < 2 ^ (prefixWord ++ tailWord_71377).sum := by decide
  have hdescent : baseEnd_71377 < baseStart_71377 := by decide
  rcases family_descends (prefixWord ++ tailWord_71377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71397 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_71397 : Nat := 118140960795 + 71397 * 2 ^ 59
def prefixEnd_71397 : Nat := 4983230072969 + 3 ^ 40 * 71397 * 2
def baseEnd_71397 : Nat := 36660978289162392609157

theorem tailTrace_71397 : CollatzResearch.WordTrace tailWord_71397 prefixEnd_71397 36660978289162392609157 := by
  unfold tailWord_71397
  simp only [CollatzResearch.WordTrace]
  refine ⟨2604062522348337481924445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1736041681565558321282963 2604062522348337481924445)
  ·
    refine ⟨976523445880626555721667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2604062522348337481924445 976523445880626555721667)
    ·
      refine ⟨1464785168820939833582501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 976523445880626555721667 1464785168820939833582501)
      ·
        refine ⟨274647219153926218796719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1464785168820939833582501 274647219153926218796719)
        ·
          refine ⟨411970828730889328195079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274647219153926218796719 411970828730889328195079)
          ·
            refine ⟨617956243096333992292619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411970828730889328195079 617956243096333992292619)
            ·
              refine ⟨926934364644500988438929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617956243096333992292619 926934364644500988438929)
              ·
                refine ⟨695200773483375741329197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926934364644500988438929 695200773483375741329197)
                ·
                  refine ⟨260700290056265902998449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 695200773483375741329197 260700290056265902998449)
                  ·
                    refine ⟨195525217542199427248837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 260700290056265902998449 195525217542199427248837)
                    ·
                      refine ⟨36660978289162392609157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 195525217542199427248837 36660978289162392609157)
                      ·
                        rfl

theorem cell23_71397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_71397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71397 prefixEnd_71397 := by exact prefixLift 71397
  have htrace : WordTrace (prefixWord ++ tailWord_71397) baseStart_71397 baseEnd_71397 := by
    simpa [prefixWord, tailWord_71397, baseEnd_71397] using wordTrace_append hprefix tailTrace_71397
  have hstable : (prefixWord ++ tailWord_71397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71397).length < 2 ^ (prefixWord ++ tailWord_71397).sum := by decide
  have hdescent : baseEnd_71397 < baseStart_71397 := by decide
  rcases family_descends (prefixWord ++ tailWord_71397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71414 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_71414 : Nat := 118140960795 + 71414 * 2 ^ 59
def prefixEnd_71414 : Nat := 4983230072969 + 3 ^ 40 * 71414 * 2
def baseEnd_71414 : Nat := 36669707460288826096579

theorem tailTrace_71414 : CollatzResearch.WordTrace tailWord_71414 prefixEnd_71414 36669707460288826096579 := by
  unfold tailWord_71414
  simp only [CollatzResearch.WordTrace]
  refine ⟨162792660205421836580831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1736455042191166256862197 162792660205421836580831)
  ·
    refine ⟨244188990308132754871247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162792660205421836580831 244188990308132754871247)
    ·
      refine ⟨366283485462199132306871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244188990308132754871247 366283485462199132306871)
      ·
        refine ⟨549425228193298698460307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366283485462199132306871 549425228193298698460307)
        ·
          refine ⟨824137842289948047690461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549425228193298698460307 824137842289948047690461)
          ·
            refine ⟨309051690858730517883923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 824137842289948047690461 309051690858730517883923)
            ·
              refine ⟨463577536288095776825885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309051690858730517883923 463577536288095776825885)
              ·
                refine ⟨173841576108035916309707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 463577536288095776825885 173841576108035916309707)
                ·
                  refine ⟨260762364162053874464561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173841576108035916309707 260762364162053874464561)
                  ·
                    refine ⟨195571773121540405848421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 260762364162053874464561 195571773121540405848421)
                    ·
                      refine ⟨36669707460288826096579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 195571773121540405848421 36669707460288826096579)
                      ·
                        rfl

theorem cell23_71414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_71414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71414 prefixEnd_71414 := by exact prefixLift 71414
  have htrace : WordTrace (prefixWord ++ tailWord_71414) baseStart_71414 baseEnd_71414 := by
    simpa [prefixWord, tailWord_71414, baseEnd_71414] using wordTrace_append hprefix tailTrace_71414
  have hstable : (prefixWord ++ tailWord_71414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71414).length < 2 ^ (prefixWord ++ tailWord_71414).sum := by decide
  have hdescent : baseEnd_71414 < baseStart_71414 := by decide
  rcases family_descends (prefixWord ++ tailWord_71414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71434 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_71434 : Nat := 118140960795 + 71434 * 2 ^ 59
def prefixEnd_71434 : Nat := 4983230072969 + 3 ^ 40 * 71434 * 2
def baseEnd_71434 : Nat := 36679977073378747846487

theorem tailTrace_71434 : CollatzResearch.WordTrace tailWord_71434 prefixEnd_71434 36679977073378747846487 := by
  unfold tailWord_71434
  simp only [CollatzResearch.WordTrace]
  refine ⟨651353005803573200255339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1736941348809528534014237 651353005803573200255339)
  ·
    refine ⟨977029508705359800383009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 651353005803573200255339 977029508705359800383009)
    ·
      refine ⟨732772131529019850287257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 977029508705359800383009 732772131529019850287257)
      ·
        refine ⟨549579098646764887715443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 732772131529019850287257 549579098646764887715443)
        ·
          refine ⟨824368647970147331573165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549579098646764887715443 824368647970147331573165)
          ·
            refine ⟨309138242988805249339937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 824368647970147331573165 309138242988805249339937)
            ·
              refine ⟨231853682241603937004953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309138242988805249339937 231853682241603937004953)
              ·
                refine ⟨173890261681202952753715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231853682241603937004953 173890261681202952753715)
                ·
                  refine ⟨260835392521804429130573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173890261681202952753715 260835392521804429130573)
                  ·
                    refine ⟨97813272195676660923965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 260835392521804429130573 97813272195676660923965)
                    ·
                      refine ⟨36679977073378747846487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 97813272195676660923965 36679977073378747846487)
                      ·
                        rfl

theorem cell23_71434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_71434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71434 prefixEnd_71434 := by exact prefixLift 71434
  have htrace : WordTrace (prefixWord ++ tailWord_71434) baseStart_71434 baseEnd_71434 := by
    simpa [prefixWord, tailWord_71434, baseEnd_71434] using wordTrace_append hprefix tailTrace_71434
  have hstable : (prefixWord ++ tailWord_71434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71434).length < 2 ^ (prefixWord ++ tailWord_71434).sum := by decide
  have hdescent : baseEnd_71434 < baseStart_71434 := by decide
  rcases family_descends (prefixWord ++ tailWord_71434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71468 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 3]
def baseStart_71468 : Nat := 118140960795 + 71468 * 2 ^ 59
def prefixEnd_71468 : Nat := 4983230072969 + 3 ^ 40 * 71468 * 2
def baseEnd_71468 : Nat := 36697435415631614821331

theorem tailTrace_71468 : CollatzResearch.WordTrace tailWord_71468 prefixEnd_71468 36697435415631614821331 := by
  unfold tailWord_71468
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303326052545558303879529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1737768070060744405172705 1303326052545558303879529)
  ·
    refine ⟨977494539409168727909647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1303326052545558303879529 977494539409168727909647)
    ·
      refine ⟨1466241809113753091864471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 977494539409168727909647 1466241809113753091864471)
      ·
        refine ⟨2199362713670629637796707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466241809113753091864471 2199362713670629637796707)
        ·
          refine ⟨3299044070505944456695061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199362713670629637796707 3299044070505944456695061)
          ·
            refine ⟨154642690804966146407581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3299044070505944456695061 154642690804966146407581)
            ·
              refine ⟨57991009051862304902843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154642690804966146407581 57991009051862304902843)
              ·
                refine ⟨86986513577793457354265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57991009051862304902843 86986513577793457354265)
                ·
                  refine ⟨65239885183345093015699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86986513577793457354265 65239885183345093015699)
                  ·
                    refine ⟨97859827775017639523549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65239885183345093015699 97859827775017639523549)
                    ·
                      refine ⟨36697435415631614821331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 97859827775017639523549 36697435415631614821331)
                      ·
                        rfl

theorem cell23_71468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 3].length) (baseStart_71468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71468 prefixEnd_71468 := by exact prefixLift 71468
  have htrace : WordTrace (prefixWord ++ tailWord_71468) baseStart_71468 baseEnd_71468 := by
    simpa [prefixWord, tailWord_71468, baseEnd_71468] using wordTrace_append hprefix tailTrace_71468
  have hstable : (prefixWord ++ tailWord_71468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71468).length < 2 ^ (prefixWord ++ tailWord_71468).sum := by decide
  have hdescent : baseEnd_71468 < baseStart_71468 := by decide
  rcases family_descends (prefixWord ++ tailWord_71468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71491 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 4, 2, 2]
def baseStart_71491 : Nat := 118140960795 + 71491 * 2 ^ 59
def prefixEnd_71491 : Nat := 4983230072969 + 3 ^ 40 * 71491 * 2
def baseEnd_71491 : Nat := 36709245470685024833725

theorem tailTrace_71491 : CollatzResearch.WordTrace tailWord_71491 prefixEnd_71491 36709245470685024833725 := by
  unfold tailWord_71491
  simp only [CollatzResearch.WordTrace]
  refine ⟨2607490984007791535846327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1738327322671861023897551 2607490984007791535846327)
  ·
    refine ⟨3911236476011687303769491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2607490984007791535846327 3911236476011687303769491)
    ·
      refine ⟨5866854714017530955654237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911236476011687303769491 5866854714017530955654237)
      ·
        refine ⟨2200070517756574108370339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5866854714017530955654237 2200070517756574108370339)
        ·
          refine ⟨3300105776634861162555509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2200070517756574108370339 3300105776634861162555509)
          ·
            refine ⟨309384916559518233989579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3300105776634861162555509 309384916559518233989579)
            ·
              refine ⟨464077374839277350984369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309384916559518233989579 464077374839277350984369)
              ·
                refine ⟨348058031129458013238277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464077374839277350984369 348058031129458013238277)
                ·
                  refine ⟨65260880836773377482177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348058031129458013238277 65260880836773377482177)
                  ·
                    refine ⟨48945660627580033111633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65260880836773377482177 48945660627580033111633)
                    ·
                      refine ⟨36709245470685024833725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48945660627580033111633 36709245470685024833725)
                      ·
                        rfl

theorem cell23_71491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 2, 2].length) (baseStart_71491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71491 prefixEnd_71491 := by exact prefixLift 71491
  have htrace : WordTrace (prefixWord ++ tailWord_71491) baseStart_71491 baseEnd_71491 := by
    simpa [prefixWord, tailWord_71491, baseEnd_71491] using wordTrace_append hprefix tailTrace_71491
  have hstable : (prefixWord ++ tailWord_71491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71491).length < 2 ^ (prefixWord ++ tailWord_71491).sum := by decide
  have hdescent : baseEnd_71491 < baseStart_71491 := by decide
  rcases family_descends (prefixWord ++ tailWord_71491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71508 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_71508 : Nat := 118140960795 + 71508 * 2 ^ 59
def prefixEnd_71508 : Nat := 4983230072969 + 3 ^ 40 * 71508 * 2
def baseEnd_71508 : Nat := 36717974641811458321147

theorem tailTrace_71508 : CollatzResearch.WordTrace tailWord_71508 prefixEnd_71508 36717974641811458321147 := by
  unfold tailWord_71508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1304055512473101719607589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1738740683297468959476785 1304055512473101719607589)
  ·
    refine ⟨244510408588706572426423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1304055512473101719607589 244510408588706572426423)
    ·
      refine ⟨366765612883059858639635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244510408588706572426423 366765612883059858639635)
      ·
        refine ⟨550148419324589787959453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366765612883059858639635 550148419324589787959453)
        ·
          refine ⟨206305657246721170484795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 550148419324589787959453 206305657246721170484795)
          ·
            refine ⟨309458485870081755727193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206305657246721170484795 309458485870081755727193)
            ·
              refine ⟨232093864402561316795395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309458485870081755727193 232093864402561316795395)
              ·
                refine ⟨348140796603841975193093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232093864402561316795395 348140796603841975193093)
                ·
                  refine ⟨65276399363220370348705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348140796603841975193093 65276399363220370348705)
                  ·
                    refine ⟨48957299522415277761529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65276399363220370348705 48957299522415277761529)
                    ·
                      refine ⟨36717974641811458321147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48957299522415277761529 36717974641811458321147)
                      ·
                        rfl

theorem cell23_71508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_71508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71508 prefixEnd_71508 := by exact prefixLift 71508
  have htrace : WordTrace (prefixWord ++ tailWord_71508) baseStart_71508 baseEnd_71508 := by
    simpa [prefixWord, tailWord_71508, baseEnd_71508] using wordTrace_append hprefix tailTrace_71508
  have hstable : (prefixWord ++ tailWord_71508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71508).length < 2 ^ (prefixWord ++ tailWord_71508).sum := by decide
  have hdescent : baseEnd_71508 < baseStart_71508 := by decide
  rcases family_descends (prefixWord ++ tailWord_71508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71537 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_71537 : Nat := 118140960795 + 71537 * 2 ^ 59
def prefixEnd_71537 : Nat := 4983230072969 + 3 ^ 40 * 71537 * 2
def baseEnd_71537 : Nat := 36732865580791844858513

theorem tailTrace_71537 : CollatzResearch.WordTrace tailWord_71537 prefixEnd_71537 36732865580791844858513 := by
  unfold tailWord_71537
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609168741841141392020865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1739445827894094261347243 2609168741841141392020865)
  ·
    refine ⟨1956876556380856044015649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2609168741841141392020865 1956876556380856044015649)
    ·
      refine ⟨1467657417285642033011737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1956876556380856044015649 1467657417285642033011737)
      ·
        refine ⟨1100743062964231524758803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1467657417285642033011737 1100743062964231524758803)
        ·
          refine ⟨1651114594446347287138205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1100743062964231524758803 1651114594446347287138205)
          ·
            refine ⟨619167972917380232676827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1651114594446347287138205 619167972917380232676827)
            ·
              refine ⟨928751959376070349015241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619167972917380232676827 928751959376070349015241)
              ·
                refine ⟨696563969532052761761431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 928751959376070349015241 696563969532052761761431)
                ·
                  refine ⟨1044845954298079142642147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696563969532052761761431 1044845954298079142642147)
                  ·
                    refine ⟨1567268931447118713963221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1044845954298079142642147 1567268931447118713963221)
                    ·
                      refine ⟨36732865580791844858513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1567268931447118713963221 36732865580791844858513)
                      ·
                        rfl

theorem cell23_71537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_71537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71537 prefixEnd_71537 := by exact prefixLift 71537
  have htrace : WordTrace (prefixWord ++ tailWord_71537) baseStart_71537 baseEnd_71537 := by
    simpa [prefixWord, tailWord_71537, baseEnd_71537] using wordTrace_append hprefix tailTrace_71537
  have hstable : (prefixWord ++ tailWord_71537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71537).length < 2 ^ (prefixWord ++ tailWord_71537).sum := by decide
  have hdescent : baseEnd_71537 < baseStart_71537 := by decide
  rcases family_descends (prefixWord ++ tailWord_71537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71581 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_71581 : Nat := 118140960795 + 71581 * 2 ^ 59
def prefixEnd_71581 : Nat := 4983230072969 + 3 ^ 40 * 71581 * 2
def baseEnd_71581 : Nat := 36755458729589672708311

theorem tailTrace_71581 : CollatzResearch.WordTrace tailWord_71581 prefixEnd_71581 36755458729589672708311 := by
  unfold tailWord_71581
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610773553681736906622597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1740515702454491271081731 2610773553681736906622597)
  ·
    refine ⟨489520041315325669991737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2610773553681736906622597 489520041315325669991737)
    ·
      refine ⟨367140030986494252493803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 489520041315325669991737 367140030986494252493803)
      ·
        refine ⟨550710046479741378740705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367140030986494252493803 550710046479741378740705)
        ·
          refine ⟨413032534859806034055529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 550710046479741378740705 413032534859806034055529)
          ·
            refine ⟨309774401144854525541647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413032534859806034055529 309774401144854525541647)
            ·
              refine ⟨464661601717281788312471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309774401144854525541647 464661601717281788312471)
              ·
                refine ⟨696992402575922682468707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464661601717281788312471 696992402575922682468707)
                ·
                  refine ⟨1045488603863884023703061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696992402575922682468707 1045488603863884023703061)
                  ·
                    refine ⟨49007278306119563611081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1045488603863884023703061 49007278306119563611081)
                    ·
                      refine ⟨36755458729589672708311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49007278306119563611081 36755458729589672708311)
                      ·
                        rfl

theorem cell23_71581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_71581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71581 prefixEnd_71581 := by exact prefixLift 71581
  have htrace : WordTrace (prefixWord ++ tailWord_71581) baseStart_71581 baseEnd_71581 := by
    simpa [prefixWord, tailWord_71581, baseEnd_71581] using wordTrace_append hprefix tailTrace_71581
  have hstable : (prefixWord ++ tailWord_71581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71581).length < 2 ^ (prefixWord ++ tailWord_71581).sum := by decide
  have hdescent : baseEnd_71581 < baseStart_71581 := by decide
  rcases family_descends (prefixWord ++ tailWord_71581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71584 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 3]
def baseStart_71584 : Nat := 118140960795 + 71584 * 2 ^ 59
def prefixEnd_71584 : Nat := 4983230072969 + 3 ^ 40 * 71584 * 2
def baseEnd_71584 : Nat := 36756999171553160970797

theorem tailTrace_71584 : CollatzResearch.WordTrace tailWord_71584 prefixEnd_71584 36756999171553160970797 := by
  unfold tailWord_71584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305441486335434209490903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1740588648447245612654537 1305441486335434209490903)
  ·
    refine ⟨1958162229503151314236355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1305441486335434209490903 1958162229503151314236355)
    ·
      refine ⟨2937243344254726971354533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1958162229503151314236355 2937243344254726971354533)
      ·
        refine ⟨550733127047761307128975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2937243344254726971354533 550733127047761307128975)
        ·
          refine ⟨826099690571641960693463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550733127047761307128975 826099690571641960693463)
          ·
            refine ⟨1239149535857462941040195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826099690571641960693463 1239149535857462941040195)
            ·
              refine ⟨1858724303786194411560293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239149535857462941040195 1858724303786194411560293)
              ·
                refine ⟨348510806959911452167555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1858724303786194411560293 348510806959911452167555)
                ·
                  refine ⟨522766210439867178251333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348510806959911452167555 522766210439867178251333)
                  ·
                    refine ⟨98018664457475095922125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 522766210439867178251333 98018664457475095922125)
                    ·
                      refine ⟨36756999171553160970797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 98018664457475095922125 36756999171553160970797)
                      ·
                        rfl

theorem cell23_71584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_71584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71584 prefixEnd_71584 := by exact prefixLift 71584
  have htrace : WordTrace (prefixWord ++ tailWord_71584) baseStart_71584 baseEnd_71584 := by
    simpa [prefixWord, tailWord_71584, baseEnd_71584] using wordTrace_append hprefix tailTrace_71584
  have hstable : (prefixWord ++ tailWord_71584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71584).length < 2 ^ (prefixWord ++ tailWord_71584).sum := by decide
  have hdescent : baseEnd_71584 < baseStart_71584 := by decide
  rcases family_descends (prefixWord ++ tailWord_71584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71587 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 10]
def baseStart_71587 : Nat := 118140960795 + 71587 * 2 ^ 59
def prefixEnd_71587 : Nat := 4983230072969 + 3 ^ 40 * 71587 * 2
def baseEnd_71587 : Nat := 4084282179279627692587

theorem tailTrace_71587 : CollatzResearch.WordTrace tailWord_71587 prefixEnd_71587 4084282179279627692587 := by
  unfold tailWord_71587
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610992391659999931341015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1740661594439999954227343 2610992391659999931341015)
  ·
    refine ⟨3916488587489999897011523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2610992391659999931341015 3916488587489999897011523)
    ·
      refine ⟨5874732881234999845517285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3916488587489999897011523 5874732881234999845517285)
      ·
        refine ⟨1101512415231562471034491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5874732881234999845517285 1101512415231562471034491)
        ·
          refine ⟨1652268622847343706551737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101512415231562471034491 1652268622847343706551737)
          ·
            refine ⟨1239201467135507779913803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1652268622847343706551737 1239201467135507779913803)
            ·
              refine ⟨1858802200703261669870705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239201467135507779913803 1858802200703261669870705)
              ·
                refine ⟨1394101650527446252403029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1858802200703261669870705 1394101650527446252403029)
                ·
                  refine ⟨4084282179279627692587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1394101650527446252403029 4084282179279627692587)
                  ·
                    rfl

theorem cell23_71587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 10].length) (baseStart_71587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71587 prefixEnd_71587 := by exact prefixLift 71587
  have htrace : WordTrace (prefixWord ++ tailWord_71587) baseStart_71587 baseEnd_71587 := by
    simpa [prefixWord, tailWord_71587, baseEnd_71587] using wordTrace_append hprefix tailTrace_71587
  have hstable : (prefixWord ++ tailWord_71587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71587).length < 2 ^ (prefixWord ++ tailWord_71587).sum := by decide
  have hdescent : baseEnd_71587 < baseStart_71587 := by decide
  rcases family_descends (prefixWord ++ tailWord_71587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71591 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 5, 4]
def baseStart_71591 : Nat := 118140960795 + 71591 * 2 ^ 59
def prefixEnd_71591 : Nat := 4983230072969 + 3 ^ 40 * 71591 * 2
def baseEnd_71591 : Nat := 12253531178711544527755

theorem tailTrace_71591 : CollatzResearch.WordTrace tailWord_71591 prefixEnd_71591 12253531178711544527755 := by
  unfold tailWord_71591
  simp only [CollatzResearch.WordTrace]
  refine ⟨2611138283645508614486627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1740758855763672409657751 2611138283645508614486627)
  ·
    refine ⟨3916707425468262921729941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2611138283645508614486627 3916707425468262921729941)
    ·
      refine ⟨183595660568824824456091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3916707425468262921729941 183595660568824824456091)
      ·
        refine ⟨275393490853237236684137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183595660568824824456091 275393490853237236684137)
        ·
          refine ⟨206545118139927927513103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275393490853237236684137 206545118139927927513103)
          ·
            refine ⟨309817677209891891269655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206545118139927927513103 309817677209891891269655)
            ·
              refine ⟨464726515814837836904483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309817677209891891269655 464726515814837836904483)
              ·
                refine ⟨697089773722256755356725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464726515814837836904483 697089773722256755356725)
                ·
                  refine ⟨65352166286461570814693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 697089773722256755356725 65352166286461570814693)
                  ·
                    refine ⟨12253531178711544527755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65352166286461570814693 12253531178711544527755)
                    ·
                      rfl

theorem cell23_71591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_71591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71591 prefixEnd_71591 := by exact prefixLift 71591
  have htrace : WordTrace (prefixWord ++ tailWord_71591) baseStart_71591 baseEnd_71591 := by
    simpa [prefixWord, tailWord_71591, baseEnd_71591] using wordTrace_append hprefix tailTrace_71591
  have hstable : (prefixWord ++ tailWord_71591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71591).length < 2 ^ (prefixWord ++ tailWord_71591).sum := by decide
  have hdescent : baseEnd_71591 < baseStart_71591 := by decide
  rcases family_descends (prefixWord ++ tailWord_71591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71601 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 1, 4, 3]
def baseStart_71601 : Nat := 118140960795 + 71601 * 2 ^ 59
def prefixEnd_71601 : Nat := 4983230072969 + 3 ^ 40 * 71601 * 2
def baseEnd_71601 : Nat := 36765728342679594458219

theorem tailTrace_71601 : CollatzResearch.WordTrace tailWord_71601 prefixEnd_71601 36765728342679594458219 := by
  unfold tailWord_71601
  simp only [CollatzResearch.WordTrace]
  refine ⟨2611503013609280322350657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1741002009072853548233771 2611503013609280322350657)
  ·
    refine ⟨1958627260206960241762993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2611503013609280322350657 1958627260206960241762993)
    ·
      refine ⟨1468970445155220181322245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1958627260206960241762993 1468970445155220181322245)
      ·
        refine ⟨275431958466603783997921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1468970445155220181322245 275431958466603783997921)
        ·
          refine ⟨206573968849952837998441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275431958466603783997921 206573968849952837998441)
          ·
            refine ⟨154930476637464628498831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206573968849952837998441 154930476637464628498831)
            ·
              refine ⟨232395714956196942748247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154930476637464628498831 232395714956196942748247)
              ·
                refine ⟨348593572434295414122371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232395714956196942748247 348593572434295414122371)
                ·
                  refine ⟨522890358651443121183557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348593572434295414122371 522890358651443121183557)
                  ·
                    refine ⟨98041942247145585221917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 522890358651443121183557 98041942247145585221917)
                    ·
                      refine ⟨36765728342679594458219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 98041942247145585221917 36765728342679594458219)
                      ·
                        rfl

theorem cell23_71601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_71601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71601 prefixEnd_71601 := by exact prefixLift 71601
  have htrace : WordTrace (prefixWord ++ tailWord_71601) baseStart_71601 baseEnd_71601 := by
    simpa [prefixWord, tailWord_71601, baseEnd_71601] using wordTrace_append hprefix tailTrace_71601
  have hstable : (prefixWord ++ tailWord_71601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71601).length < 2 ^ (prefixWord ++ tailWord_71601).sum := by decide
  have hdescent : baseEnd_71601 < baseStart_71601 := by decide
  rcases family_descends (prefixWord ++ tailWord_71601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71608 : List Nat := [2, 1, 2, 1, 2, 3, 4, 3, 1, 4]
def baseStart_71608 : Nat := 118140960795 + 71608 * 2 ^ 59
def prefixEnd_71608 : Nat := 4983230072969 + 3 ^ 40 * 71608 * 2
def baseEnd_71608 : Nat := 12256440902420355690229

theorem tailTrace_71608 : CollatzResearch.WordTrace tailWord_71608 prefixEnd_71608 12256440902420355690229 := by
  unfold tailWord_71608
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305879162291960258927739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1741172216389280345236985 1305879162291960258927739)
  ·
    refine ⟨1958818743437940388391609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1305879162291960258927739 1958818743437940388391609)
    ·
      refine ⟨1469114057578455291293707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1958818743437940388391609 1469114057578455291293707)
      ·
        refine ⟨2203671086367682936940561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469114057578455291293707 2203671086367682936940561)
        ·
          refine ⟨1652753314775762202705421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2203671086367682936940561 1652753314775762202705421)
          ·
            refine ⟨619782493040910826014533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1652753314775762202705421 619782493040910826014533)
            ·
              refine ⟨116209217445170779877725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 619782493040910826014533 116209217445170779877725)
              ·
                refine ⟨43578456541939042454147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116209217445170779877725 43578456541939042454147)
                ·
                  refine ⟨65367684812908563681221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43578456541939042454147 65367684812908563681221)
                  ·
                    refine ⟨12256440902420355690229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65367684812908563681221 12256440902420355690229)
                    ·
                      rfl

theorem cell23_71608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_71608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71608 prefixEnd_71608 := by exact prefixLift 71608
  have htrace : WordTrace (prefixWord ++ tailWord_71608) baseStart_71608 baseEnd_71608 := by
    simpa [prefixWord, tailWord_71608, baseEnd_71608] using wordTrace_append hprefix tailTrace_71608
  have hstable : (prefixWord ++ tailWord_71608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71608).length < 2 ^ (prefixWord ++ tailWord_71608).sum := by decide
  have hdescent : baseEnd_71608 < baseStart_71608 := by decide
  rcases family_descends (prefixWord ++ tailWord_71608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71624 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_71624 : Nat := 118140960795 + 71624 * 2 ^ 59
def prefixEnd_71624 : Nat := 4983230072969 + 3 ^ 40 * 71624 * 2
def baseEnd_71624 : Nat := 36777538397733004470613

theorem tailTrace_71624 : CollatzResearch.WordTrace tailWord_71624 prefixEnd_71624 36777538397733004470613 := by
  unfold tailWord_71624
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306170946262977625218963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1741561261683970166958617 1306170946262977625218963)
  ·
    refine ⟨1959256419394466437828445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1306170946262977625218963 1959256419394466437828445)
    ·
      refine ⟨734721157272924914185667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1959256419394466437828445 734721157272924914185667)
      ·
        refine ⟨1102081735909387371278501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734721157272924914185667 1102081735909387371278501)
        ·
          refine ⟨206640325483010132114719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1102081735909387371278501 206640325483010132114719)
          ·
            refine ⟨309960488224515198172079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206640325483010132114719 309960488224515198172079)
            ·
              refine ⟨464940732336772797258119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309960488224515198172079 464940732336772797258119)
              ·
                refine ⟨697411098505159195887179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464940732336772797258119 697411098505159195887179)
                ·
                  refine ⟨1046116647757738793830769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697411098505159195887179 1046116647757738793830769)
                  ·
                    refine ⟨784587485818304095373077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1046116647757738793830769 784587485818304095373077)
                    ·
                      refine ⟨36777538397733004470613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 784587485818304095373077 36777538397733004470613)
                      ·
                        rfl

theorem cell23_71624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_71624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71624 prefixEnd_71624 := by exact prefixLift 71624
  have htrace : WordTrace (prefixWord ++ tailWord_71624) baseStart_71624 baseEnd_71624 := by
    simpa [prefixWord, tailWord_71624, baseEnd_71624] using wordTrace_append hprefix tailTrace_71624
  have hstable : (prefixWord ++ tailWord_71624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71624).length < 2 ^ (prefixWord ++ tailWord_71624).sum := by decide
  have hdescent : baseEnd_71624 < baseStart_71624 := by decide
  rcases family_descends (prefixWord ++ tailWord_71624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71651 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 1, 5]
def baseStart_71651 : Nat := 118140960795 + 71651 * 2 ^ 59
def prefixEnd_71651 : Nat := 4983230072969 + 3 ^ 40 * 71651 * 2
def baseEnd_71651 : Nat := 12263800791801466277663

theorem tailTrace_71651 : CollatzResearch.WordTrace tailWord_71651 prefixEnd_71651 12263800791801466277663 := by
  unfold tailWord_71651
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613326663428138861670807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1742217775618759241113871 2613326663428138861670807)
  ·
    refine ⟨3919989995142208292506211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2613326663428138861670807 3919989995142208292506211)
    ·
      refine ⟨5879984992713312438759317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3919989995142208292506211 5879984992713312438759317)
      ·
        refine ⟨275624296533436520566843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5879984992713312438759317 275624296533436520566843)
        ·
          refine ⟨413436444800154780850265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275624296533436520566843 413436444800154780850265)
          ·
            refine ⟨310077333600116085637699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413436444800154780850265 310077333600116085637699)
            ·
              refine ⟨465116000400174128456549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310077333600116085637699 465116000400174128456549)
              ·
                refine ⟨87209250075032649085603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 465116000400174128456549 87209250075032649085603)
                ·
                  refine ⟨130813875112548973628405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87209250075032649085603 130813875112548973628405)
                  ·
                    refine ⟨12263800791801466277663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 130813875112548973628405 12263800791801466277663)
                    ·
                      rfl

theorem cell23_71651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 5].length) (baseStart_71651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71651 prefixEnd_71651 := by exact prefixLift 71651
  have htrace : WordTrace (prefixWord ++ tailWord_71651) baseStart_71651 baseEnd_71651 := by
    simpa [prefixWord, tailWord_71651, baseEnd_71651] using wordTrace_append hprefix tailTrace_71651
  have hstable : (prefixWord ++ tailWord_71651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71651).length < 2 ^ (prefixWord ++ tailWord_71651).sum := by decide
  have hdescent : baseEnd_71651 < baseStart_71651 := by decide
  rcases family_descends (prefixWord ++ tailWord_71651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71658 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_71658 : Nat := 118140960795 + 71658 * 2 ^ 59
def prefixEnd_71658 : Nat := 4983230072969 + 3 ^ 40 * 71658 * 2
def baseEnd_71658 : Nat := 36794996739985871445457

theorem tailTrace_71658 : CollatzResearch.WordTrace tailWord_71658 prefixEnd_71658 36794996739985871445457 := by
  unfold tailWord_71658
  simp only [CollatzResearch.WordTrace]
  refine ⟨653395493600694764293907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1742387982935186038117085 653395493600694764293907)
  ·
    refine ⟨980093240401042146440861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 653395493600694764293907 980093240401042146440861)
    ·
      refine ⟨367534965150390804915323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 980093240401042146440861 367534965150390804915323)
      ·
        refine ⟨551302447725586207372985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367534965150390804915323 551302447725586207372985)
        ·
          refine ⟨413476835794189655529739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551302447725586207372985 413476835794189655529739)
          ·
            refine ⟨620215253691284483294609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413476835794189655529739 620215253691284483294609)
            ·
              refine ⟨465161440268463362470957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620215253691284483294609 465161440268463362470957)
              ·
                refine ⟨174435540100673760926609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 465161440268463362470957 174435540100673760926609)
                ·
                  refine ⟨130826655075505320694957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174435540100673760926609 130826655075505320694957)
                  ·
                    refine ⟨49059995653314495260609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 130826655075505320694957 49059995653314495260609)
                    ·
                      refine ⟨36794996739985871445457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49059995653314495260609 36794996739985871445457)
                      ·
                        rfl

theorem cell23_71658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_71658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71658 prefixEnd_71658 := by exact prefixLift 71658
  have htrace : WordTrace (prefixWord ++ tailWord_71658) baseStart_71658 baseEnd_71658 := by
    simpa [prefixWord, tailWord_71658, baseEnd_71658] using wordTrace_append hprefix tailTrace_71658
  have hstable : (prefixWord ++ tailWord_71658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71658).length < 2 ^ (prefixWord ++ tailWord_71658).sum := by decide
  have hdescent : baseEnd_71658 < baseStart_71658 := by decide
  rcases family_descends (prefixWord ++ tailWord_71658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71664 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 1, 6]
def baseStart_71664 : Nat := 118140960795 + 71664 * 2 ^ 59
def prefixEnd_71664 : Nat := 4983230072969 + 3 ^ 40 * 71664 * 2
def baseEnd_71664 : Nat := 12266025874637615990143

theorem tailTrace_71664 : CollatzResearch.WordTrace tailWord_71664 prefixEnd_71664 12266025874637615990143 := by
  unfold tailWord_71664
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306900406190521040947023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1742533874920694721262697 1306900406190521040947023)
  ·
    refine ⟨1960350609285781561420535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1306900406190521040947023 1960350609285781561420535)
    ·
      refine ⟨2940525913928672342130803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1960350609285781561420535 2940525913928672342130803)
      ·
        refine ⟨4410788870893008513196205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2940525913928672342130803 4410788870893008513196205)
        ·
          refine ⟨1654045826584878192448577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4410788870893008513196205 1654045826584878192448577)
          ·
            refine ⟨1240534369938658644336433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1654045826584878192448577 1240534369938658644336433)
            ·
              refine ⟨930400777453993983252325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240534369938658644336433 930400777453993983252325)
              ·
                refine ⟨174450145772623871859811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 930400777453993983252325 174450145772623871859811)
                ·
                  refine ⟨261675218658935807789717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174450145772623871859811 261675218658935807789717)
                  ·
                    refine ⟨12266025874637615990143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 261675218658935807789717 12266025874637615990143)
                    ·
                      rfl

theorem cell23_71664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_71664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71664 prefixEnd_71664 := by exact prefixLift 71664
  have htrace : WordTrace (prefixWord ++ tailWord_71664) baseStart_71664 baseEnd_71664 := by
    simpa [prefixWord, tailWord_71664, baseEnd_71664] using wordTrace_append hprefix tailTrace_71664
  have hstable : (prefixWord ++ tailWord_71664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71664).length < 2 ^ (prefixWord ++ tailWord_71664).sum := by decide
  have hdescent : baseEnd_71664 < baseStart_71664 := by decide
  rcases family_descends (prefixWord ++ tailWord_71664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71681 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 4, 4]
def baseStart_71681 : Nat := 118140960795 + 71681 * 2 ^ 59
def prefixEnd_71681 : Nat := 4983230072969 + 3 ^ 40 * 71681 * 2
def baseEnd_71681 : Nat := 12268935598346427152617

theorem tailTrace_71681 : CollatzResearch.WordTrace tailWord_71681 prefixEnd_71681 12268935598346427152617 := by
  unfold tailWord_71681
  simp only [CollatzResearch.WordTrace]
  refine ⟨2614420853319453985262897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1742947235546302656841931 2614420853319453985262897)
  ·
    refine ⟨1960815639989590488947173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2614420853319453985262897 1960815639989590488947173)
    ·
      refine ⟨367652932498048216677595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1960815639989590488947173 367652932498048216677595)
      ·
        refine ⟨551479398747072325016393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367652932498048216677595 551479398747072325016393)
        ·
          refine ⟨413609549060304243762295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551479398747072325016393 413609549060304243762295)
          ·
            refine ⟨620414323590456365643443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413609549060304243762295 620414323590456365643443)
            ·
              refine ⟨930621485385684548465165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620414323590456365643443 930621485385684548465165)
              ·
                refine ⟨348983057019631705674437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 930621485385684548465165 348983057019631705674437)
                ·
                  refine ⟨65434323191180944813957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 348983057019631705674437 65434323191180944813957)
                  ·
                    refine ⟨12268935598346427152617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65434323191180944813957 12268935598346427152617)
                    ·
                      rfl

theorem cell23_71681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_71681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71681 prefixEnd_71681 := by exact prefixLift 71681
  have htrace : WordTrace (prefixWord ++ tailWord_71681) baseStart_71681 baseEnd_71681 := by
    simpa [prefixWord, tailWord_71681, baseEnd_71681] using wordTrace_append hprefix tailTrace_71681
  have hstable : (prefixWord ++ tailWord_71681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71681).length < 2 ^ (prefixWord ++ tailWord_71681).sum := by decide
  have hdescent : baseEnd_71681 < baseStart_71681 := by decide
  rcases family_descends (prefixWord ++ tailWord_71681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71691 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 3]
def baseStart_71691 : Nat := 118140960795 + 71691 * 2 ^ 59
def prefixEnd_71691 : Nat := 4983230072969 + 3 ^ 40 * 71691 * 2
def baseEnd_71691 : Nat := 36811941601584242332805

theorem tailTrace_71691 : CollatzResearch.WordTrace tailWord_71691 prefixEnd_71691 36811941601584242332805 := by
  unfold tailWord_71691
  simp only [CollatzResearch.WordTrace]
  refine ⟨2614785583283225693126927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1743190388855483795417951 2614785583283225693126927)
  ·
    refine ⟨3922178374924838539690391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2614785583283225693126927 3922178374924838539690391)
    ·
      refine ⟨5883267562387257809535587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3922178374924838539690391 5883267562387257809535587)
      ·
        refine ⟨8824901343580886714303381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5883267562387257809535587 8824901343580886714303381)
        ·
          refine ⟨413667250480354064732971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8824901343580886714303381 413667250480354064732971)
          ·
            refine ⟨620500875720531097099457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413667250480354064732971 620500875720531097099457)
            ·
              refine ⟨465375656790398322824593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620500875720531097099457 465375656790398322824593)
              ·
                refine ⟨349031742592798742118445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465375656790398322824593 349031742592798742118445)
                ·
                  refine ⟨130886903472299528294417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349031742592798742118445 130886903472299528294417)
                  ·
                    refine ⟨98165177604224646220813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 130886903472299528294417 98165177604224646220813)
                    ·
                      refine ⟨36811941601584242332805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 98165177604224646220813 36811941601584242332805)
                      ·
                        rfl

theorem cell23_71691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 3].length) (baseStart_71691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71691 prefixEnd_71691 := by exact prefixLift 71691
  have htrace : WordTrace (prefixWord ++ tailWord_71691) baseStart_71691 baseEnd_71691 := by
    simpa [prefixWord, tailWord_71691, baseEnd_71691] using wordTrace_append hprefix tailTrace_71691
  have hstable : (prefixWord ++ tailWord_71691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71691).length < 2 ^ (prefixWord ++ tailWord_71691).sum := by decide
  have hdescent : baseEnd_71691 < baseStart_71691 := by decide
  rcases family_descends (prefixWord ++ tailWord_71691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71708 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_71708 : Nat := 118140960795 + 71708 * 2 ^ 59
def prefixEnd_71708 : Nat := 4983230072969 + 3 ^ 40 * 71708 * 2
def baseEnd_71708 : Nat := 36820670772710675820227

theorem tailTrace_71708 : CollatzResearch.WordTrace tailWord_71708 prefixEnd_71708 36820670772710675820227 := by
  unfold tailWord_71708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1307702812110818798247889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1743603749481091730997185 1307702812110818798247889)
  ·
    refine ⟨980777109083114098685917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1307702812110818798247889 980777109083114098685917)
    ·
      refine ⟨367791415906167787007219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 980777109083114098685917 367791415906167787007219)
      ·
        refine ⟨551687123859251680510829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367791415906167787007219 551687123859251680510829)
        ·
          refine ⟨206882671447219380191561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 551687123859251680510829 206882671447219380191561)
          ·
            refine ⟨155162003585414535143671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206882671447219380191561 155162003585414535143671)
            ·
              refine ⟨232743005378121802715507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155162003585414535143671 232743005378121802715507)
              ·
                refine ⟨349114508067182704073261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232743005378121802715507 349114508067182704073261)
                ·
                  refine ⟨130917940525193514027473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 349114508067182704073261 130917940525193514027473)
                  ·
                    refine ⟨98188455393895135520605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 130917940525193514027473 98188455393895135520605)
                    ·
                      refine ⟨36820670772710675820227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 98188455393895135520605 36820670772710675820227)
                      ·
                        rfl

theorem cell23_71708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_71708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71708 prefixEnd_71708 := by exact prefixLift 71708
  have htrace : WordTrace (prefixWord ++ tailWord_71708) baseStart_71708 baseEnd_71708 := by
    simpa [prefixWord, tailWord_71708, baseEnd_71708] using wordTrace_append hprefix tailTrace_71708
  have hstable : (prefixWord ++ tailWord_71708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71708).length < 2 ^ (prefixWord ++ tailWord_71708).sum := by decide
  have hdescent : baseEnd_71708 < baseStart_71708 := by decide
  rcases family_descends (prefixWord ++ tailWord_71708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71732 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_71732 : Nat := 118140960795 + 71732 * 2 ^ 59
def prefixEnd_71732 : Nat := 4983230072969 + 3 ^ 40 * 71732 * 2
def baseEnd_71732 : Nat := 12277664769472860640039

theorem tailTrace_71732 : CollatzResearch.WordTrace tailWord_71732 prefixEnd_71732 12277664769472860640039 := by
  unfold tailWord_71732
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308140488067344847684725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1744187317423126463579633 1308140488067344847684725)
  ·
    refine ⟨122638170756313579470443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1308140488067344847684725 122638170756313579470443)
    ·
      refine ⟨183957256134470369205665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122638170756313579470443 183957256134470369205665)
      ·
        refine ⟨137967942100852776904249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183957256134470369205665 137967942100852776904249)
        ·
          refine ⟨103475956575639582678187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137967942100852776904249 103475956575639582678187)
          ·
            refine ⟨155213934863459374017281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103475956575639582678187 155213934863459374017281)
            ·
              refine ⟨116410451147594530512961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155213934863459374017281 116410451147594530512961)
              ·
                refine ⟨87307838360695897884721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116410451147594530512961 87307838360695897884721)
                ·
                  refine ⟨65480878770521923413541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87307838360695897884721 65480878770521923413541)
                  ·
                    refine ⟨12277664769472860640039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65480878770521923413541 12277664769472860640039)
                    ·
                      rfl

theorem cell23_71732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_71732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71732 prefixEnd_71732 := by exact prefixLift 71732
  have htrace : WordTrace (prefixWord ++ tailWord_71732) baseStart_71732 baseEnd_71732 := by
    simpa [prefixWord, tailWord_71732, baseEnd_71732] using wordTrace_append hprefix tailTrace_71732
  have hstable : (prefixWord ++ tailWord_71732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71732).length < 2 ^ (prefixWord ++ tailWord_71732).sum := by decide
  have hdescent : baseEnd_71732 < baseStart_71732 := by decide
  rcases family_descends (prefixWord ++ tailWord_71732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71791 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 4]
def baseStart_71791 : Nat := 118140960795 + 71791 * 2 ^ 59
def prefixEnd_71791 : Nat := 4983230072969 + 3 ^ 40 * 71791 * 2
def baseEnd_71791 : Nat := 36863289667033851082345

theorem tailTrace_71791 : CollatzResearch.WordTrace tailWord_71791 prefixEnd_71791 36863289667033851082345 := by
  unfold tailWord_71791
  simp only [CollatzResearch.WordTrace]
  refine ⟨2618432882920942771767227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1745621921947295181178151 2618432882920942771767227)
  ·
    refine ⟨3927649324381414157650841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2618432882920942771767227 3927649324381414157650841)
    ·
      refine ⟨2945736993286060618238131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3927649324381414157650841 2945736993286060618238131)
      ·
        refine ⟨4418605489929090927357197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2945736993286060618238131 4418605489929090927357197)
        ·
          refine ⟨1656977058723409097758949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4418605489929090927357197 1656977058723409097758949)
          ·
            refine ⟨310683198510639205829803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1656977058723409097758949 310683198510639205829803)
            ·
              refine ⟨466024797765958808744705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310683198510639205829803 466024797765958808744705)
              ·
                refine ⟨349518598324469106558529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466024797765958808744705 349518598324469106558529)
                ·
                  refine ⟨262138948743351829918897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349518598324469106558529 262138948743351829918897)
                  ·
                    refine ⟨196604211557513872439173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 262138948743351829918897 196604211557513872439173)
                    ·
                      refine ⟨36863289667033851082345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 196604211557513872439173 36863289667033851082345)
                      ·
                        rfl

theorem cell23_71791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_71791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71791 prefixEnd_71791 := by exact prefixLift 71791
  have htrace : WordTrace (prefixWord ++ tailWord_71791) baseStart_71791 baseEnd_71791 := by
    simpa [prefixWord, tailWord_71791, baseEnd_71791] using wordTrace_append hprefix tailTrace_71791
  have hstable : (prefixWord ++ tailWord_71791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71791).length < 2 ^ (prefixWord ++ tailWord_71791).sum := by decide
  have hdescent : baseEnd_71791 < baseStart_71791 := by decide
  rcases family_descends (prefixWord ++ tailWord_71791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71801 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 7]
def baseStart_71801 : Nat := 118140960795 + 71801 * 2 ^ 59
def prefixEnd_71801 : Nat := 4983230072969 + 3 ^ 40 * 71801 * 2
def baseEnd_71801 : Nat := 4096491608175423550811

theorem tailTrace_71801 : CollatzResearch.WordTrace tailWord_71801 prefixEnd_71801 4096491608175423550811 := by
  unfold tailWord_71801
  simp only [CollatzResearch.WordTrace]
  refine ⟨2618797612884714479631257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1745865075256476319754171 2618797612884714479631257)
  ·
    refine ⟨1964098209663535859723443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2618797612884714479631257 1964098209663535859723443)
    ·
      refine ⟨2946147314495303789585165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1964098209663535859723443 2946147314495303789585165)
      ·
        refine ⟨1104805242935738921094437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2946147314495303789585165 1104805242935738921094437)
        ·
          refine ⟨207150983050451047705207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1104805242935738921094437 207150983050451047705207)
          ·
            refine ⟨310726474575676571557811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207150983050451047705207 310726474575676571557811)
            ·
              refine ⟨466089711863514857336717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310726474575676571557811 466089711863514857336717)
              ·
                refine ⟨174783641948818071501269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466089711863514857336717 174783641948818071501269)
                ·
                  refine ⟨4096491608175423550811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 174783641948818071501269 4096491608175423550811)
                  ·
                    rfl

theorem cell23_71801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 7].length) (baseStart_71801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71801 prefixEnd_71801 := by exact prefixLift 71801
  have htrace : WordTrace (prefixWord ++ tailWord_71801) baseStart_71801 baseEnd_71801 := by
    simpa [prefixWord, tailWord_71801, baseEnd_71801] using wordTrace_append hprefix tailTrace_71801
  have hstable : (prefixWord ++ tailWord_71801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71801).length < 2 ^ (prefixWord ++ tailWord_71801).sum := by decide
  have hdescent : baseEnd_71801 < baseStart_71801 := by decide
  rcases family_descends (prefixWord ++ tailWord_71801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71895 : List Nat := [1, 1, 3, 2, 1, 2, 1, 7, 1, 4]
def baseStart_71895 : Nat := 118140960795 + 71895 * 2 ^ 59
def prefixEnd_71895 : Nat := 4983230072969 + 3 ^ 40 * 71895 * 2
def baseEnd_71895 : Nat := 12305563885033814727289

theorem tailTrace_71895 : CollatzResearch.WordTrace tailWord_71895 prefixEnd_71895 12305563885033814727289 := by
  unfold tailWord_71895
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622226074544168533553139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1748150716362779022368759 2622226074544168533553139)
  ·
    refine ⟨3933339111816252800329709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2622226074544168533553139 3933339111816252800329709)
    ·
      refine ⟨1475002166931094800123641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3933339111816252800329709 1475002166931094800123641)
      ·
        refine ⟨1106251625198321100092731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1475002166931094800123641 1106251625198321100092731)
        ·
          refine ⟨1659377437797481650139097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106251625198321100092731 1659377437797481650139097)
          ·
            refine ⟨1244533078348111237604323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1659377437797481650139097 1244533078348111237604323)
            ·
              refine ⟨1866799617522166856406485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244533078348111237604323 1866799617522166856406485)
              ·
                refine ⟨43753116035675785697027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1866799617522166856406485 43753116035675785697027)
                ·
                  refine ⟨65629674053513678545541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43753116035675785697027 65629674053513678545541)
                  ·
                    refine ⟨12305563885033814727289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65629674053513678545541 12305563885033814727289)
                    ·
                      rfl

theorem cell23_71895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_71895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71895 prefixEnd_71895 := by exact prefixLift 71895
  have htrace : WordTrace (prefixWord ++ tailWord_71895) baseStart_71895 baseEnd_71895 := by
    simpa [prefixWord, tailWord_71895, baseEnd_71895] using wordTrace_append hprefix tailTrace_71895
  have hstable : (prefixWord ++ tailWord_71895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71895).length < 2 ^ (prefixWord ++ tailWord_71895).sum := by decide
  have hdescent : baseEnd_71895 < baseStart_71895 := by decide
  rcases family_descends (prefixWord ++ tailWord_71895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71912 : List Nat := [2, 1, 4, 1, 2, 3, 1, 4, 1, 4]
def baseStart_71912 : Nat := 118140960795 + 71912 * 2 ^ 59
def prefixEnd_71912 : Nat := 4983230072969 + 3 ^ 40 * 71912 * 2
def baseEnd_71912 : Nat := 12308473608742625889763

theorem tailTrace_71912 : CollatzResearch.WordTrace tailWord_71912 prefixEnd_71912 12308473608742625889763 := by
  unfold tailWord_71912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1311423057741290218460995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1748564076988386957947993 1311423057741290218460995)
  ·
    refine ⟨1967134586611935327691493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1311423057741290218460995 1967134586611935327691493)
    ·
      refine ⟨368837734989737873942155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1967134586611935327691493 368837734989737873942155)
      ·
        refine ⟨553256602484606810913233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368837734989737873942155 553256602484606810913233)
        ·
          refine ⟨414942451863455108184925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 553256602484606810913233 414942451863455108184925)
          ·
            refine ⟨155603419448795665569347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 414942451863455108184925 155603419448795665569347)
            ·
              refine ⟨233405129173193498354021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155603419448795665569347 233405129173193498354021)
              ·
                refine ⟨43763461719973780941379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233405129173193498354021 43763461719973780941379)
                ·
                  refine ⟨65645192579960671412069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43763461719973780941379 65645192579960671412069)
                  ·
                    refine ⟨12308473608742625889763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65645192579960671412069 12308473608742625889763)
                    ·
                      rfl

theorem cell23_71912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_71912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71912 prefixEnd_71912 := by exact prefixLift 71912
  have htrace : WordTrace (prefixWord ++ tailWord_71912) baseStart_71912 baseEnd_71912 := by
    simpa [prefixWord, tailWord_71912, baseEnd_71912] using wordTrace_append hprefix tailTrace_71912
  have hstable : (prefixWord ++ tailWord_71912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71912).length < 2 ^ (prefixWord ++ tailWord_71912).sum := by decide
  have hdescent : baseEnd_71912 < baseStart_71912 := by decide
  rcases family_descends (prefixWord ++ tailWord_71912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71918 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_71918 : Nat := 118140960795 + 71918 * 2 ^ 59
def prefixEnd_71918 : Nat := 4983230072969 + 3 ^ 40 * 71918 * 2
def baseEnd_71918 : Nat := 36928501710154854194261

theorem tailTrace_71918 : CollatzResearch.WordTrace tailWord_71918 prefixEnd_71918 36928501710154854194261 := by
  unfold tailWord_71918
  simp only [CollatzResearch.WordTrace]
  refine ⟨327883119182605432705051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1748709968973895641093605 327883119182605432705051)
  ·
    refine ⟨491824678773908149057577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 327883119182605432705051 491824678773908149057577)
    ·
      refine ⟨368868509080431111793183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 491824678773908149057577 368868509080431111793183)
      ·
        refine ⟨553302763620646667689775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 368868509080431111793183 553302763620646667689775)
        ·
          refine ⟨829954145430970001534663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553302763620646667689775 829954145430970001534663)
          ·
            refine ⟨1244931218146455002301995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829954145430970001534663 1244931218146455002301995)
            ·
              refine ⟨1867396827219682503452993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244931218146455002301995 1867396827219682503452993)
              ·
                refine ⟨1400547620414761877589745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1867396827219682503452993 1400547620414761877589745)
                ·
                  refine ⟨1050410715311071408192309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1400547620414761877589745 1050410715311071408192309)
                  ·
                    refine ⟨98476004560412944518029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1050410715311071408192309 98476004560412944518029)
                    ·
                      refine ⟨36928501710154854194261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 98476004560412944518029 36928501710154854194261)
                      ·
                        rfl

theorem cell23_71918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_71918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71918 prefixEnd_71918 := by exact prefixLift 71918
  have htrace : WordTrace (prefixWord ++ tailWord_71918) baseStart_71918 baseEnd_71918 := by
    simpa [prefixWord, tailWord_71918, baseEnd_71918] using wordTrace_append hprefix tailTrace_71918
  have hstable : (prefixWord ++ tailWord_71918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71918).length < 2 ^ (prefixWord ++ tailWord_71918).sum := by decide
  have hdescent : baseEnd_71918 < baseStart_71918 := by decide
  rcases family_descends (prefixWord ++ tailWord_71918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71935 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 3, 1, 3]
def baseStart_71935 : Nat := 118140960795 + 71935 * 2 ^ 59
def prefixEnd_71935 : Nat := 4983230072969 + 3 ^ 40 * 71935 * 2
def baseEnd_71935 : Nat := 36937230881281287681683

theorem tailTrace_71935 : CollatzResearch.WordTrace tailWord_71935 prefixEnd_71935 36937230881281287681683 := by
  unfold tailWord_71935
  simp only [CollatzResearch.WordTrace]
  refine ⟨2623684994399255365009259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1749123329599503576672839 2623684994399255365009259)
  ·
    refine ⟨3935527491598883047513889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2623684994399255365009259 3935527491598883047513889)
    ·
      refine ⟨2951645618699162285635417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3935527491598883047513889 2951645618699162285635417)
      ·
        refine ⟨2213734214024371714226563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2951645618699162285635417 2213734214024371714226563)
        ·
          refine ⟨3320601321036557571339845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2213734214024371714226563 3320601321036557571339845)
          ·
            refine ⟨622612747694354544626221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3320601321036557571339845 622612747694354544626221)
            ·
              refine ⟨233479780385382954234833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 622612747694354544626221 233479780385382954234833)
              ·
                refine ⟨175109835289037215676125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233479780385382954234833 175109835289037215676125)
                ·
                  refine ⟨65666188233388955878547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175109835289037215676125 65666188233388955878547)
                  ·
                    refine ⟨98499282350083433817821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65666188233388955878547 98499282350083433817821)
                    ·
                      refine ⟨36937230881281287681683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 98499282350083433817821 36937230881281287681683)
                      ·
                        rfl

theorem cell23_71935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_71935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71935 prefixEnd_71935 := by exact prefixLift 71935
  have htrace : WordTrace (prefixWord ++ tailWord_71935) baseStart_71935 baseEnd_71935 := by
    simpa [prefixWord, tailWord_71935, baseEnd_71935] using wordTrace_append hprefix tailTrace_71935
  have hstable : (prefixWord ++ tailWord_71935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71935).length < 2 ^ (prefixWord ++ tailWord_71935).sum := by decide
  have hdescent : baseEnd_71935 < baseStart_71935 := by decide
  rcases family_descends (prefixWord ++ tailWord_71935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71945 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 1, 5, 2]
def baseStart_71945 : Nat := 118140960795 + 71945 * 2 ^ 59
def prefixEnd_71945 : Nat := 4983230072969 + 3 ^ 40 * 71945 * 2
def baseEnd_71945 : Nat := 36942365687826248556637

theorem tailTrace_71945 : CollatzResearch.WordTrace tailWord_71945 prefixEnd_71945 36942365687826248556637 := by
  unfold tailWord_71945
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624049724363027072873289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1749366482908684715248859 2624049724363027072873289)
  ·
    refine ⟨1968037293272270304654967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2624049724363027072873289 1968037293272270304654967)
    ·
      refine ⟨2952055939908405456982451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1968037293272270304654967 2952055939908405456982451)
      ·
        refine ⟨4428083909862608185473677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2952055939908405456982451 4428083909862608185473677)
        ·
          refine ⟨1660531466198478069552629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4428083909862608185473677 1660531466198478069552629)
          ·
            refine ⟨155674824956107319020559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1660531466198478069552629 155674824956107319020559)
            ·
              refine ⟨233512237434160978530839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155674824956107319020559 233512237434160978530839)
              ·
                refine ⟨350268356151241467796259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233512237434160978530839 350268356151241467796259)
                ·
                  refine ⟨525402534226862201694389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350268356151241467796259 525402534226862201694389)
                  ·
                    refine ⟨49256487583768331408849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 525402534226862201694389 49256487583768331408849)
                    ·
                      refine ⟨36942365687826248556637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49256487583768331408849 36942365687826248556637)
                      ·
                        rfl

theorem cell23_71945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 5, 2].length) (baseStart_71945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71945 prefixEnd_71945 := by exact prefixLift 71945
  have htrace : WordTrace (prefixWord ++ tailWord_71945) baseStart_71945 baseEnd_71945 := by
    simpa [prefixWord, tailWord_71945, baseEnd_71945] using wordTrace_append hprefix tailTrace_71945
  have hstable : (prefixWord ++ tailWord_71945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71945).length < 2 ^ (prefixWord ++ tailWord_71945).sum := by decide
  have hdescent : baseEnd_71945 < baseStart_71945 := by decide
  rcases family_descends (prefixWord ++ tailWord_71945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71992 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 3, 2, 2]
def baseStart_71992 : Nat := 118140960795 + 71992 * 2 ^ 59
def prefixEnd_71992 : Nat := 4983230072969 + 3 ^ 40 * 71992 * 2
def baseEnd_71992 : Nat := 36966499278587564668921

theorem tailTrace_71992 : CollatzResearch.WordTrace tailWord_71992 prefixEnd_71992 36966499278587564668921 := by
  unfold tailWord_71992
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312881977596377049917115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1750509303461836066556153 1312881977596377049917115)
  ·
    refine ⟨1969322966394565574875673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1312881977596377049917115 1969322966394565574875673)
    ·
      refine ⟨1476992224795924181156755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1969322966394565574875673 1476992224795924181156755)
      ·
        refine ⟨2215488337193886271735133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476992224795924181156755 2215488337193886271735133)
        ·
          refine ⟨830808126447707351900675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2215488337193886271735133 830808126447707351900675)
          ·
            refine ⟨1246212189671561027851013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830808126447707351900675 1246212189671561027851013)
            ·
              refine ⟨233664785563417692722065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1246212189671561027851013 233664785563417692722065)
              ·
                refine ⟨175248589172563269541549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233664785563417692722065 175248589172563269541549)
                ·
                  refine ⟨65718220939711226078081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175248589172563269541549 65718220939711226078081)
                  ·
                    refine ⟨49288665704783419558561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65718220939711226078081 49288665704783419558561)
                    ·
                      refine ⟨36966499278587564668921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49288665704783419558561 36966499278587564668921)
                      ·
                        rfl

theorem cell23_71992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3, 2, 2].length) (baseStart_71992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_71992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_71992 prefixEnd_71992 := by exact prefixLift 71992
  have htrace : WordTrace (prefixWord ++ tailWord_71992) baseStart_71992 baseEnd_71992 := by
    simpa [prefixWord, tailWord_71992, baseEnd_71992] using wordTrace_append hprefix tailTrace_71992
  have hstable : (prefixWord ++ tailWord_71992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71992).length < 2 ^ (prefixWord ++ tailWord_71992).sum := by decide
  have hdescent : baseEnd_71992 < baseStart_71992 := by decide
  rcases family_descends (prefixWord ++ tailWord_71992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72095 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 4]
def baseStart_72095 : Nat := 118140960795 + 72095 * 2 ^ 59
def prefixEnd_72095 : Nat := 4983230072969 + 3 ^ 40 * 72095 * 2
def baseEnd_72095 : Nat := 37019387786000661680947

theorem tailTrace_72095 : CollatzResearch.WordTrace tailWord_72095 prefixEnd_72095 37019387786000661680947 := by
  unfold tailWord_72095
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629520673819602690833739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1753013782546401793889159 2629520673819602690833739)
  ·
    refine ⟨3944281010729404036250609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2629520673819602690833739 3944281010729404036250609)
    ·
      refine ⟨2958210758047053027187957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3944281010729404036250609 2958210758047053027187957)
      ·
        refine ⟨277332258566911221298871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2958210758047053027187957 277332258566911221298871)
        ·
          refine ⟨415998387850366831948307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277332258566911221298871 415998387850366831948307)
          ·
            refine ⟨623997581775550247922461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415998387850366831948307 623997581775550247922461)
            ·
              refine ⟨233999093165831342970923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 623997581775550247922461 233999093165831342970923)
              ·
                refine ⟨350998639748747014456385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233999093165831342970923 350998639748747014456385)
                ·
                  refine ⟨263248979811560260842289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350998639748747014456385 263248979811560260842289)
                  ·
                    refine ⟨197436734858670195631717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 263248979811560260842289 197436734858670195631717)
                    ·
                      refine ⟨37019387786000661680947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 197436734858670195631717 37019387786000661680947)
                      ·
                        rfl

theorem cell23_72095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_72095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72095 prefixEnd_72095 := by exact prefixLift 72095
  have htrace : WordTrace (prefixWord ++ tailWord_72095) baseStart_72095 baseEnd_72095 := by
    simpa [prefixWord, tailWord_72095, baseEnd_72095] using wordTrace_append hprefix tailTrace_72095
  have hstable : (prefixWord ++ tailWord_72095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72095).length < 2 ^ (prefixWord ++ tailWord_72095).sum := by decide
  have hdescent : baseEnd_72095 < baseStart_72095 := by decide
  rcases family_descends (prefixWord ++ tailWord_72095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72099 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 2, 2, 2]
def baseStart_72099 : Nat := 118140960795 + 72099 * 2 ^ 59
def prefixEnd_72099 : Nat := 4983230072969 + 3 ^ 40 * 72099 * 2
def baseEnd_72099 : Nat := 37021441708618646030929

theorem tailTrace_72099 : CollatzResearch.WordTrace tailWord_72099 prefixEnd_72099 37021441708618646030929 := by
  unfold tailWord_72099
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629666565805111373979351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1753111043870074249319567 2629666565805111373979351)
  ·
    refine ⟨3944499848707667060969027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2629666565805111373979351 3944499848707667060969027)
    ·
      refine ⟨5916749773061500591453541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3944499848707667060969027 5916749773061500591453541)
      ·
        refine ⟨1109390582449031360897539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5916749773061500591453541 1109390582449031360897539)
        ·
          refine ⟨1664085873673547041346309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109390582449031360897539 1664085873673547041346309)
          ·
            refine ⟨312016101313790070252433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1664085873673547041346309 312016101313790070252433)
            ·
              refine ⟨234012075985342552689325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312016101313790070252433 234012075985342552689325)
              ·
                refine ⟨87754528494503457258497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234012075985342552689325 87754528494503457258497)
                ·
                  refine ⟨65815896370877592943873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87754528494503457258497 65815896370877592943873)
                  ·
                    refine ⟨49361922278158194707905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65815896370877592943873 49361922278158194707905)
                    ·
                      refine ⟨37021441708618646030929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49361922278158194707905 37021441708618646030929)
                      ·
                        rfl

theorem cell23_72099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_72099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72099 prefixEnd_72099 := by exact prefixLift 72099
  have htrace : WordTrace (prefixWord ++ tailWord_72099) baseStart_72099 baseEnd_72099 := by
    simpa [prefixWord, tailWord_72099, baseEnd_72099] using wordTrace_append hprefix tailTrace_72099
  have hstable : (prefixWord ++ tailWord_72099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72099).length < 2 ^ (prefixWord ++ tailWord_72099).sum := by decide
  have hdescent : baseEnd_72099 < baseStart_72099 := by decide
  rcases family_descends (prefixWord ++ tailWord_72099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72195 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 6]
def baseStart_72195 : Nat := 118140960795 + 72195 * 2 ^ 59
def prefixEnd_72195 : Nat := 4983230072969 + 3 ^ 40 * 72195 * 2
def baseEnd_72195 : Nat := 4118970650161141158943

theorem tailTrace_72195 : CollatzResearch.WordTrace tailWord_72195 prefixEnd_72195 4118970650161141158943 := by
  unfold tailWord_72195
  simp only [CollatzResearch.WordTrace]
  refine ⟨2633167973457319769474039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1755445315638213179649359 2633167973457319769474039)
  ·
    refine ⟨3949751960185979654211059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2633167973457319769474039 3949751960185979654211059)
    ·
      refine ⟨5924627940278969481316589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3949751960185979654211059 5924627940278969481316589)
      ·
        refine ⟨2221735477604613555493721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5924627940278969481316589 2221735477604613555493721)
        ·
          refine ⟨1666301608203460166620291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2221735477604613555493721 1666301608203460166620291)
          ·
            refine ⟨2499452412305190249930437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666301608203460166620291 2499452412305190249930437)
            ·
              refine ⟨468647327307223171861957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2499452412305190249930437 468647327307223171861957)
              ·
                refine ⟨87871373870104344724117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 468647327307223171861957 87871373870104344724117)
                ·
                  refine ⟨4118970650161141158943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87871373870104344724117 4118970650161141158943)
                  ·
                    rfl

theorem cell23_72195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 6].length) (baseStart_72195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72195 prefixEnd_72195 := by exact prefixLift 72195
  have htrace : WordTrace (prefixWord ++ tailWord_72195) baseStart_72195 baseEnd_72195 := by
    simpa [prefixWord, tailWord_72195, baseEnd_72195] using wordTrace_append hprefix tailTrace_72195
  have hstable : (prefixWord ++ tailWord_72195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72195).length < 2 ^ (prefixWord ++ tailWord_72195).sum := by decide
  have hdescent : baseEnd_72195 < baseStart_72195 := by decide
  rcases family_descends (prefixWord ++ tailWord_72195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72242 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_72242 : Nat := 118140960795 + 72242 * 2 ^ 59
def prefixEnd_72242 : Nat := 4983230072969 + 3 ^ 40 * 72242 * 2
def baseEnd_72242 : Nat := 12364956480737195514257

theorem tailTrace_72242 : CollatzResearch.WordTrace tailWord_72242 prefixEnd_72242 12364956480737195514257 := by
  unfold tailWord_72242
  simp only [CollatzResearch.WordTrace]
  refine ⟨658720551071761699108745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1756588136191364530956653 658720551071761699108745)
  ·
    refine ⟨494040413303821274331559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 658720551071761699108745 494040413303821274331559)
    ·
      refine ⟨741060619955731911497339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494040413303821274331559 741060619955731911497339)
      ·
        refine ⟨1111590929933597867246009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741060619955731911497339 1111590929933597867246009)
        ·
          refine ⟨833693197450198400434507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1111590929933597867246009 833693197450198400434507)
          ·
            refine ⟨1250539796175297600651761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833693197450198400434507 1250539796175297600651761)
            ·
              refine ⟨937904847131473200488821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250539796175297600651761 937904847131473200488821)
              ·
                refine ⟨87928579418575612545827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 937904847131473200488821 87928579418575612545827)
                ·
                  refine ⟨131892869127863418818741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87928579418575612545827 131892869127863418818741)
                  ·
                    refine ⟨12364956480737195514257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 131892869127863418818741 12364956480737195514257)
                    ·
                      rfl

theorem cell23_72242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_72242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72242 prefixEnd_72242 := by exact prefixLift 72242
  have htrace : WordTrace (prefixWord ++ tailWord_72242) baseStart_72242 baseEnd_72242 := by
    simpa [prefixWord, tailWord_72242, baseEnd_72242] using wordTrace_append hprefix tailTrace_72242
  have hstable : (prefixWord ++ tailWord_72242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72242).length < 2 ^ (prefixWord ++ tailWord_72242).sum := by decide
  have hdescent : baseEnd_72242 < baseStart_72242 := by decide
  rcases family_descends (prefixWord ++ tailWord_72242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72249 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 2, 3, 2]
def baseStart_72249 : Nat := 118140960795 + 72249 * 2 ^ 59
def prefixEnd_72249 : Nat := 4983230072969 + 3 ^ 40 * 72249 * 2
def baseEnd_72249 : Nat := 37098463806793059155239

theorem tailTrace_72249 : CollatzResearch.WordTrace tailWord_72249 prefixEnd_72249 37098463806793059155239 := by
  unfold tailWord_72249
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635137515261686991939801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1756758343507791327959867 2635137515261686991939801)
  ·
    refine ⟨1976353136446265243954851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2635137515261686991939801 1976353136446265243954851)
    ·
      refine ⟨2964529704669397865932277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976353136446265243954851 2964529704669397865932277)
      ·
        refine ⟨277924659812756049931151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2964529704669397865932277 277924659812756049931151)
        ·
          refine ⟨416886989719134074896727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277924659812756049931151 416886989719134074896727)
          ·
            refine ⟨625330484578701112345091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416886989719134074896727 625330484578701112345091)
            ·
              refine ⟨937995726868051668517637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625330484578701112345091 937995726868051668517637)
              ·
                refine ⟨175874198787759687847057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 937995726868051668517637 175874198787759687847057)
                ·
                  refine ⟨131905649090819765885293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175874198787759687847057 131905649090819765885293)
                  ·
                    refine ⟨49464618409057412206985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131905649090819765885293 49464618409057412206985)
                    ·
                      refine ⟨37098463806793059155239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49464618409057412206985 37098463806793059155239)
                      ·
                        rfl

theorem cell23_72249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_72249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72249 prefixEnd_72249 := by exact prefixLift 72249
  have htrace : WordTrace (prefixWord ++ tailWord_72249) baseStart_72249 baseEnd_72249 := by
    simpa [prefixWord, tailWord_72249, baseEnd_72249] using wordTrace_append hprefix tailTrace_72249
  have hstable : (prefixWord ++ tailWord_72249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72249).length < 2 ^ (prefixWord ++ tailWord_72249).sum := by decide
  have hdescent : baseEnd_72249 < baseStart_72249 := by decide
  rcases family_descends (prefixWord ++ tailWord_72249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72255 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 3, 6]
def baseStart_72255 : Nat := 118140960795 + 72255 * 2 ^ 59
def prefixEnd_72255 : Nat := 4983230072969 + 3 ^ 40 * 72255 * 2
def baseEnd_72255 : Nat := 12367181563573345226737

theorem tailTrace_72255 : CollatzResearch.WordTrace tailWord_72255 prefixEnd_72255 12367181563573345226737 := by
  unfold tailWord_72255
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635356353239950016658219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1756904235493300011105479 2635356353239950016658219)
  ·
    refine ⟨3953034529859925024987329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2635356353239950016658219 3953034529859925024987329)
    ·
      refine ⟨2964775897394943768740497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3953034529859925024987329 2964775897394943768740497)
      ·
        refine ⟨2223581923046207826555373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2964775897394943768740497 2223581923046207826555373)
        ·
          refine ⟨833843221142327934958265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2223581923046207826555373 833843221142327934958265)
          ·
            refine ⟨625382415856745951218699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 833843221142327934958265 625382415856745951218699)
            ·
              refine ⟨938073623785118926828049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625382415856745951218699 938073623785118926828049)
              ·
                refine ⟨703555217838839195121037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 938073623785118926828049 703555217838839195121037)
                ·
                  refine ⟨263833206689564698170389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 703555217838839195121037 263833206689564698170389)
                  ·
                    refine ⟨12367181563573345226737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 263833206689564698170389 12367181563573345226737)
                    ·
                      rfl

theorem cell23_72255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_72255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72255 prefixEnd_72255 := by exact prefixLift 72255
  have htrace : WordTrace (prefixWord ++ tailWord_72255) baseStart_72255 baseEnd_72255 := by
    simpa [prefixWord, tailWord_72255, baseEnd_72255] using wordTrace_append hprefix tailTrace_72255
  have hstable : (prefixWord ++ tailWord_72255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72255).length < 2 ^ (prefixWord ++ tailWord_72255).sum := by decide
  have hdescent : baseEnd_72255 < baseStart_72255 := by decide
  rcases family_descends (prefixWord ++ tailWord_72255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72292 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_72292 : Nat := 118140960795 + 72292 * 2 ^ 59
def prefixEnd_72292 : Nat := 4983230072969 + 3 ^ 40 * 72292 * 2
def baseEnd_72292 : Nat := 37120543474936390917541

theorem tailTrace_72292 : CollatzResearch.WordTrace tailWord_72292 prefixEnd_72292 37120543474936390917541 := by
  unfold tailWord_72292
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318352927052952667877565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1757803902737270223836753 1318352927052952667877565)
  ·
    refine ⟨494382347644857250454087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1318352927052952667877565 494382347644857250454087)
    ·
      refine ⟨741573521467285875681131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494382347644857250454087 741573521467285875681131)
      ·
        refine ⟨1112360282200928813521697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741573521467285875681131 1112360282200928813521697)
        ·
          refine ⟨834270211650696610141273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1112360282200928813521697 834270211650696610141273)
          ·
            refine ⟨625702658738022457605955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834270211650696610141273 625702658738022457605955)
            ·
              refine ⟨938553988107033686408933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625702658738022457605955 938553988107033686408933)
              ·
                refine ⟨175978872770068816201675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 938553988107033686408933 175978872770068816201675)
                ·
                  refine ⟨263968309155103224302513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175978872770068816201675 263968309155103224302513)
                  ·
                    refine ⟨197976231866327418226885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 263968309155103224302513 197976231866327418226885)
                    ·
                      refine ⟨37120543474936390917541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 197976231866327418226885 37120543474936390917541)
                      ·
                        rfl

theorem cell23_72292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_72292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72292 prefixEnd_72292 := by exact prefixLift 72292
  have htrace : WordTrace (prefixWord ++ tailWord_72292) baseStart_72292 baseEnd_72292 := by
    simpa [prefixWord, tailWord_72292, baseEnd_72292] using wordTrace_append hprefix tailTrace_72292
  have hstable : (prefixWord ++ tailWord_72292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72292).length < 2 ^ (prefixWord ++ tailWord_72292).sum := by decide
  have hdescent : baseEnd_72292 < baseStart_72292 := by decide
  rcases family_descends (prefixWord ++ tailWord_72292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72293 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 1, 5]
def baseStart_72293 : Nat := 118140960795 + 72293 * 2 ^ 59
def prefixEnd_72293 : Nat := 4983230072969 + 3 ^ 40 * 72293 * 2
def baseEnd_72293 : Nat := 12373685651863629001679

theorem tailTrace_72293 : CollatzResearch.WordTrace tailWord_72293 prefixEnd_72293 12373685651863629001679 := by
  unfold tailWord_72293
  simp only [CollatzResearch.WordTrace]
  refine ⟨2636742327102282506541533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1757828218068188337694355 2636742327102282506541533)
  ·
    refine ⟨988778372663355939953075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2636742327102282506541533 988778372663355939953075)
    ·
      refine ⟨1483167558995033909929613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988778372663355939953075 1483167558995033909929613)
      ·
        refine ⟨556187834623137716223605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1483167558995033909929613 556187834623137716223605)
        ·
          refine ⟨52142609495919160895963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 556187834623137716223605 52142609495919160895963)
          ·
            refine ⟨78213914243878741343945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52142609495919160895963 78213914243878741343945)
            ·
              refine ⟨58660435682909056007959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78213914243878741343945 58660435682909056007959)
              ·
                refine ⟨87990653524363584011939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58660435682909056007959 87990653524363584011939)
                ·
                  refine ⟨131985980286545376017909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87990653524363584011939 131985980286545376017909)
                  ·
                    refine ⟨12373685651863629001679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 131985980286545376017909 12373685651863629001679)
                    ·
                      rfl

theorem cell23_72293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_72293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72293 prefixEnd_72293 := by exact prefixLift 72293
  have htrace : WordTrace (prefixWord ++ tailWord_72293) baseStart_72293 baseEnd_72293 := by
    simpa [prefixWord, tailWord_72293, baseEnd_72293] using wordTrace_append hprefix tailTrace_72293
  have hstable : (prefixWord ++ tailWord_72293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72293).length < 2 ^ (prefixWord ++ tailWord_72293).sum := by decide
  have hdescent : baseEnd_72293 < baseStart_72293 := by decide
  rcases family_descends (prefixWord ++ tailWord_72293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72296 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_72296 : Nat := 118140960795 + 72296 * 2 ^ 59
def prefixEnd_72296 : Nat := 4983230072969 + 3 ^ 40 * 72296 * 2
def baseEnd_72296 : Nat := 37122597397554375267523

theorem tailTrace_72296 : CollatzResearch.WordTrace tailWord_72296 prefixEnd_72296 37122597397554375267523 := by
  unfold tailWord_72296
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318425873045707009450371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1757901164060942679267161 1318425873045707009450371)
  ·
    refine ⟨1977638809568560514175557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1318425873045707009450371 1977638809568560514175557)
    ·
      refine ⟨370807276794105096407917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1977638809568560514175557 370807276794105096407917)
      ·
        refine ⟨139052728797789411152969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 370807276794105096407917 139052728797789411152969)
        ·
          refine ⟨104289546598342058364727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139052728797789411152969 104289546598342058364727)
          ·
            refine ⟨156434319897513087547091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104289546598342058364727 156434319897513087547091)
            ·
              refine ⟨234651479846269631320637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156434319897513087547091 234651479846269631320637)
              ·
                refine ⟨87994304942351111745239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234651479846269631320637 87994304942351111745239)
                ·
                  refine ⟨131991457413526667617859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87994304942351111745239 131991457413526667617859)
                  ·
                    refine ⟨197987186120290001426789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 131991457413526667617859 197987186120290001426789)
                    ·
                      refine ⟨37122597397554375267523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 197987186120290001426789 37122597397554375267523)
                      ·
                        rfl

theorem cell23_72296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_72296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72296 prefixEnd_72296 := by exact prefixLift 72296
  have htrace : WordTrace (prefixWord ++ tailWord_72296) baseStart_72296 baseEnd_72296 := by
    simpa [prefixWord, tailWord_72296, baseEnd_72296] using wordTrace_append hprefix tailTrace_72296
  have hstable : (prefixWord ++ tailWord_72296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72296).length < 2 ^ (prefixWord ++ tailWord_72296).sum := by decide
  have hdescent : baseEnd_72296 < baseStart_72296 := by decide
  rcases family_descends (prefixWord ++ tailWord_72296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72302 : List Nat := [4, 1, 2, 2, 2, 2, 10]
def baseStart_72302 : Nat := 118140960795 + 72302 * 2 ^ 59
def prefixEnd_72302 : Nat := 4983230072969 + 3 ^ 40 * 72302 * 2
def baseEnd_72302 : Nat := 458341707178782120895

theorem tailTrace_72302 : CollatzResearch.WordTrace tailWord_72302 prefixEnd_72302 458341707178782120895 := by
  unfold tailWord_72302
  simp only [CollatzResearch.WordTrace]
  refine ⟨329633823008709630452395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1758047056046451362412773 329633823008709630452395)
  ·
    refine ⟨494450734513064445678593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 329633823008709630452395 494450734513064445678593)
    ·
      refine ⟨370838050884798334258945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 494450734513064445678593 370838050884798334258945)
      ·
        refine ⟨278128538163598750694209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370838050884798334258945 278128538163598750694209)
        ·
          refine ⟨208596403622699063020657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278128538163598750694209 208596403622699063020657)
          ·
            refine ⟨156447302717024297265493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208596403622699063020657 156447302717024297265493)
            ·
              refine ⟨458341707178782120895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 156447302717024297265493 458341707178782120895)
              ·
                rfl

theorem cell23_72302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 10].length) (baseStart_72302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72302 prefixEnd_72302 := by exact prefixLift 72302
  have htrace : WordTrace (prefixWord ++ tailWord_72302) baseStart_72302 baseEnd_72302 := by
    simpa [prefixWord, tailWord_72302, baseEnd_72302] using wordTrace_append hprefix tailTrace_72302
  have hstable : (prefixWord ++ tailWord_72302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72302).length < 2 ^ (prefixWord ++ tailWord_72302).sum := by decide
  have hdescent : baseEnd_72302 < baseStart_72302 := by decide
  rcases family_descends (prefixWord ++ tailWord_72302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72305 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_72305 : Nat := 118140960795 + 72305 * 2 ^ 59
def prefixEnd_72305 : Nat := 4983230072969 + 3 ^ 40 * 72305 * 2
def baseEnd_72305 : Nat := 37127218723444840054981

theorem tailTrace_72305 : CollatzResearch.WordTrace tailWord_72305 prefixEnd_72305 37127218723444840054981 := by
  unfold tailWord_72305
  simp only [CollatzResearch.WordTrace]
  refine ⟨2637180003058808555978369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1758120002039205703985579 2637180003058808555978369)
  ·
    refine ⟨1977885002294106416983777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2637180003058808555978369 1977885002294106416983777)
    ·
      refine ⟨1483413751720579812737833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1977885002294106416983777 1483413751720579812737833)
      ·
        refine ⟨1112560313790434859553375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1483413751720579812737833 1112560313790434859553375)
        ·
          refine ⟨1668840470685652289330063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112560313790434859553375 1668840470685652289330063)
          ·
            refine ⟨2503260706028478433995095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668840470685652289330063 2503260706028478433995095)
            ·
              refine ⟨3754891059042717650992643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503260706028478433995095 3754891059042717650992643)
              ·
                refine ⟨5632336588564076476488965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3754891059042717650992643 5632336588564076476488965)
                ·
                  refine ⟨1056063110355764339341681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5632336588564076476488965 1056063110355764339341681)
                  ·
                    refine ⟨792047332766823254506261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1056063110355764339341681 792047332766823254506261)
                    ·
                      refine ⟨37127218723444840054981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 792047332766823254506261 37127218723444840054981)
                      ·
                        rfl

theorem cell23_72305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_72305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72305 prefixEnd_72305 := by exact prefixLift 72305
  have htrace : WordTrace (prefixWord ++ tailWord_72305) baseStart_72305 baseEnd_72305 := by
    simpa [prefixWord, tailWord_72305, baseEnd_72305] using wordTrace_append hprefix tailTrace_72305
  have hstable : (prefixWord ++ tailWord_72305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72305).length < 2 ^ (prefixWord ++ tailWord_72305).sum := by decide
  have hdescent : baseEnd_72305 < baseStart_72305 := by decide
  rcases family_descends (prefixWord ++ tailWord_72305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72313 : List Nat := [1, 2, 1, 3, 3, 2, 2, 4, 1, 2, 2]
def baseStart_72313 : Nat := 118140960795 + 72313 * 2 ^ 59
def prefixEnd_72313 : Nat := 4983230072969 + 3 ^ 40 * 72313 * 2
def baseEnd_72313 : Nat := 37131326568680808754945

theorem tailTrace_72313 : CollatzResearch.WordTrace tailWord_72313 prefixEnd_72313 37131326568680808754945 := by
  unfold tailWord_72313
  simp only [CollatzResearch.WordTrace]
  refine ⟨2637471787029825922269593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1758314524686550614846395 2637471787029825922269593)
  ·
    refine ⟨1978103840272369441702195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2637471787029825922269593 1978103840272369441702195)
    ·
      refine ⟨2967155760408554162553293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1978103840272369441702195 2967155760408554162553293)
      ·
        refine ⟨1112683410153207810957485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2967155760408554162553293 1112683410153207810957485)
        ·
          refine ⟨417256278807452929109057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1112683410153207810957485 417256278807452929109057)
          ·
            refine ⟨312942209105589696831793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 417256278807452929109057 312942209105589696831793)
            ·
              refine ⟨234706656829192272623845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312942209105589696831793 234706656829192272623845)
              ·
                refine ⟨44007498155473551116971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234706656829192272623845 44007498155473551116971)
                ·
                  refine ⟨66011247233210326675457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44007498155473551116971 66011247233210326675457)
                  ·
                    refine ⟨49508435424907745006593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66011247233210326675457 49508435424907745006593)
                    ·
                      refine ⟨37131326568680808754945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49508435424907745006593 37131326568680808754945)
                      ·
                        rfl

theorem cell23_72313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_72313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72313 prefixEnd_72313 := by exact prefixLift 72313
  have htrace : WordTrace (prefixWord ++ tailWord_72313) baseStart_72313 baseEnd_72313 := by
    simpa [prefixWord, tailWord_72313, baseEnd_72313] using wordTrace_append hprefix tailTrace_72313
  have hstable : (prefixWord ++ tailWord_72313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72313).length < 2 ^ (prefixWord ++ tailWord_72313).sum := by decide
  have hdescent : baseEnd_72313 < baseStart_72313 := by decide
  rcases family_descends (prefixWord ++ tailWord_72313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72315 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 2, 7]
def baseStart_72315 : Nat := 118140960795 + 72315 * 2 ^ 59
def prefixEnd_72315 : Nat := 4983230072969 + 3 ^ 40 * 72315 * 2
def baseEnd_72315 : Nat := 12377451176663266976645

theorem tailTrace_72315 : CollatzResearch.WordTrace tailWord_72315 prefixEnd_72315 12377451176663266976645 := by
  unfold tailWord_72315
  simp only [CollatzResearch.WordTrace]
  refine ⟨2637544733022580263842399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1758363155348386842561599 2637544733022580263842399)
  ·
    refine ⟨3956317099533870395763599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2637544733022580263842399 3956317099533870395763599)
    ·
      refine ⟨5934475649300805593645399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3956317099533870395763599 5934475649300805593645399)
      ·
        refine ⟨8901713473951208390468099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5934475649300805593645399 8901713473951208390468099)
        ·
          refine ⟨13352570210926812585702149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8901713473951208390468099 13352570210926812585702149)
          ·
            refine ⟨2503606914548777359819153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13352570210926812585702149 2503606914548777359819153)
            ·
              refine ⟨1877705185911583019864365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503606914548777359819153 1877705185911583019864365)
              ·
                refine ⟨704139444716843632449137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1877705185911583019864365 704139444716843632449137)
                ·
                  refine ⟨528104583537632724336853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 704139444716843632449137 528104583537632724336853)
                  ·
                    refine ⟨12377451176663266976645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 528104583537632724336853 12377451176663266976645)
                    ·
                      rfl

theorem cell23_72315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 7].length) (baseStart_72315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72315 prefixEnd_72315 := by exact prefixLift 72315
  have htrace : WordTrace (prefixWord ++ tailWord_72315) baseStart_72315 baseEnd_72315 := by
    simpa [prefixWord, tailWord_72315, baseEnd_72315] using wordTrace_append hprefix tailTrace_72315
  have hstable : (prefixWord ++ tailWord_72315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72315).length < 2 ^ (prefixWord ++ tailWord_72315).sum := by decide
  have hdescent : baseEnd_72315 < baseStart_72315 := by decide
  rcases family_descends (prefixWord ++ tailWord_72315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72356 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 1, 3, 2]
def baseStart_72356 : Nat := 118140960795 + 72356 * 2 ^ 59
def prefixEnd_72356 : Nat := 4983230072969 + 3 ^ 40 * 72356 * 2
def baseEnd_72356 : Nat := 37153406236824140517247

theorem tailTrace_72356 : CollatzResearch.WordTrace tailWord_72356 prefixEnd_72356 37153406236824140517247 := by
  unfold tailWord_72356
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319520062937022133042461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1759360083916029510723281 1319520062937022133042461)
  ·
    refine ⟨494820023601383299890923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1319520062937022133042461 494820023601383299890923)
    ·
      refine ⟨742230035402074949836385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494820023601383299890923 742230035402074949836385)
      ·
        refine ⟨556672526551556212377289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 742230035402074949836385 556672526551556212377289)
        ·
          refine ⟨417504394913667159282967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 556672526551556212377289 417504394913667159282967)
          ·
            refine ⟨626256592370500738924451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417504394913667159282967 626256592370500738924451)
            ·
              refine ⟨939384888555751108386677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626256592370500738924451 939384888555751108386677)
              ·
                refine ⟨88067333302101666411251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 939384888555751108386677 88067333302101666411251)
                ·
                  refine ⟨132100999953152499616877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88067333302101666411251 132100999953152499616877)
                  ·
                    refine ⟨49537874982432187356329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132100999953152499616877 49537874982432187356329)
                    ·
                      refine ⟨37153406236824140517247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49537874982432187356329 37153406236824140517247)
                      ·
                        rfl

theorem cell23_72356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_72356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72356 prefixEnd_72356 := by exact prefixLift 72356
  have htrace : WordTrace (prefixWord ++ tailWord_72356) baseStart_72356 baseEnd_72356 := by
    simpa [prefixWord, tailWord_72356, baseEnd_72356] using wordTrace_append hprefix tailTrace_72356
  have hstable : (prefixWord ++ tailWord_72356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72356).length < 2 ^ (prefixWord ++ tailWord_72356).sum := by decide
  have hdescent : baseEnd_72356 < baseStart_72356 := by decide
  rcases family_descends (prefixWord ++ tailWord_72356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72409 : List Nat := [1, 2, 1, 2, 3, 2, 2, 5, 5]
def baseStart_72409 : Nat := 118140960795 + 72409 * 2 ^ 59
def prefixEnd_72409 : Nat := 4983230072969 + 3 ^ 40 * 72409 * 2
def baseEnd_72409 : Nat := 4131180079056937017167

theorem tailTrace_72409 : CollatzResearch.WordTrace tailWord_72409 prefixEnd_72409 4131180079056937017167 := by
  unfold tailWord_72409
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640973194682034317764281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1760648796454689545176187 2640973194682034317764281)
  ·
    refine ⟨1980729896011525738323211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2640973194682034317764281 1980729896011525738323211)
    ·
      refine ⟨2971094844017288607484817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1980729896011525738323211 2971094844017288607484817)
      ·
        refine ⟨2228321133012966455613613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2971094844017288607484817 2228321133012966455613613)
        ·
          refine ⟨835620424879862420855105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2228321133012966455613613 835620424879862420855105)
          ·
            refine ⟨626715318659896815641329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835620424879862420855105 626715318659896815641329)
            ·
              refine ⟨470036488994922611730997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626715318659896815641329 470036488994922611730997)
              ·
                refine ⟨44065920843273994849781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 470036488994922611730997 44065920843273994849781)
                ·
                  refine ⟨4131180079056937017167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44065920843273994849781 4131180079056937017167)
                  ·
                    rfl

theorem cell23_72409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 5].length) (baseStart_72409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72409 prefixEnd_72409 := by exact prefixLift 72409
  have htrace : WordTrace (prefixWord ++ tailWord_72409) baseStart_72409 baseEnd_72409 := by
    simpa [prefixWord, tailWord_72409, baseEnd_72409] using wordTrace_append hprefix tailTrace_72409
  have hstable : (prefixWord ++ tailWord_72409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72409).length < 2 ^ (prefixWord ++ tailWord_72409).sum := by decide
  have hdescent : baseEnd_72409 < baseStart_72409 := by decide
  rcases family_descends (prefixWord ++ tailWord_72409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72432 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 5]
def baseStart_72432 : Nat := 118140960795 + 72432 * 2 ^ 59
def prefixEnd_72432 : Nat := 4983230072969 + 3 ^ 40 * 72432 * 2
def baseEnd_72432 : Nat := 37192430766565843166897

theorem tailTrace_72432 : CollatzResearch.WordTrace tailWord_72432 prefixEnd_72432 37192430766565843166897 := by
  unfold tailWord_72432
  simp only [CollatzResearch.WordTrace]
  refine ⟨1320906036799354622925775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1761208049065806163901033 1320906036799354622925775)
  ·
    refine ⟨1981359055199031934388663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1320906036799354622925775 1981359055199031934388663)
    ·
      refine ⟨2972038582798547901582995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1981359055199031934388663 2972038582798547901582995)
      ·
        refine ⟨4458057874197821852374493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972038582798547901582995 4458057874197821852374493)
        ·
          refine ⟨1671771702824183194640435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4458057874197821852374493 1671771702824183194640435)
          ·
            refine ⟨2507657554236274791960653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671771702824183194640435 2507657554236274791960653)
            ·
              refine ⟨940371582838603046985245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2507657554236274791960653 940371582838603046985245)
              ·
                refine ⟨352639343564476142619467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 940371582838603046985245 352639343564476142619467)
                ·
                  refine ⟨528959015346714213929201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352639343564476142619467 528959015346714213929201)
                  ·
                    refine ⟨396719261510035660446901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 528959015346714213929201 396719261510035660446901)
                    ·
                      refine ⟨37192430766565843166897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 396719261510035660446901 37192430766565843166897)
                      ·
                        rfl

theorem cell23_72432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_72432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72432 prefixEnd_72432 := by exact prefixLift 72432
  have htrace : WordTrace (prefixWord ++ tailWord_72432) baseStart_72432 baseEnd_72432 := by
    simpa [prefixWord, tailWord_72432, baseEnd_72432] using wordTrace_append hprefix tailTrace_72432
  have hstable : (prefixWord ++ tailWord_72432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72432).length < 2 ^ (prefixWord ++ tailWord_72432).sum := by decide
  have hdescent : baseEnd_72432 < baseStart_72432 := by decide
  rcases family_descends (prefixWord ++ tailWord_72432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72437 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_72437 : Nat := 118140960795 + 72437 * 2 ^ 59
def prefixEnd_72437 : Nat := 4983230072969 + 3 ^ 40 * 72437 * 2
def baseEnd_72437 : Nat := 37194998169838323604375

theorem tailTrace_72437 : CollatzResearch.WordTrace tailWord_72437 prefixEnd_72437 37194998169838323604375 := by
  unfold tailWord_72437
  simp only [CollatzResearch.WordTrace]
  refine ⟨2641994438580595099783565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1761329625720396733189043 2641994438580595099783565)
  ·
    refine ⟨990747914467723162418837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2641994438580595099783565 990747914467723162418837)
    ·
      refine ⟨46441308490674523238383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 990747914467723162418837 46441308490674523238383)
      ·
        refine ⟨69661962736011784857575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46441308490674523238383 69661962736011784857575)
        ·
          refine ⟨104492944104017677286363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69661962736011784857575 104492944104017677286363)
          ·
            refine ⟨156739416156026515929545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104492944104017677286363 156739416156026515929545)
            ·
              refine ⟨117554562117019886947159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156739416156026515929545 117554562117019886947159)
              ·
                refine ⟨176331843175529830420739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117554562117019886947159 176331843175529830420739)
                ·
                  refine ⟨264497764763294745631109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176331843175529830420739 264497764763294745631109)
                  ·
                    refine ⟨49593330893117764805833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 264497764763294745631109 49593330893117764805833)
                    ·
                      refine ⟨37194998169838323604375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49593330893117764805833 37194998169838323604375)
                      ·
                        rfl

theorem cell23_72437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_72437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72437 prefixEnd_72437 := by exact prefixLift 72437
  have htrace : WordTrace (prefixWord ++ tailWord_72437) baseStart_72437 baseEnd_72437 := by
    simpa [prefixWord, tailWord_72437, baseEnd_72437] using wordTrace_append hprefix tailTrace_72437
  have hstable : (prefixWord ++ tailWord_72437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72437).length < 2 ^ (prefixWord ++ tailWord_72437).sum := by decide
  have hdescent : baseEnd_72437 < baseStart_72437 := by decide
  rcases family_descends (prefixWord ++ tailWord_72437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72456 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 2, 5]
def baseStart_72456 : Nat := 118140960795 + 72456 * 2 ^ 59
def prefixEnd_72456 : Nat := 4983230072969 + 3 ^ 40 * 72456 * 2
def baseEnd_72456 : Nat := 12401584767424583088929

theorem tailTrace_72456 : CollatzResearch.WordTrace tailWord_72456 prefixEnd_72456 12401584767424583088929 := by
  unfold tailWord_72456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1321343712755880672362611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1761791617007840896483481 1321343712755880672362611)
  ·
    refine ⟨1982015569133821008543917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1321343712755880672362611 1982015569133821008543917)
    ·
      refine ⟨743255838425182878203969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1982015569133821008543917 743255838425182878203969)
      ·
        refine ⟨557441878818887158652977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 743255838425182878203969 557441878818887158652977)
        ·
          refine ⟨418081409114165368989733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557441878818887158652977 418081409114165368989733)
          ·
            refine ⟨78390264208906006685575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 418081409114165368989733 78390264208906006685575)
            ·
              refine ⟨117585396313359010028363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78390264208906006685575 117585396313359010028363)
              ·
                refine ⟨176378094470038515042545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117585396313359010028363 176378094470038515042545)
                ·
                  refine ⟨132283570852528886281909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176378094470038515042545 132283570852528886281909)
                  ·
                    refine ⟨12401584767424583088929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 132283570852528886281909 12401584767424583088929)
                    ·
                      rfl

theorem cell23_72456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_72456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72456 prefixEnd_72456 := by exact prefixLift 72456
  have htrace : WordTrace (prefixWord ++ tailWord_72456) baseStart_72456 baseEnd_72456 := by
    simpa [prefixWord, tailWord_72456, baseEnd_72456] using wordTrace_append hprefix tailTrace_72456
  have hstable : (prefixWord ++ tailWord_72456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72456).length < 2 ^ (prefixWord ++ tailWord_72456).sum := by decide
  have hdescent : baseEnd_72456 < baseStart_72456 := by decide
  rcases family_descends (prefixWord ++ tailWord_72456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72459 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 3, 6, 2]
def baseStart_72459 : Nat := 118140960795 + 72459 * 2 ^ 59
def prefixEnd_72459 : Nat := 4983230072969 + 3 ^ 40 * 72459 * 2
def baseEnd_72459 : Nat := 37206294744237237529273

theorem tailTrace_72459 : CollatzResearch.WordTrace tailWord_72459 prefixEnd_72459 37206294744237237529273 := by
  unfold tailWord_72459
  simp only [CollatzResearch.WordTrace]
  refine ⟨2642796844500892857084431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1761864563000595238056287 2642796844500892857084431)
  ·
    refine ⟨3964195266751339285626647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2642796844500892857084431 3964195266751339285626647)
    ·
      refine ⟨5946292900127008928439971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3964195266751339285626647 5946292900127008928439971)
      ·
        refine ⟨8919439350190513392659957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5946292900127008928439971 8919439350190513392659957)
        ·
          refine ⟨836197439080360630561871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8919439350190513392659957 836197439080360630561871)
          ·
            refine ⟨1254296158620540945842807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836197439080360630561871 1254296158620540945842807)
            ·
              refine ⟨1881444237930811418764211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254296158620540945842807 1881444237930811418764211)
              ·
                refine ⟨2822166356896217128146317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881444237930811418764211 2822166356896217128146317)
                ·
                  refine ⟨1058312383836081423054869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2822166356896217128146317 1058312383836081423054869)
                  ·
                    refine ⟨49608392992316316705697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1058312383836081423054869 49608392992316316705697)
                    ·
                      refine ⟨37206294744237237529273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49608392992316316705697 37206294744237237529273)
                      ·
                        rfl

theorem cell23_72459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 6, 2].length) (baseStart_72459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72459 prefixEnd_72459 := by exact prefixLift 72459
  have htrace : WordTrace (prefixWord ++ tailWord_72459) baseStart_72459 baseEnd_72459 := by
    simpa [prefixWord, tailWord_72459, baseEnd_72459] using wordTrace_append hprefix tailTrace_72459
  have hstable : (prefixWord ++ tailWord_72459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72459).length < 2 ^ (prefixWord ++ tailWord_72459).sum := by decide
  have hdescent : baseEnd_72459 < baseStart_72459 := by decide
  rcases family_descends (prefixWord ++ tailWord_72459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72469 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 5, 4]
def baseStart_72469 : Nat := 118140960795 + 72469 * 2 ^ 59
def prefixEnd_72469 : Nat := 4983230072969 + 3 ^ 40 * 72469 * 2
def baseEnd_72469 : Nat := 12403809850260732801409

theorem tailTrace_72469 : CollatzResearch.WordTrace tailWord_72469 prefixEnd_72469 12403809850260732801409 := by
  unfold tailWord_72469
  simp only [CollatzResearch.WordTrace]
  refine ⟨2643161574464664564948461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1762107716309776376632307 2643161574464664564948461)
  ·
    refine ⟨991185590424249211855673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2643161574464664564948461 991185590424249211855673)
    ·
      refine ⟨743389192818186908891755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 991185590424249211855673 743389192818186908891755)
      ·
        refine ⟨1115083789227280363337633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743389192818186908891755 1115083789227280363337633)
        ·
          refine ⟨836312841920460272503225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1115083789227280363337633 836312841920460272503225)
          ·
            refine ⟨627234631440345204377419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 836312841920460272503225 627234631440345204377419)
            ·
              refine ⟨940851947160517806566129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627234631440345204377419 940851947160517806566129)
              ·
                refine ⟨705638960370388354924597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940851947160517806566129 705638960370388354924597)
                ·
                  refine ⟨66153652534723908274181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 705638960370388354924597 66153652534723908274181)
                  ·
                    refine ⟨12403809850260732801409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66153652534723908274181 12403809850260732801409)
                    ·
                      rfl

theorem cell23_72469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_72469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72469 prefixEnd_72469 := by exact prefixLift 72469
  have htrace : WordTrace (prefixWord ++ tailWord_72469) baseStart_72469 baseEnd_72469 := by
    simpa [prefixWord, tailWord_72469, baseEnd_72469] using wordTrace_append hprefix tailTrace_72469
  have hstable : (prefixWord ++ tailWord_72469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72469).length < 2 ^ (prefixWord ++ tailWord_72469).sum := by decide
  have hdescent : baseEnd_72469 < baseStart_72469 := by decide
  rcases family_descends (prefixWord ++ tailWord_72469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72476 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_72476 : Nat := 118140960795 + 72476 * 2 ^ 59
def prefixEnd_72476 : Nat := 4983230072969 + 3 ^ 40 * 72476 * 2
def baseEnd_72476 : Nat := 37215023915363671016695

theorem tailTrace_72476 : CollatzResearch.WordTrace tailWord_72476 prefixEnd_72476 37215023915363671016695 := by
  unfold tailWord_72476
  simp only [CollatzResearch.WordTrace]
  refine ⟨1321708442719652380226641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1762277923626203173635521 1321708442719652380226641)
  ·
    refine ⟨991281332039739285169981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1321708442719652380226641 991281332039739285169981)
    ·
      refine ⟨371730499514902231938743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 991281332039739285169981 371730499514902231938743)
      ·
        refine ⟨557595749272353347908115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371730499514902231938743 557595749272353347908115)
        ·
          refine ⟨836393623908530021862173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557595749272353347908115 836393623908530021862173)
          ·
            refine ⟨313647608965698758198315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 836393623908530021862173 313647608965698758198315)
            ·
              refine ⟨470471413448548137297473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313647608965698758198315 470471413448548137297473)
              ·
                refine ⟨352853560086411102973105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470471413448548137297473 352853560086411102973105)
                ·
                  refine ⟨264640170064808327229829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 352853560086411102973105 264640170064808327229829)
                  ·
                    refine ⟨49620031887151561355593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 264640170064808327229829 49620031887151561355593)
                    ·
                      refine ⟨37215023915363671016695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49620031887151561355593 37215023915363671016695)
                      ·
                        rfl

theorem cell23_72476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_72476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72476 prefixEnd_72476 := by exact prefixLift 72476
  have htrace : WordTrace (prefixWord ++ tailWord_72476) baseStart_72476 baseEnd_72476 := by
    simpa [prefixWord, tailWord_72476, baseEnd_72476] using wordTrace_append hprefix tailTrace_72476
  have hstable : (prefixWord ++ tailWord_72476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72476).length < 2 ^ (prefixWord ++ tailWord_72476).sum := by decide
  have hdescent : baseEnd_72476 < baseStart_72476 := by decide
  rcases family_descends (prefixWord ++ tailWord_72476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72512 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 2, 9]
def baseStart_72512 : Nat := 118140960795 + 72512 * 2 ^ 59
def prefixEnd_72512 : Nat := 4983230072969 + 3 ^ 40 * 72512 * 2
def baseEnd_72512 : Nat := 12411169739641843388843

theorem tailTrace_72512 : CollatzResearch.WordTrace tailWord_72512 prefixEnd_72512 12411169739641843388843 := by
  unfold tailWord_72512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322364956654441454381895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1763153275539255272509193 1322364956654441454381895)
  ·
    refine ⟨1983547434981662181572843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1322364956654441454381895 1983547434981662181572843)
    ·
      refine ⟨2975321152472493272359265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1983547434981662181572843 2975321152472493272359265)
      ·
        refine ⟨2231490864354369954269449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2975321152472493272359265 2231490864354369954269449)
        ·
          refine ⟨1673618148265777465702087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2231490864354369954269449 1673618148265777465702087)
          ·
            refine ⟨2510427222398666198553131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673618148265777465702087 2510427222398666198553131)
            ·
              refine ⟨3765640833597999297829697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510427222398666198553131 3765640833597999297829697)
              ·
                refine ⟨2824230625198499473372273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3765640833597999297829697 2824230625198499473372273)
                ·
                  refine ⟨2118172968898874605029205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2824230625198499473372273 2118172968898874605029205)
                  ·
                    refine ⟨12411169739641843388843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2118172968898874605029205 12411169739641843388843)
                    ·
                      rfl

theorem cell23_72512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_72512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72512 prefixEnd_72512 := by exact prefixLift 72512
  have htrace : WordTrace (prefixWord ++ tailWord_72512) baseStart_72512 baseEnd_72512 := by
    simpa [prefixWord, tailWord_72512, baseEnd_72512] using wordTrace_append hprefix tailTrace_72512
  have hstable : (prefixWord ++ tailWord_72512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72512).length < 2 ^ (prefixWord ++ tailWord_72512).sum := by decide
  have hdescent : baseEnd_72512 < baseStart_72512 := by decide
  rcases family_descends (prefixWord ++ tailWord_72512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72526 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_72526 : Nat := 118140960795 + 72526 * 2 ^ 59
def prefixEnd_72526 : Nat := 4983230072969 + 3 ^ 40 * 72526 * 2
def baseEnd_72526 : Nat := 37240697948088475391465

theorem tailTrace_72526 : CollatzResearch.WordTrace tailWord_72526 prefixEnd_72526 37240697948088475391465 := by
  unfold tailWord_72526
  simp only [CollatzResearch.WordTrace]
  refine ⟨330655066907270412471679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1763493690172108866515621 330655066907270412471679)
  ·
    refine ⟨495982600360905618707519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 330655066907270412471679 495982600360905618707519)
    ·
      refine ⟨743973900541358428061279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495982600360905618707519 743973900541358428061279)
      ·
        refine ⟨1115960850812037642091919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743973900541358428061279 1115960850812037642091919)
        ·
          refine ⟨1673941276218056463137879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115960850812037642091919 1673941276218056463137879)
          ·
            refine ⟨2510911914327084694706819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673941276218056463137879 2510911914327084694706819)
            ·
              refine ⟨3766367871490627042060229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510911914327084694706819 3766367871490627042060229)
              ·
                refine ⟨706193975904492570386293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3766367871490627042060229 706193975904492570386293)
                ·
                  refine ⟨66205685241046178473715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 706193975904492570386293 66205685241046178473715)
                  ·
                    refine ⟨99308527861569267710573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66205685241046178473715 99308527861569267710573)
                    ·
                      refine ⟨37240697948088475391465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 99308527861569267710573 37240697948088475391465)
                      ·
                        rfl

theorem cell23_72526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_72526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72526 prefixEnd_72526 := by exact prefixLift 72526
  have htrace : WordTrace (prefixWord ++ tailWord_72526) baseStart_72526 baseEnd_72526 := by
    simpa [prefixWord, tailWord_72526, baseEnd_72526] using wordTrace_append hprefix tailTrace_72526
  have hstable : (prefixWord ++ tailWord_72526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72526).length < 2 ^ (prefixWord ++ tailWord_72526).sum := by decide
  have hdescent : baseEnd_72526 < baseStart_72526 := by decide
  rcases family_descends (prefixWord ++ tailWord_72526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72596 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_72596 : Nat := 118140960795 + 72596 * 2 ^ 59
def prefixEnd_72596 : Nat := 4983230072969 + 3 ^ 40 * 72596 * 2
def baseEnd_72596 : Nat := 37276641593903201516143

theorem tailTrace_72596 : CollatzResearch.WordTrace tailWord_72596 prefixEnd_72596 37276641593903201516143 := by
  unfold tailWord_72596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323896822502282627410821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1765195763336376836547761 1323896822502282627410821)
  ·
    refine ⟨248230654219177992639529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1323896822502282627410821 248230654219177992639529)
    ·
      refine ⟨186172990664383494479647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248230654219177992639529 186172990664383494479647)
      ·
        refine ⟨279259485996575241719471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186172990664383494479647 279259485996575241719471)
        ·
          refine ⟨418889228994862862579207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279259485996575241719471 418889228994862862579207)
          ·
            refine ⟨628333843492294293868811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418889228994862862579207 628333843492294293868811)
            ·
              refine ⟨942500765238441440803217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628333843492294293868811 942500765238441440803217)
              ·
                refine ⟨706875573928831080602413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942500765238441440803217 706875573928831080602413)
                ·
                  refine ⟨265078340223311655225905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 706875573928831080602413 265078340223311655225905)
                  ·
                    refine ⟨198808755167483741419429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 265078340223311655225905 198808755167483741419429)
                    ·
                      refine ⟨37276641593903201516143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 198808755167483741419429 37276641593903201516143)
                      ·
                        rfl

theorem cell23_72596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_72596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72596 prefixEnd_72596 := by exact prefixLift 72596
  have htrace : WordTrace (prefixWord ++ tailWord_72596) baseStart_72596 baseEnd_72596 := by
    simpa [prefixWord, tailWord_72596, baseEnd_72596] using wordTrace_append hprefix tailTrace_72596
  have hstable : (prefixWord ++ tailWord_72596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72596).length < 2 ^ (prefixWord ++ tailWord_72596).sum := by decide
  have hdescent : baseEnd_72596 < baseStart_72596 := by decide
  rcases family_descends (prefixWord ++ tailWord_72596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72637 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 1, 2, 3]
def baseStart_72637 : Nat := 118140960795 + 72637 * 2 ^ 59
def prefixEnd_72637 : Nat := 4983230072969 + 3 ^ 40 * 72637 * 2
def baseEnd_72637 : Nat := 37297694300737541103455

theorem tailTrace_72637 : CollatzResearch.WordTrace tailWord_72637 prefixEnd_72637 37297694300737541103455 := by
  unfold tailWord_72637
  simp only [CollatzResearch.WordTrace]
  refine ⟨2649289037856029257064165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1766192691904019504709443 2649289037856029257064165)
  ·
    refine ⟨496741694598005485699531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2649289037856029257064165 496741694598005485699531)
    ·
      refine ⟨745112541897008228549297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 496741694598005485699531 745112541897008228549297)
      ·
        refine ⟨558834406422756171411973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 745112541897008228549297 558834406422756171411973)
        ·
          refine ⟨104781451204266782139745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 558834406422756171411973 104781451204266782139745)
          ·
            refine ⟨78586088403200086604809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104781451204266782139745 78586088403200086604809)
            ·
              refine ⟨58939566302400064953607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78586088403200086604809 58939566302400064953607)
              ·
                refine ⟨88409349453600097430411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58939566302400064953607 88409349453600097430411)
                ·
                  refine ⟨132614024180400146145617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88409349453600097430411 132614024180400146145617)
                  ·
                    refine ⟨99460518135300109609213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 132614024180400146145617 99460518135300109609213)
                    ·
                      refine ⟨37297694300737541103455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 99460518135300109609213 37297694300737541103455)
                      ·
                        rfl

theorem cell23_72637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_72637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72637 prefixEnd_72637 := by exact prefixLift 72637
  have htrace : WordTrace (prefixWord ++ tailWord_72637) baseStart_72637 baseEnd_72637 := by
    simpa [prefixWord, tailWord_72637, baseEnd_72637] using wordTrace_append hprefix tailTrace_72637
  have hstable : (prefixWord ++ tailWord_72637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72637).length < 2 ^ (prefixWord ++ tailWord_72637).sum := by decide
  have hdescent : baseEnd_72637 < baseStart_72637 := by decide
  rcases family_descends (prefixWord ++ tailWord_72637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72639 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 4]
def baseStart_72639 : Nat := 118140960795 + 72639 * 2 ^ 59
def prefixEnd_72639 : Nat := 4983230072969 + 3 ^ 40 * 72639 * 2
def baseEnd_72639 : Nat := 37298721262046533278445

theorem tailTrace_72639 : CollatzResearch.WordTrace tailWord_72639 prefixEnd_72639 37298721262046533278445 := by
  unfold tailWord_72639
  simp only [CollatzResearch.WordTrace]
  refine ⟨2649361983848783598636971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1766241322565855732424647 2649361983848783598636971)
  ·
    refine ⟨3974042975773175397955457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2649361983848783598636971 3974042975773175397955457)
    ·
      refine ⟨2980532231829881548466593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3974042975773175397955457 2980532231829881548466593)
      ·
        refine ⟨2235399173872411161349945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2980532231829881548466593 2235399173872411161349945)
        ·
          refine ⟨1676549380404308371012459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2235399173872411161349945 1676549380404308371012459)
          ·
            refine ⟨2514824070606462556518689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676549380404308371012459 2514824070606462556518689)
            ·
              refine ⟨1886118052954846917389017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2514824070606462556518689 1886118052954846917389017)
              ·
                refine ⟨1414588539716135188041763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886118052954846917389017 1414588539716135188041763)
                ·
                  refine ⟨2121882809574202782062645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1414588539716135188041763 2121882809574202782062645)
                  ·
                    refine ⟨198926513397581510818373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2121882809574202782062645 198926513397581510818373)
                    ·
                      refine ⟨37298721262046533278445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 198926513397581510818373 37298721262046533278445)
                      ·
                        rfl

theorem cell23_72639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_72639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72639 prefixEnd_72639 := by exact prefixLift 72639
  have htrace : WordTrace (prefixWord ++ tailWord_72639) baseStart_72639 baseEnd_72639 := by
    simpa [prefixWord, tailWord_72639, baseEnd_72639] using wordTrace_append hprefix tailTrace_72639
  have hstable : (prefixWord ++ tailWord_72639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72639).length < 2 ^ (prefixWord ++ tailWord_72639).sum := by decide
  have hdescent : baseEnd_72639 < baseStart_72639 := by decide
  rcases family_descends (prefixWord ++ tailWord_72639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72643 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 1, 3, 2]
def baseStart_72643 : Nat := 118140960795 + 72643 * 2 ^ 59
def prefixEnd_72643 : Nat := 4983230072969 + 3 ^ 40 * 72643 * 2
def baseEnd_72643 : Nat := 37300775184664517628427

theorem tailTrace_72643 : CollatzResearch.WordTrace tailWord_72643 prefixEnd_72643 37300775184664517628427 := by
  unfold tailWord_72643
  simp only [CollatzResearch.WordTrace]
  refine ⟨2649507875834292281782583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1766338583889528187855055 2649507875834292281782583)
  ·
    refine ⟨3974261813751438422673875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2649507875834292281782583 3974261813751438422673875)
    ·
      refine ⟨5961392720627157634010813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3974261813751438422673875 5961392720627157634010813)
      ·
        refine ⟨2235522270235184112754055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5961392720627157634010813 2235522270235184112754055)
        ·
          refine ⟨3353283405352776169131083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2235522270235184112754055 3353283405352776169131083)
          ·
            refine ⟨5029925108029164253696625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3353283405352776169131083 5029925108029164253696625)
            ·
              refine ⟨3772443831021873190272469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5029925108029164253696625 3772443831021873190272469)
              ·
                refine ⟨88416652289575152897011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3772443831021873190272469 88416652289575152897011)
                ·
                  refine ⟨132624978434362729345517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88416652289575152897011 132624978434362729345517)
                  ·
                    refine ⟨49734366912886023504569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132624978434362729345517 49734366912886023504569)
                    ·
                      refine ⟨37300775184664517628427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49734366912886023504569 37300775184664517628427)
                      ·
                        rfl

theorem cell23_72643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 3, 2].length) (baseStart_72643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72643 prefixEnd_72643 := by exact prefixLift 72643
  have htrace : WordTrace (prefixWord ++ tailWord_72643) baseStart_72643 baseEnd_72643 := by
    simpa [prefixWord, tailWord_72643, baseEnd_72643] using wordTrace_append hprefix tailTrace_72643
  have hstable : (prefixWord ++ tailWord_72643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72643).length < 2 ^ (prefixWord ++ tailWord_72643).sum := by decide
  have hdescent : baseEnd_72643 < baseStart_72643 := by decide
  rcases family_descends (prefixWord ++ tailWord_72643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72644 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_72644 : Nat := 118140960795 + 72644 * 2 ^ 59
def prefixEnd_72644 : Nat := 4983230072969 + 3 ^ 40 * 72644 * 2
def baseEnd_72644 : Nat := 12433762888439671238641

theorem tailTrace_72644 : CollatzResearch.WordTrace tailWord_72644 prefixEnd_72644 12433762888439671238641 := by
  unfold tailWord_72644
  simp only [CollatzResearch.WordTrace]
  refine ⟨1324772174415334726284493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1766362899220446301712657 1324772174415334726284493)
  ·
    refine ⟨496789565405750522356685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1324772174415334726284493 496789565405750522356685)
    ·
      refine ⟨186296087027156445883757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 496789565405750522356685 186296087027156445883757)
      ·
        refine ⟨69861032635183667206409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186296087027156445883757 69861032635183667206409)
        ·
          refine ⟨52395774476387750404807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69861032635183667206409 52395774476387750404807)
          ·
            refine ⟨78593661714581625607211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52395774476387750404807 78593661714581625607211)
            ·
              refine ⟨117890492571872438410817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78593661714581625607211 117890492571872438410817)
              ·
                refine ⟨88417869428904328808113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117890492571872438410817 88417869428904328808113)
                ·
                  refine ⟨66313402071678246606085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88417869428904328808113 66313402071678246606085)
                  ·
                    refine ⟨12433762888439671238641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66313402071678246606085 12433762888439671238641)
                    ·
                      rfl

theorem cell23_72644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_72644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72644 prefixEnd_72644 := by exact prefixLift 72644
  have htrace : WordTrace (prefixWord ++ tailWord_72644) baseStart_72644 baseEnd_72644 := by
    simpa [prefixWord, tailWord_72644, baseEnd_72644] using wordTrace_append hprefix tailTrace_72644
  have hstable : (prefixWord ++ tailWord_72644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72644).length < 2 ^ (prefixWord ++ tailWord_72644).sum := by decide
  have hdescent : baseEnd_72644 < baseStart_72644 := by decide
  rcases family_descends (prefixWord ++ tailWord_72644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72666 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_72666 : Nat := 118140960795 + 72666 * 2 ^ 59
def prefixEnd_72666 : Nat := 4983230072969 + 3 ^ 40 * 72666 * 2
def baseEnd_72666 : Nat := 12437528413239309213607

theorem tailTrace_72666 : CollatzResearch.WordTrace tailWord_72666 prefixEnd_72666 12437528413239309213607 := by
  unfold tailWord_72666
  simp only [CollatzResearch.WordTrace]
  refine ⟨662586688687741802467463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1766897836500644806579901 662586688687741802467463)
  ·
    refine ⟨993880033031612703701195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662586688687741802467463 993880033031612703701195)
    ·
      refine ⟨1490820049547419055551793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993880033031612703701195 1490820049547419055551793)
      ·
        refine ⟨1118115037160564291663845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1490820049547419055551793 1118115037160564291663845)
        ·
          refine ⟨209646569467605804686971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1118115037160564291663845 209646569467605804686971)
          ·
            refine ⟨314469854201408707030457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209646569467605804686971 314469854201408707030457)
            ·
              refine ⟨235852390651056530272843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314469854201408707030457 235852390651056530272843)
              ·
                refine ⟨353778585976584795409265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235852390651056530272843 353778585976584795409265)
                ·
                  refine ⟨265333939482438596556949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353778585976584795409265 265333939482438596556949)
                  ·
                    refine ⟨12437528413239309213607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 265333939482438596556949 12437528413239309213607)
                    ·
                      rfl

theorem cell23_72666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_72666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72666 prefixEnd_72666 := by exact prefixLift 72666
  have htrace : WordTrace (prefixWord ++ tailWord_72666) baseStart_72666 baseEnd_72666 := by
    simpa [prefixWord, tailWord_72666, baseEnd_72666] using wordTrace_append hprefix tailTrace_72666
  have hstable : (prefixWord ++ tailWord_72666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72666).length < 2 ^ (prefixWord ++ tailWord_72666).sum := by decide
  have hdescent : baseEnd_72666 < baseStart_72666 := by decide
  rcases family_descends (prefixWord ++ tailWord_72666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72807 : List Nat := [1, 1, 5, 1, 1, 4, 2, 3, 1, 4]
def baseStart_72807 : Nat := 118140960795 + 72807 * 2 ^ 59
def prefixEnd_72807 : Nat := 4983230072969 + 3 ^ 40 * 72807 * 2
def baseEnd_72807 : Nat := 12461662004000625325891

theorem tailTrace_72807 : CollatzResearch.WordTrace tailWord_72807 prefixEnd_72807 12461662004000625325891 := by
  unfold tailWord_72807
  simp only [CollatzResearch.WordTrace]
  refine ⟨2655489447240148290752675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1770326298160098860501783 2655489447240148290752675)
  ·
    refine ⟨3983234170860222436129013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2655489447240148290752675 3983234170860222436129013)
    ·
      refine ⟨373428203518145853387095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3983234170860222436129013 373428203518145853387095)
      ·
        refine ⟨560142305277218780080643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373428203518145853387095 560142305277218780080643)
        ·
          refine ⟨840213457915828170120965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 560142305277218780080643 840213457915828170120965)
          ·
            refine ⟨157540023359217781897681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 840213457915828170120965 157540023359217781897681)
            ·
              refine ⟨118155017519413336423261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157540023359217781897681 118155017519413336423261)
              ·
                refine ⟨44308131569780001158723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118155017519413336423261 44308131569780001158723)
                ·
                  refine ⟨66462197354670001738085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44308131569780001158723 66462197354670001738085)
                  ·
                    refine ⟨12461662004000625325891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66462197354670001738085 12461662004000625325891)
                    ·
                      rfl

theorem cell23_72807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_72807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72807 prefixEnd_72807 := by exact prefixLift 72807
  have htrace : WordTrace (prefixWord ++ tailWord_72807) baseStart_72807 baseEnd_72807 := by
    simpa [prefixWord, tailWord_72807, baseEnd_72807] using wordTrace_append hprefix tailTrace_72807
  have hstable : (prefixWord ++ tailWord_72807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72807).length < 2 ^ (prefixWord ++ tailWord_72807).sum := by decide
  have hdescent : baseEnd_72807 < baseStart_72807 := by decide
  rcases family_descends (prefixWord ++ tailWord_72807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72850 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_72850 : Nat := 118140960795 + 72850 * 2 ^ 59
def prefixEnd_72850 : Nat := 4983230072969 + 3 ^ 40 * 72850 * 2
def baseEnd_72850 : Nat := 12469021893381735913325

theorem tailTrace_72850 : CollatzResearch.WordTrace tailWord_72850 prefixEnd_72850 12469021893381735913325 := by
  unfold tailWord_72850
  simp only [CollatzResearch.WordTrace]
  refine ⟨664264446521091658642001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1771371857389577756378669 664264446521091658642001)
  ·
    refine ⟨498198334890818743981501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 664264446521091658642001 498198334890818743981501)
    ·
      refine ⟨186824375584057028993063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 498198334890818743981501 186824375584057028993063)
      ·
        refine ⟨280236563376085543489595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186824375584057028993063 280236563376085543489595)
        ·
          refine ⟨420354845064128315234393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280236563376085543489595 420354845064128315234393)
          ·
            refine ⟨315266133798096236425795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 420354845064128315234393 315266133798096236425795)
            ·
              refine ⟨472899200697144354638693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315266133798096236425795 472899200697144354638693)
              ·
                refine ⟨88668600130714566494755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472899200697144354638693 88668600130714566494755)
                ·
                  refine ⟨133002900196071849742133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88668600130714566494755 133002900196071849742133)
                  ·
                    refine ⟨12469021893381735913325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 133002900196071849742133 12469021893381735913325)
                    ·
                      rfl

theorem cell23_72850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_72850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72850 prefixEnd_72850 := by exact prefixLift 72850
  have htrace : WordTrace (prefixWord ++ tailWord_72850) baseStart_72850 baseEnd_72850 := by
    simpa [prefixWord, tailWord_72850, baseEnd_72850] using wordTrace_append hprefix tailTrace_72850
  have hstable : (prefixWord ++ tailWord_72850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72850).length < 2 ^ (prefixWord ++ tailWord_72850).sum := by decide
  have hdescent : baseEnd_72850 < baseStart_72850 := by decide
  rcases family_descends (prefixWord ++ tailWord_72850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72874 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_72874 : Nat := 118140960795 + 72874 * 2 ^ 59
def prefixEnd_72874 : Nat := 4983230072969 + 3 ^ 40 * 72874 * 2
def baseEnd_72874 : Nat := 37419389215853113839865

theorem tailTrace_72874 : CollatzResearch.WordTrace tailWord_72874 prefixEnd_72874 37419389215853113839865 := by
  unfold tailWord_72874
  simp only [CollatzResearch.WordTrace]
  refine ⟨664483284499354683360419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1771955425331612488961117 664483284499354683360419)
  ·
    refine ⟨996724926749032025040629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 664483284499354683360419 996724926749032025040629)
    ·
      refine ⟨93442961882721752347559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 996724926749032025040629 93442961882721752347559)
      ·
        refine ⟨140164442824082628521339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93442961882721752347559 140164442824082628521339)
        ·
          refine ⟨210246664236123942782009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140164442824082628521339 210246664236123942782009)
          ·
            refine ⟨157684998177092957086507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210246664236123942782009 157684998177092957086507)
            ·
              refine ⟨236527497265639435629761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157684998177092957086507 236527497265639435629761)
              ·
                refine ⟨177395622949229576722321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236527497265639435629761 177395622949229576722321)
                ·
                  refine ⟨133046717211922182541741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177395622949229576722321 133046717211922182541741)
                  ·
                    refine ⟨49892518954470818453153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133046717211922182541741 49892518954470818453153)
                    ·
                      refine ⟨37419389215853113839865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49892518954470818453153 37419389215853113839865)
                      ·
                        rfl

theorem cell23_72874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_72874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72874 prefixEnd_72874 := by exact prefixLift 72874
  have htrace : WordTrace (prefixWord ++ tailWord_72874) baseStart_72874 baseEnd_72874 := by
    simpa [prefixWord, tailWord_72874, baseEnd_72874] using wordTrace_append hprefix tailTrace_72874
  have hstable : (prefixWord ++ tailWord_72874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72874).length < 2 ^ (prefixWord ++ tailWord_72874).sum := by decide
  have hdescent : baseEnd_72874 < baseStart_72874 := by decide
  rcases family_descends (prefixWord ++ tailWord_72874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72881 : List Nat := [1, 2, 2, 5, 1, 2, 3, 2, 1, 1, 3]
def baseStart_72881 : Nat := 118140960795 + 72881 * 2 ^ 59
def prefixEnd_72881 : Nat := 4983230072969 + 3 ^ 40 * 72881 * 2
def baseEnd_72881 : Nat := 37422983580434586452333

theorem tailTrace_72881 : CollatzResearch.WordTrace tailWord_72881 prefixEnd_72881 37422983580434586452333 := by
  unfold tailWord_72881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2658188448972058928946497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1772125632648039285964331 2658188448972058928946497)
  ·
    refine ⟨1993641336729044196709873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2658188448972058928946497 1993641336729044196709873)
    ·
      refine ⟨1495231002546783147532405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1993641336729044196709873 1495231002546783147532405)
      ·
        refine ⟨140177906488760920081163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1495231002546783147532405 140177906488760920081163)
        ·
          refine ⟨210266859733141380121745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140177906488760920081163 210266859733141380121745)
          ·
            refine ⟨157700144799856035091309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210266859733141380121745 157700144799856035091309)
            ·
              refine ⟨59137554299946013159241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157700144799856035091309 59137554299946013159241)
              ·
                refine ⟨44353165724959509869431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59137554299946013159241 44353165724959509869431)
                ·
                  refine ⟨66529748587439264804147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44353165724959509869431 66529748587439264804147)
                  ·
                    refine ⟨99794622881158897206221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66529748587439264804147 99794622881158897206221)
                    ·
                      refine ⟨37422983580434586452333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 99794622881158897206221 37422983580434586452333)
                      ·
                        rfl

theorem cell23_72881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_72881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72881 prefixEnd_72881 := by exact prefixLift 72881
  have htrace : WordTrace (prefixWord ++ tailWord_72881) baseStart_72881 baseEnd_72881 := by
    simpa [prefixWord, tailWord_72881, baseEnd_72881] using wordTrace_append hprefix tailTrace_72881
  have hstable : (prefixWord ++ tailWord_72881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72881).length < 2 ^ (prefixWord ++ tailWord_72881).sum := by decide
  have hdescent : baseEnd_72881 < baseStart_72881 := by decide
  rcases family_descends (prefixWord ++ tailWord_72881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72903 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_72903 : Nat := 118140960795 + 72903 * 2 ^ 59
def prefixEnd_72903 : Nat := 4983230072969 + 3 ^ 40 * 72903 * 2
def baseEnd_72903 : Nat := 37434280154833500377231

theorem tailTrace_72903 : CollatzResearch.WordTrace tailWord_72903 prefixEnd_72903 37434280154833500377231 := by
  unfold tailWord_72903
  simp only [CollatzResearch.WordTrace]
  refine ⟨2658990854892356686247363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1772660569928237790831575 2658990854892356686247363)
  ·
    refine ⟨3988486282338535029371045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2658990854892356686247363 3988486282338535029371045)
    ·
      refine ⟨747841177938475318007071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3988486282338535029371045 747841177938475318007071)
      ·
        refine ⟨1121761766907712977010607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 747841177938475318007071 1121761766907712977010607)
        ·
          refine ⟨1682642650361569465515911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1121761766907712977010607 1682642650361569465515911)
          ·
            refine ⟨2523963975542354198273867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682642650361569465515911 2523963975542354198273867)
            ·
              refine ⟨3785945963313531297410801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523963975542354198273867 3785945963313531297410801)
              ·
                refine ⟨2839459472485148473058101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3785945963313531297410801 2839459472485148473058101)
                ·
                  refine ⟨266199325545482669349197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2839459472485148473058101 266199325545482669349197)
                  ·
                    refine ⟨99824747079556001005949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 266199325545482669349197 99824747079556001005949)
                    ·
                      refine ⟨37434280154833500377231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 99824747079556001005949 37434280154833500377231)
                      ·
                        rfl

theorem cell23_72903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_72903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72903 prefixEnd_72903 := by exact prefixLift 72903
  have htrace : WordTrace (prefixWord ++ tailWord_72903) baseStart_72903 baseEnd_72903 := by
    simpa [prefixWord, tailWord_72903, baseEnd_72903] using wordTrace_append hprefix tailTrace_72903
  have hstable : (prefixWord ++ tailWord_72903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72903).length < 2 ^ (prefixWord ++ tailWord_72903).sum := by decide
  have hdescent : baseEnd_72903 < baseStart_72903 := by decide
  rcases family_descends (prefixWord ++ tailWord_72903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72938 : List Nat := [3, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_72938 : Nat := 118140960795 + 72938 * 2 ^ 59
def prefixEnd_72938 : Nat := 4983230072969 + 3 ^ 40 * 72938 * 2
def baseEnd_72938 : Nat := 37452251977740863439571

theorem tailTrace_72938 : CollatzResearch.WordTrace tailWord_72938 prefixEnd_72938 37452251977740863439571 := by
  unfold tailWord_72938
  simp only [CollatzResearch.WordTrace]
  refine ⟨665066852441389415942867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1773511606510371775847645 665066852441389415942867)
  ·
    refine ⟨997600278662084123914301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 665066852441389415942867 997600278662084123914301)
    ·
      refine ⟨374100104498281546467863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 997600278662084123914301 374100104498281546467863)
      ·
        refine ⟨561150156747422319701795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374100104498281546467863 561150156747422319701795)
        ·
          refine ⟨841725235121133479552693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561150156747422319701795 841725235121133479552693)
          ·
            refine ⟨78911740792606263708065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 841725235121133479552693 78911740792606263708065)
            ·
              refine ⟨59183805594454697781049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78911740792606263708065 59183805594454697781049)
              ·
                refine ⟨44387854195841023335787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59183805594454697781049 44387854195841023335787)
                ·
                  refine ⟨66581781293761535003681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44387854195841023335787 66581781293761535003681)
                  ·
                    refine ⟨49936335970321151252761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66581781293761535003681 49936335970321151252761)
                    ·
                      refine ⟨37452251977740863439571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49936335970321151252761 37452251977740863439571)
                      ·
                        rfl

theorem cell23_72938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_72938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72938 prefixEnd_72938 := by exact prefixLift 72938
  have htrace : WordTrace (prefixWord ++ tailWord_72938) baseStart_72938 baseEnd_72938 := by
    simpa [prefixWord, tailWord_72938, baseEnd_72938] using wordTrace_append hprefix tailTrace_72938
  have hstable : (prefixWord ++ tailWord_72938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72938).length < 2 ^ (prefixWord ++ tailWord_72938).sum := by decide
  have hdescent : baseEnd_72938 < baseStart_72938 := by decide
  rcases family_descends (prefixWord ++ tailWord_72938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72953 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 2, 6]
def baseStart_72953 : Nat := 118140960795 + 72953 * 2 ^ 59
def prefixEnd_72953 : Nat := 4983230072969 + 3 ^ 40 * 72953 * 2
def baseEnd_72953 : Nat := 12486651395852768250667

theorem tailTrace_72953 : CollatzResearch.WordTrace tailWord_72953 prefixEnd_72953 12486651395852768250667 := by
  unfold tailWord_72953
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660814504711215225567513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1773876336474143483711675 2660814504711215225567513)
  ·
    refine ⟨1995610878533411419175635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2660814504711215225567513 1995610878533411419175635)
    ·
      refine ⟨2993416317800117128763453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1995610878533411419175635 2993416317800117128763453)
      ·
        refine ⟨1122531119175043923286295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2993416317800117128763453 1122531119175043923286295)
        ·
          refine ⟨1683796678762565884929443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1122531119175043923286295 1683796678762565884929443)
          ·
            refine ⟨2525695018143848827394165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683796678762565884929443 2525695018143848827394165)
            ·
              refine ⟨236783907950985827568203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2525695018143848827394165 236783907950985827568203)
              ·
                refine ⟨355175861926478741352305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236783907950985827568203 355175861926478741352305)
                ·
                  refine ⟨266381896444859056014229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 355175861926478741352305 266381896444859056014229)
                  ·
                    refine ⟨12486651395852768250667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 266381896444859056014229 12486651395852768250667)
                    ·
                      rfl

theorem cell23_72953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_72953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72953 prefixEnd_72953 := by exact prefixLift 72953
  have htrace : WordTrace (prefixWord ++ tailWord_72953) baseStart_72953 baseEnd_72953 := by
    simpa [prefixWord, tailWord_72953, baseEnd_72953] using wordTrace_append hprefix tailTrace_72953
  have hstable : (prefixWord ++ tailWord_72953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72953).length < 2 ^ (prefixWord ++ tailWord_72953).sum := by decide
  have hdescent : baseEnd_72953 < baseStart_72953 := by decide
  rcases family_descends (prefixWord ++ tailWord_72953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72977 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 4, 2, 2]
def baseStart_72977 : Nat := 118140960795 + 72977 * 2 ^ 59
def prefixEnd_72977 : Nat := 4983230072969 + 3 ^ 40 * 72977 * 2
def baseEnd_72977 : Nat := 37472277723266210851891

theorem tailTrace_72977 : CollatzResearch.WordTrace tailWord_72977 prefixEnd_72977 37472277723266210851891 := by
  unfold tailWord_72977
  simp only [CollatzResearch.WordTrace]
  refine ⟨2661689856624267324441185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1774459904416178216294123 2661689856624267324441185)
  ·
    refine ⟨1996267392468200493330889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2661689856624267324441185 1996267392468200493330889)
    ·
      refine ⟨1497200544351150369998167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1996267392468200493330889 1497200544351150369998167)
      ·
        refine ⟨2245800816526725554997251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497200544351150369998167 2245800816526725554997251)
        ·
          refine ⟨3368701224790088332495877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2245800816526725554997251 3368701224790088332495877)
          ·
            refine ⟨631631479648141562342977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3368701224790088332495877 631631479648141562342977)
            ·
              refine ⟨473723609736106171757233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631631479648141562342977 473723609736106171757233)
              ·
                refine ⟨355292707302079628817925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 473723609736106171757233 355292707302079628817925)
                ·
                  refine ⟨66617382619139930403361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355292707302079628817925 66617382619139930403361)
                  ·
                    refine ⟨49963036964354947802521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66617382619139930403361 49963036964354947802521)
                    ·
                      refine ⟨37472277723266210851891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49963036964354947802521 37472277723266210851891)
                      ·
                        rfl

theorem cell23_72977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 2, 2].length) (baseStart_72977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72977 prefixEnd_72977 := by exact prefixLift 72977
  have htrace : WordTrace (prefixWord ++ tailWord_72977) baseStart_72977 baseEnd_72977 := by
    simpa [prefixWord, tailWord_72977, baseEnd_72977] using wordTrace_append hprefix tailTrace_72977
  have hstable : (prefixWord ++ tailWord_72977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72977).length < 2 ^ (prefixWord ++ tailWord_72977).sum := by decide
  have hdescent : baseEnd_72977 < baseStart_72977 := by decide
  rcases family_descends (prefixWord ++ tailWord_72977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72983 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 9]
def baseStart_72983 : Nat := 118140960795 + 72983 * 2 ^ 59
def prefixEnd_72983 : Nat := 4983230072969 + 3 ^ 40 * 72983 * 2
def baseEnd_72983 : Nat := 4163928734132576375207

theorem tailTrace_72983 : CollatzResearch.WordTrace tailWord_72983 prefixEnd_72983 4163928734132576375207 := by
  unfold tailWord_72983
  simp only [CollatzResearch.WordTrace]
  refine ⟨2661908694602530349159603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1774605796401686899439735 2661908694602530349159603)
  ·
    refine ⟨3992863041903795523739405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2661908694602530349159603 3992863041903795523739405)
    ·
      refine ⟨1497323640713923321402277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3992863041903795523739405 1497323640713923321402277)
      ·
        refine ⟨280748182633860622762927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1497323640713923321402277 280748182633860622762927)
        ·
          refine ⟨421122273950790934144391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280748182633860622762927 421122273950790934144391)
          ·
            refine ⟨631683410926186401216587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421122273950790934144391 631683410926186401216587)
            ·
              refine ⟨947525116389279601824881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631683410926186401216587 947525116389279601824881)
              ·
                refine ⟨710643837291959701368661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947525116389279601824881 710643837291959701368661)
                ·
                  refine ⟨4163928734132576375207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 710643837291959701368661 4163928734132576375207)
                  ·
                    rfl

theorem cell23_72983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 9].length) (baseStart_72983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_72983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_72983 prefixEnd_72983 := by exact prefixLift 72983
  have htrace : WordTrace (prefixWord ++ tailWord_72983) baseStart_72983 baseEnd_72983 := by
    simpa [prefixWord, tailWord_72983, baseEnd_72983] using wordTrace_append hprefix tailTrace_72983
  have hstable : (prefixWord ++ tailWord_72983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72983).length < 2 ^ (prefixWord ++ tailWord_72983).sum := by decide
  have hdescent : baseEnd_72983 < baseStart_72983 := by decide
  rcases family_descends (prefixWord ++ tailWord_72983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73000 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 7]
def baseStart_73000 : Nat := 118140960795 + 73000 * 2 ^ 59
def prefixEnd_73000 : Nat := 4983230072969 + 3 ^ 40 * 73000 * 2
def baseEnd_73000 : Nat := 4164898642035513429365

theorem tailTrace_73000 : CollatzResearch.WordTrace tailWord_73000 prefixEnd_73000 4164898642035513429365 := by
  unfold tailWord_73000
  simp only [CollatzResearch.WordTrace]
  refine ⟨1331264367770471126264227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1775019157027294835018969 1331264367770471126264227)
  ·
    refine ⟨1996896551655706689396341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1331264367770471126264227 1996896551655706689396341)
    ·
      refine ⟨187209051717722502130907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1996896551655706689396341 187209051717722502130907)
      ·
        refine ⟨280813577576583753196361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187209051717722502130907 280813577576583753196361)
        ·
          refine ⟨210610183182437814897271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280813577576583753196361 210610183182437814897271)
          ·
            refine ⟨315915274773656722345907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210610183182437814897271 315915274773656722345907)
            ·
              refine ⟨473872912160485083518861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315915274773656722345907 473872912160485083518861)
              ·
                refine ⟨177702342060181906319573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473872912160485083518861 177702342060181906319573)
                ·
                  refine ⟨4164898642035513429365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 177702342060181906319573 4164898642035513429365)
                  ·
                    rfl

theorem cell23_73000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 7].length) (baseStart_73000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73000 prefixEnd_73000 := by exact prefixLift 73000
  have htrace : WordTrace (prefixWord ++ tailWord_73000) baseStart_73000 baseEnd_73000 := by
    simpa [prefixWord, tailWord_73000, baseEnd_73000] using wordTrace_append hprefix tailTrace_73000
  have hstable : (prefixWord ++ tailWord_73000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73000).length < 2 ^ (prefixWord ++ tailWord_73000).sum := by decide
  have hdescent : baseEnd_73000 < baseStart_73000 := by decide
  rcases family_descends (prefixWord ++ tailWord_73000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73011 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 2, 2, 2]
def baseStart_73011 : Nat := 118140960795 + 73011 * 2 ^ 59
def prefixEnd_73011 : Nat := 4983230072969 + 3 ^ 40 * 73011 * 2
def baseEnd_73011 : Nat := 37489736065519077826735

theorem tailTrace_73011 : CollatzResearch.WordTrace tailWord_73011 prefixEnd_73011 37489736065519077826735 := by
  unfold tailWord_73011
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662929938501091131178887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1775286625667394087452591 2662929938501091131178887)
  ·
    refine ⟨3994394907751636696768331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2662929938501091131178887 3994394907751636696768331)
    ·
      refine ⟨5991592361627455045152497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3994394907751636696768331 5991592361627455045152497)
      ·
        refine ⟨4493694271220591283864373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5991592361627455045152497 4493694271220591283864373)
        ·
          refine ⟨421283837926930432862285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4493694271220591283864373 421283837926930432862285)
          ·
            refine ⟨157981439222598912323357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421283837926930432862285 157981439222598912323357)
            ·
              refine ⟨59243039708474592121259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157981439222598912323357 59243039708474592121259)
              ·
                refine ⟨88864559562711888181889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59243039708474592121259 88864559562711888181889)
                ·
                  refine ⟨66648419672033916136417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88864559562711888181889 66648419672033916136417)
                  ·
                    refine ⟨49986314754025437102313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66648419672033916136417 49986314754025437102313)
                    ·
                      refine ⟨37489736065519077826735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 49986314754025437102313 37489736065519077826735)
                      ·
                        rfl

theorem cell23_73011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 2, 2, 2].length) (baseStart_73011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73011 prefixEnd_73011 := by exact prefixLift 73011
  have htrace : WordTrace (prefixWord ++ tailWord_73011) baseStart_73011 baseEnd_73011 := by
    simpa [prefixWord, tailWord_73011, baseEnd_73011] using wordTrace_append hprefix tailTrace_73011
  have hstable : (prefixWord ++ tailWord_73011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73011).length < 2 ^ (prefixWord ++ tailWord_73011).sum := by decide
  have hdescent : baseEnd_73011 < baseStart_73011 := by decide
  rcases family_descends (prefixWord ++ tailWord_73011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73050 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_73050 : Nat := 118140960795 + 73050 * 2 ^ 59
def prefixEnd_73050 : Nat := 4983230072969 + 3 ^ 40 * 73050 * 2
def baseEnd_73050 : Nat := 37509761811044425239055

theorem tailTrace_73050 : CollatzResearch.WordTrace tailWord_73050 prefixEnd_73050 37509761811044425239055 := by
  unfold tailWord_73050
  simp only [CollatzResearch.WordTrace]
  refine ⟨666088096339950197962151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1776234923573200527899069 666088096339950197962151)
  ·
    refine ⟨999132144509925296943227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 666088096339950197962151 999132144509925296943227)
    ·
      refine ⟨1498698216764887945414841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 999132144509925296943227 1498698216764887945414841)
      ·
        refine ⟨1124023662573665959061131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1498698216764887945414841 1124023662573665959061131)
        ·
          refine ⟨1686035493860498938591697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124023662573665959061131 1686035493860498938591697)
          ·
            refine ⟨1264526620395374203943773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686035493860498938591697 1264526620395374203943773)
            ·
              refine ⟨474197482648265326478915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1264526620395374203943773 474197482648265326478915)
              ·
                refine ⟨711296223972397989718373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474197482648265326478915 711296223972397989718373)
                ·
                  refine ⟨133368041994824623072195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711296223972397989718373 133368041994824623072195)
                  ·
                    refine ⟨200052062992236934608293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133368041994824623072195 200052062992236934608293)
                    ·
                      refine ⟨37509761811044425239055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 200052062992236934608293 37509761811044425239055)
                      ·
                        rfl

theorem cell23_73050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_73050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73050 prefixEnd_73050 := by exact prefixLift 73050
  have htrace : WordTrace (prefixWord ++ tailWord_73050) baseStart_73050 baseEnd_73050 := by
    simpa [prefixWord, tailWord_73050, baseEnd_73050] using wordTrace_append hprefix tailTrace_73050
  have hstable : (prefixWord ++ tailWord_73050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73050).length < 2 ^ (prefixWord ++ tailWord_73050).sum := by decide
  have hdescent : baseEnd_73050 < baseStart_73050 := by decide
  rcases family_descends (prefixWord ++ tailWord_73050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73120 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 5, 5]
def baseStart_73120 : Nat := 118140960795 + 73120 * 2 ^ 59
def prefixEnd_73120 : Nat := 4983230072969 + 3 ^ 40 * 73120 * 2
def baseEnd_73120 : Nat := 12515235152286383787911

theorem tailTrace_73120 : CollatzResearch.WordTrace tailWord_73120 prefixEnd_73120 12515235152286383787911 := by
  unfold tailWord_73120
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333452747553101373448407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1777936996737468497931209 1333452747553101373448407)
  ·
    refine ⟨2000179121329652060172611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1333452747553101373448407 2000179121329652060172611)
    ·
      refine ⟨3000268681994478090258917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2000179121329652060172611 3000268681994478090258917)
      ·
        refine ⟨562550377873964641923547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3000268681994478090258917 562550377873964641923547)
        ·
          refine ⟨843825566810946962885321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562550377873964641923547 843825566810946962885321)
          ·
            refine ⟨632869175108210222163991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 843825566810946962885321 632869175108210222163991)
            ·
              refine ⟨949303762662315333245987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632869175108210222163991 949303762662315333245987)
              ·
                refine ⟨1423955643993472999868981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949303762662315333245987 1423955643993472999868981)
                ·
                  refine ⟨133495841624388093737717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1423955643993472999868981 133495841624388093737717)
                  ·
                    refine ⟨12515235152286383787911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 133495841624388093737717 12515235152286383787911)
                    ·
                      rfl

theorem cell23_73120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_73120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73120 prefixEnd_73120 := by exact prefixLift 73120
  have htrace : WordTrace (prefixWord ++ tailWord_73120) baseStart_73120 baseEnd_73120 := by
    simpa [prefixWord, tailWord_73120, baseEnd_73120] using wordTrace_append hprefix tailTrace_73120
  have hstable : (prefixWord ++ tailWord_73120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73120).length < 2 ^ (prefixWord ++ tailWord_73120).sum := by decide
  have hdescent : baseEnd_73120 < baseStart_73120 := by decide
  rcases family_descends (prefixWord ++ tailWord_73120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73137 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 1, 5]
def baseStart_73137 : Nat := 118140960795 + 73137 * 2 ^ 59
def prefixEnd_73137 : Nat := 4983230072969 + 3 ^ 40 * 73137 * 2
def baseEnd_73137 : Nat := 12518144875995194950385

theorem tailTrace_73137 : CollatzResearch.WordTrace tailWord_73137 prefixEnd_73137 12518144875995194950385 := by
  unfold tailWord_73137
  simp only [CollatzResearch.WordTrace]
  refine ⟨2667525536044614650265665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1778350357363076433510443 2667525536044614650265665)
  ·
    refine ⟨2000644152033460987699249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2667525536044614650265665 2000644152033460987699249)
    ·
      refine ⟨1500483114025095740774437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2000644152033460987699249 1500483114025095740774437)
      ·
        refine ⟨281340583879705451395207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1500483114025095740774437 281340583879705451395207)
        ·
          refine ⟨422010875819558177092811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281340583879705451395207 422010875819558177092811)
          ·
            refine ⟨633016313729337265639217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422010875819558177092811 633016313729337265639217)
            ·
              refine ⟨474762235297002949229413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633016313729337265639217 474762235297002949229413)
              ·
                refine ⟨89017919118188052980515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 474762235297002949229413 89017919118188052980515)
                ·
                  refine ⟨133526878677282079470773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89017919118188052980515 133526878677282079470773)
                  ·
                    refine ⟨12518144875995194950385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 133526878677282079470773 12518144875995194950385)
                    ·
                      rfl

theorem cell23_73137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_73137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73137 prefixEnd_73137 := by exact prefixLift 73137
  have htrace : WordTrace (prefixWord ++ tailWord_73137) baseStart_73137 baseEnd_73137 := by
    simpa [prefixWord, tailWord_73137, baseEnd_73137] using wordTrace_append hprefix tailTrace_73137
  have hstable : (prefixWord ++ tailWord_73137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73137).length < 2 ^ (prefixWord ++ tailWord_73137).sum := by decide
  have hdescent : baseEnd_73137 < baseStart_73137 := by decide
  rcases family_descends (prefixWord ++ tailWord_73137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73144 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 2, 3, 2]
def baseStart_73144 : Nat := 118140960795 + 73144 * 2 ^ 59
def prefixEnd_73144 : Nat := 4983230072969 + 3 ^ 40 * 73144 * 2
def baseEnd_73144 : Nat := 37558028992567057463623

theorem tailTrace_73144 : CollatzResearch.WordTrace tailWord_73144 prefixEnd_73144 37558028992567057463623 := by
  unfold tailWord_73144
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333890423509627422885243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1778520564679503230513657 1333890423509627422885243)
  ·
    refine ⟨2000835635264441134327865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1333890423509627422885243 2000835635264441134327865)
    ·
      refine ⟨1500626726448330850745899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2000835635264441134327865 1500626726448330850745899)
      ·
        refine ⟨2250940089672496276118849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1500626726448330850745899 2250940089672496276118849)
        ·
          refine ⟨1688205067254372207089137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2250940089672496276118849 1688205067254372207089137)
          ·
            refine ⟨1266153800440779155316853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1688205067254372207089137 1266153800440779155316853)
            ·
              refine ⟨118701918791323045810955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1266153800440779155316853 118701918791323045810955)
              ·
                refine ⟨178052878186984568716433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118701918791323045810955 178052878186984568716433)
                ·
                  refine ⟨133539658640238426537325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178052878186984568716433 133539658640238426537325)
                  ·
                    refine ⟨50077371990089409951497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133539658640238426537325 50077371990089409951497)
                    ·
                      refine ⟨37558028992567057463623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50077371990089409951497 37558028992567057463623)
                      ·
                        rfl

theorem cell23_73144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 3, 2].length) (baseStart_73144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73144 prefixEnd_73144 := by exact prefixLift 73144
  have htrace : WordTrace (prefixWord ++ tailWord_73144) baseStart_73144 baseEnd_73144 := by
    simpa [prefixWord, tailWord_73144, baseEnd_73144] using wordTrace_append hprefix tailTrace_73144
  have hstable : (prefixWord ++ tailWord_73144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73144).length < 2 ^ (prefixWord ++ tailWord_73144).sum := by decide
  have hdescent : baseEnd_73144 < baseStart_73144 := by decide
  rcases family_descends (prefixWord ++ tailWord_73144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73177 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 5]
def baseStart_73177 : Nat := 118140960795 + 73177 * 2 ^ 59
def prefixEnd_73177 : Nat := 4983230072969 + 3 ^ 40 * 73177 * 2
def baseEnd_73177 : Nat := 37574973854165428350971

theorem tailTrace_73177 : CollatzResearch.WordTrace tailWord_73177 prefixEnd_73177 37574973854165428350971 := by
  unfold tailWord_73177
  simp only [CollatzResearch.WordTrace]
  refine ⟨2668984455899701481721785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1779322970599800987814523 2668984455899701481721785)
  ·
    refine ⟨2001738341924776111291339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2668984455899701481721785 2001738341924776111291339)
    ·
      refine ⟨3002607512887164166937009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2001738341924776111291339 3002607512887164166937009)
      ·
        refine ⟨2251955634665373125202757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3002607512887164166937009 2251955634665373125202757)
        ·
          refine ⟨422241681499757460975517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2251955634665373125202757 422241681499757460975517)
          ·
            refine ⟨158340630562409047865819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 422241681499757460975517 158340630562409047865819)
            ·
              refine ⟨237510945843613571798729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158340630562409047865819 237510945843613571798729)
              ·
                refine ⟨178133209382710178849047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237510945843613571798729 178133209382710178849047)
                ·
                  refine ⟨267199814074065268273571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178133209382710178849047 267199814074065268273571)
                  ·
                    refine ⟨400799721111097902410357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 267199814074065268273571 400799721111097902410357)
                    ·
                      refine ⟨37574973854165428350971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 400799721111097902410357 37574973854165428350971)
                      ·
                        rfl

theorem cell23_73177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_73177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73177 prefixEnd_73177 := by exact prefixLift 73177
  have htrace : WordTrace (prefixWord ++ tailWord_73177) baseStart_73177 baseEnd_73177 := by
    simpa [prefixWord, tailWord_73177, baseEnd_73177] using wordTrace_append hprefix tailTrace_73177
  have hstable : (prefixWord ++ tailWord_73177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73177).length < 2 ^ (prefixWord ++ tailWord_73177).sum := by decide
  have hdescent : baseEnd_73177 < baseStart_73177 := by decide
  rcases family_descends (prefixWord ++ tailWord_73177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73187 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 6]
def baseStart_73187 : Nat := 118140960795 + 73187 * 2 ^ 59
def prefixEnd_73187 : Nat := 4983230072969 + 3 ^ 40 * 73187 * 2
def baseEnd_73187 : Nat := 37580108660710389225925

theorem tailTrace_73187 : CollatzResearch.WordTrace tailWord_73187 prefixEnd_73187 37580108660710389225925 := by
  unfold tailWord_73187
  simp only [CollatzResearch.WordTrace]
  refine ⟨2669349185863473189585815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1779566123908982126390543 2669349185863473189585815)
  ·
    refine ⟨4004023778795209784378723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2669349185863473189585815 4004023778795209784378723)
    ·
      refine ⟨6006035668192814676568085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4004023778795209784378723 6006035668192814676568085)
      ·
        refine ⟨281532921946538187964129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6006035668192814676568085 281532921946538187964129)
        ·
          refine ⟨211149691459903640973097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281532921946538187964129 211149691459903640973097)
          ·
            refine ⟨158362268594927730729823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211149691459903640973097 158362268594927730729823)
            ·
              refine ⟨237543402892391596094735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158362268594927730729823 237543402892391596094735)
              ·
                refine ⟨356315104338587394142103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237543402892391596094735 356315104338587394142103)
                ·
                  refine ⟨534472656507881091213155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 356315104338587394142103 534472656507881091213155)
                  ·
                    refine ⟨801708984761821636819733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 534472656507881091213155 801708984761821636819733)
                    ·
                      refine ⟨37580108660710389225925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 801708984761821636819733 37580108660710389225925)
                      ·
                        rfl

theorem cell23_73187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_73187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73187 prefixEnd_73187 := by exact prefixLift 73187
  have htrace : WordTrace (prefixWord ++ tailWord_73187) baseStart_73187 baseEnd_73187 := by
    simpa [prefixWord, tailWord_73187, baseEnd_73187] using wordTrace_append hprefix tailTrace_73187
  have hstable : (prefixWord ++ tailWord_73187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73187).length < 2 ^ (prefixWord ++ tailWord_73187).sum := by decide
  have hdescent : baseEnd_73187 < baseStart_73187 := by decide
  rcases family_descends (prefixWord ++ tailWord_73187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73191 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_73191 : Nat := 118140960795 + 73191 * 2 ^ 59
def prefixEnd_73191 : Nat := 4983230072969 + 3 ^ 40 * 73191 * 2
def baseEnd_73191 : Nat := 37582162583328373575907

theorem tailTrace_73191 : CollatzResearch.WordTrace tailWord_73191 prefixEnd_73191 37582162583328373575907 := by
  unfold tailWord_73191
  simp only [CollatzResearch.WordTrace]
  refine ⟨2669495077848981872731427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1779663385232654581820951 2669495077848981872731427)
  ·
    refine ⟨4004242616773472809097141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2669495077848981872731427 4004242616773472809097141)
    ·
      refine ⟨375397745322513075852857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4004242616773472809097141 375397745322513075852857)
      ·
        refine ⟨281548308991884806889643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375397745322513075852857 281548308991884806889643)
        ·
          refine ⟨422322463487827210334465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281548308991884806889643 422322463487827210334465)
          ·
            refine ⟨316741847615870407750849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422322463487827210334465 316741847615870407750849)
            ·
              refine ⟨237556385711902805813137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316741847615870407750849 237556385711902805813137)
              ·
                refine ⟨178167289283927104359853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237556385711902805813137 178167289283927104359853)
                ·
                  refine ⟨66812733481472664134945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178167289283927104359853 66812733481472664134945)
                  ·
                    refine ⟨50109550111104498101209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66812733481472664134945 50109550111104498101209)
                    ·
                      refine ⟨37582162583328373575907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50109550111104498101209 37582162583328373575907)
                      ·
                        rfl

theorem cell23_73191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_73191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73191 prefixEnd_73191 := by exact prefixLift 73191
  have htrace : WordTrace (prefixWord ++ tailWord_73191) baseStart_73191 baseEnd_73191 := by
    simpa [prefixWord, tailWord_73191, baseEnd_73191] using wordTrace_append hprefix tailTrace_73191
  have hstable : (prefixWord ++ tailWord_73191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73191).length < 2 ^ (prefixWord ++ tailWord_73191).sum := by decide
  have hdescent : baseEnd_73191 < baseStart_73191 := by decide
  rcases family_descends (prefixWord ++ tailWord_73191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73208 : List Nat := [2, 1, 2, 1, 1, 5, 3, 3, 1, 2, 2]
def baseStart_73208 : Nat := 118140960795 + 73208 * 2 ^ 59
def prefixEnd_73208 : Nat := 4983230072969 + 3 ^ 40 * 73208 * 2
def baseEnd_73208 : Nat := 37590891754454807063329

theorem tailTrace_73208 : CollatzResearch.WordTrace tailWord_73208 prefixEnd_73208 37590891754454807063329 := by
  unfold tailWord_73208
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335057559393696888050139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1780076745858262517400185 1335057559393696888050139)
  ·
    refine ⟨2002586339090545332075209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1335057559393696888050139 2002586339090545332075209)
    ·
      refine ⟨1501939754317908999056407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2002586339090545332075209 1501939754317908999056407)
      ·
        refine ⟨2252909631476863498584611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1501939754317908999056407 2252909631476863498584611)
        ·
          refine ⟨3379364447215295247876917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2252909631476863498584611 3379364447215295247876917)
          ·
            refine ⟨316815416926433929488461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3379364447215295247876917 316815416926433929488461)
            ·
              refine ⟨118805781347412723558173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316815416926433929488461 118805781347412723558173)
              ·
                refine ⟨44552168005279771334315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118805781347412723558173 44552168005279771334315)
                ·
                  refine ⟨66828252007919657001473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44552168005279771334315 66828252007919657001473)
                  ·
                    refine ⟨50121189005939742751105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66828252007919657001473 50121189005939742751105)
                    ·
                      refine ⟨37590891754454807063329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50121189005939742751105 37590891754454807063329)
                      ·
                        rfl

theorem cell23_73208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 1, 2, 2].length) (baseStart_73208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73208 prefixEnd_73208 := by exact prefixLift 73208
  have htrace : WordTrace (prefixWord ++ tailWord_73208) baseStart_73208 baseEnd_73208 := by
    simpa [prefixWord, tailWord_73208, baseEnd_73208] using wordTrace_append hprefix tailTrace_73208
  have hstable : (prefixWord ++ tailWord_73208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73208).length < 2 ^ (prefixWord ++ tailWord_73208).sum := by decide
  have hdescent : baseEnd_73208 < baseStart_73208 := by decide
  rcases family_descends (prefixWord ++ tailWord_73208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73224 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_73224 : Nat := 118140960795 + 73224 * 2 ^ 59
def prefixEnd_73224 : Nat := 4983230072969 + 3 ^ 40 * 73224 * 2
def baseEnd_73224 : Nat := 37599107444926744463255

theorem tailTrace_73224 : CollatzResearch.WordTrace tailWord_73224 prefixEnd_73224 37599107444926744463255 := by
  unfold tailWord_73224
  simp only [CollatzResearch.WordTrace]
  refine ⟨1335349343364714254341363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1780465791152952339121817 1335349343364714254341363)
  ·
    refine ⟨2003024015047071381512045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1335349343364714254341363 2003024015047071381512045)
    ·
      refine ⟨751134005642651768067017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2003024015047071381512045 751134005642651768067017)
      ·
        refine ⟨563350504231988826050263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751134005642651768067017 563350504231988826050263)
        ·
          refine ⟨845025756347983239075395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563350504231988826050263 845025756347983239075395)
          ·
            refine ⟨1267538634521974858613093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845025756347983239075395 1267538634521974858613093)
            ·
              refine ⟨237663493972870285989955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1267538634521974858613093 237663493972870285989955)
              ·
                refine ⟨356495240959305428984933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237663493972870285989955 356495240959305428984933)
                ·
                  refine ⟨66842857679869767934675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 356495240959305428984933 66842857679869767934675)
                  ·
                    refine ⟨100264286519804651902013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66842857679869767934675 100264286519804651902013)
                    ·
                      refine ⟨37599107444926744463255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 100264286519804651902013 37599107444926744463255)
                      ·
                        rfl

theorem cell23_73224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_73224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73224 prefixEnd_73224 := by exact prefixLift 73224
  have htrace : WordTrace (prefixWord ++ tailWord_73224) baseStart_73224 baseEnd_73224 := by
    simpa [prefixWord, tailWord_73224, baseEnd_73224] using wordTrace_append hprefix tailTrace_73224
  have hstable : (prefixWord ++ tailWord_73224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73224).length < 2 ^ (prefixWord ++ tailWord_73224).sum := by decide
  have hdescent : baseEnd_73224 < baseStart_73224 := by decide
  rcases family_descends (prefixWord ++ tailWord_73224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73251 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 3, 3, 2]
def baseStart_73251 : Nat := 118140960795 + 73251 * 2 ^ 59
def prefixEnd_73251 : Nat := 4983230072969 + 3 ^ 40 * 73251 * 2
def baseEnd_73251 : Nat := 37612971422598138825631

theorem tailTrace_73251 : CollatzResearch.WordTrace tailWord_73251 prefixEnd_73251 37612971422598138825631 := by
  unfold tailWord_73251
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671683457631612119915607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1781122305087741413277071 2671683457631612119915607)
  ·
    refine ⟨4007525186447418179873411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2671683457631612119915607 4007525186447418179873411)
    ·
      refine ⟨6011287779671127269810117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4007525186447418179873411 6011287779671127269810117)
      ·
        refine ⟨1127116458688336363089397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6011287779671127269810117 1127116458688336363089397)
        ·
          refine ⟨105667168002031534039631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1127116458688336363089397 105667168002031534039631)
          ·
            refine ⟨158500752003047301059447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105667168002031534039631 158500752003047301059447)
            ·
              refine ⟨237751128004570951589171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158500752003047301059447 237751128004570951589171)
              ·
                refine ⟨356626692006856427383757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237751128004570951589171 356626692006856427383757)
                ·
                  refine ⟨133735009502571160268909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356626692006856427383757 133735009502571160268909)
                  ·
                    refine ⟨50150628563464185100841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133735009502571160268909 50150628563464185100841)
                    ·
                      refine ⟨37612971422598138825631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50150628563464185100841 37612971422598138825631)
                      ·
                        rfl

theorem cell23_73251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_73251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73251 prefixEnd_73251 := by exact prefixLift 73251
  have htrace : WordTrace (prefixWord ++ tailWord_73251) baseStart_73251 baseEnd_73251 := by
    simpa [prefixWord, tailWord_73251, baseEnd_73251] using wordTrace_append hprefix tailTrace_73251
  have hstable : (prefixWord ++ tailWord_73251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73251).length < 2 ^ (prefixWord ++ tailWord_73251).sum := by decide
  have hdescent : baseEnd_73251 < baseStart_73251 := by decide
  rcases family_descends (prefixWord ++ tailWord_73251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73267 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 5]
def baseStart_73267 : Nat := 118140960795 + 73267 * 2 ^ 59
def prefixEnd_73267 : Nat := 4983230072969 + 3 ^ 40 * 73267 * 2
def baseEnd_73267 : Nat := 37621187113070076225557

theorem tailTrace_73267 : CollatzResearch.WordTrace tailWord_73267 prefixEnd_73267 37621187113070076225557 := by
  unfold tailWord_73267
  simp only [CollatzResearch.WordTrace]
  refine ⟨2672267025573646852498055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1781511350382431234998703 2672267025573646852498055)
  ·
    refine ⟨4008400538360470278747083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2672267025573646852498055 4008400538360470278747083)
    ·
      refine ⟨6012600807540705418120625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4008400538360470278747083 6012600807540705418120625)
      ·
        refine ⟨4509450605655529063590469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6012600807540705418120625 4509450605655529063590469)
        ·
          refine ⟨845521988560411699423213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4509450605655529063590469 845521988560411699423213)
          ·
            refine ⟨317070745710154387283705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 845521988560411699423213 317070745710154387283705)
            ·
              refine ⟨237803059282615790462779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317070745710154387283705 237803059282615790462779)
              ·
                refine ⟨356704588923923685694169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237803059282615790462779 356704588923923685694169)
                ·
                  refine ⟨267528441692942764270627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356704588923923685694169 267528441692942764270627)
                  ·
                    refine ⟨401292662539414146405941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 267528441692942764270627 401292662539414146405941)
                    ·
                      refine ⟨37621187113070076225557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 401292662539414146405941 37621187113070076225557)
                      ·
                        rfl

theorem cell23_73267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_73267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73267 prefixEnd_73267 := by exact prefixLift 73267
  have htrace : WordTrace (prefixWord ++ tailWord_73267) baseStart_73267 baseEnd_73267 := by
    simpa [prefixWord, tailWord_73267, baseEnd_73267] using wordTrace_append hprefix tailTrace_73267
  have hstable : (prefixWord ++ tailWord_73267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73267).length < 2 ^ (prefixWord ++ tailWord_73267).sum := by decide
  have hdescent : baseEnd_73267 < baseStart_73267 := by decide
  rcases family_descends (prefixWord ++ tailWord_73267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73298 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_73298 : Nat := 118140960795 + 73298 * 2 ^ 59
def prefixEnd_73298 : Nat := 4983230072969 + 3 ^ 40 * 73298 * 2
def baseEnd_73298 : Nat := 37637105013359454937915

theorem tailTrace_73298 : CollatzResearch.WordTrace tailWord_73298 prefixEnd_73298 37637105013359454937915 := by
  unfold tailWord_73298
  simp only [CollatzResearch.WordTrace]
  refine ⟨668349422115334786719137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1782265125640892764584365 668349422115334786719137)
  ·
    refine ⟨501262066586501090039353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 668349422115334786719137 501262066586501090039353)
    ·
      refine ⟨375946549939875817529515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 501262066586501090039353 375946549939875817529515)
      ·
        refine ⟨563919824909813726294273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375946549939875817529515 563919824909813726294273)
        ·
          refine ⟨422939868682360294720705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563919824909813726294273 422939868682360294720705)
          ·
            refine ⟨317204901511770221040529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422939868682360294720705 317204901511770221040529)
            ·
              refine ⟨237903676133827665780397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317204901511770221040529 237903676133827665780397)
              ·
                refine ⟨89213878550185374667649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237903676133827665780397 89213878550185374667649)
                ·
                  refine ⟨66910408912639031000737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89213878550185374667649 66910408912639031000737)
                  ·
                    refine ⟨50182806684479273250553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66910408912639031000737 50182806684479273250553)
                    ·
                      refine ⟨37637105013359454937915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50182806684479273250553 37637105013359454937915)
                      ·
                        rfl

theorem cell23_73298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_73298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73298 prefixEnd_73298 := by exact prefixLift 73298
  have htrace : WordTrace (prefixWord ++ tailWord_73298) baseStart_73298 baseEnd_73298 := by
    simpa [prefixWord, tailWord_73298, baseEnd_73298] using wordTrace_append hprefix tailTrace_73298
  have hstable : (prefixWord ++ tailWord_73298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73298).length < 2 ^ (prefixWord ++ tailWord_73298).sum := by decide
  have hdescent : baseEnd_73298 < baseStart_73298 := by decide
  rcases family_descends (prefixWord ++ tailWord_73298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73354 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_73354 : Nat := 118140960795 + 73354 * 2 ^ 59
def prefixEnd_73354 : Nat := 4983230072969 + 3 ^ 40 * 73354 * 2
def baseEnd_73354 : Nat := 37665859930011235837657

theorem tailTrace_73354 : CollatzResearch.WordTrace tailWord_73354 prefixEnd_73354 37665859930011235837657 := by
  unfold tailWord_73354
  simp only [CollatzResearch.WordTrace]
  refine ⟨668860044064615177728779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1783626784172307140610077 668860044064615177728779)
  ·
    refine ⟨1003290066096922766593169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 668860044064615177728779 1003290066096922766593169)
    ·
      refine ⟨752467549572692074944877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1003290066096922766593169 752467549572692074944877)
      ·
        refine ⟨282175331089759528104329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 752467549572692074944877 282175331089759528104329)
        ·
          refine ⟨211631498317319646078247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282175331089759528104329 211631498317319646078247)
          ·
            refine ⟨317447247475979469117371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211631498317319646078247 317447247475979469117371)
            ·
              refine ⟨476170871213969203676057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317447247475979469117371 476170871213969203676057)
              ·
                refine ⟨357128153410476902757043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476170871213969203676057 357128153410476902757043)
                ·
                  refine ⟨535692230115715354135565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357128153410476902757043 535692230115715354135565)
                  ·
                    refine ⟨200884586293393257800837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 535692230115715354135565 200884586293393257800837)
                    ·
                      refine ⟨37665859930011235837657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 200884586293393257800837 37665859930011235837657)
                      ·
                        rfl

theorem cell23_73354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_73354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73354 prefixEnd_73354 := by exact prefixLift 73354
  have htrace : WordTrace (prefixWord ++ tailWord_73354) baseStart_73354 baseEnd_73354 := by
    simpa [prefixWord, tailWord_73354, baseEnd_73354] using wordTrace_append hprefix tailTrace_73354
  have hstable : (prefixWord ++ tailWord_73354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73354).length < 2 ^ (prefixWord ++ tailWord_73354).sum := by decide
  have hdescent : baseEnd_73354 < baseStart_73354 := by decide
  rcases family_descends (prefixWord ++ tailWord_73354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73424 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 1, 5]
def baseStart_73424 : Nat := 118140960795 + 73424 * 2 ^ 59
def prefixEnd_73424 : Nat := 4983230072969 + 3 ^ 40 * 73424 * 2
def baseEnd_73424 : Nat := 12567267858608653987445

theorem tailTrace_73424 : CollatzResearch.WordTrace tailWord_73424 prefixEnd_73424 12567267858608653987445 := by
  unfold tailWord_73424
  simp only [CollatzResearch.WordTrace]
  refine ⟨1338996643002431332981663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1785328857336575110642217 1338996643002431332981663)
  ·
    refine ⟨2008494964503646999472495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1338996643002431332981663 2008494964503646999472495)
    ·
      refine ⟨3012742446755470499208743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2008494964503646999472495 3012742446755470499208743)
      ·
        refine ⟨4519113670133205748813115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012742446755470499208743 4519113670133205748813115)
        ·
          refine ⟨6778670505199808623219673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4519113670133205748813115 6778670505199808623219673)
          ·
            refine ⟨5084002878899856467414755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6778670505199808623219673 5084002878899856467414755)
            ·
              refine ⟨7626004318349784701122133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084002878899856467414755 7626004318349784701122133)
              ·
                refine ⟨89367238105661539466275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7626004318349784701122133 89367238105661539466275)
                ·
                  refine ⟨134050857158492309199413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89367238105661539466275 134050857158492309199413)
                  ·
                    refine ⟨12567267858608653987445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 134050857158492309199413 12567267858608653987445)
                    ·
                      rfl

theorem cell23_73424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 5].length) (baseStart_73424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73424 prefixEnd_73424 := by exact prefixLift 73424
  have htrace : WordTrace (prefixWord ++ tailWord_73424) baseStart_73424 baseEnd_73424 := by
    simpa [prefixWord, tailWord_73424, baseEnd_73424] using wordTrace_append hprefix tailTrace_73424
  have hstable : (prefixWord ++ tailWord_73424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73424).length < 2 ^ (prefixWord ++ tailWord_73424).sum := by decide
  have hdescent : baseEnd_73424 < baseStart_73424 := by decide
  rcases family_descends (prefixWord ++ tailWord_73424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73448 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_73448 : Nat := 118140960795 + 73448 * 2 ^ 59
def prefixEnd_73448 : Nat := 4983230072969 + 3 ^ 40 * 73448 * 2
def baseEnd_73448 : Nat := 37714127111533868062225

theorem tailTrace_73448 : CollatzResearch.WordTrace tailWord_73448 prefixEnd_73448 37714127111533868062225 := by
  unfold tailWord_73448
  simp only [CollatzResearch.WordTrace]
  refine ⟨1339434318958957382418499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1785912425278609843224665 1339434318958957382418499)
  ·
    refine ⟨2009151478438436073627749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1339434318958957382418499 2009151478438436073627749)
    ·
      refine ⟨376715902207206763805203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2009151478438436073627749 376715902207206763805203)
      ·
        refine ⟨565073853310810145707805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376715902207206763805203 565073853310810145707805)
        ·
          refine ⟨211902694991553804640427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 565073853310810145707805 211902694991553804640427)
          ·
            refine ⟨317854042487330706960641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211902694991553804640427 317854042487330706960641)
            ·
              refine ⟨238390531865498030220481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317854042487330706960641 238390531865498030220481)
              ·
                refine ⟨178792898899123522665361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238390531865498030220481 178792898899123522665361)
                ·
                  refine ⟨134094674174342641999021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178792898899123522665361 134094674174342641999021)
                  ·
                    refine ⟨50285502815378490749633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134094674174342641999021 50285502815378490749633)
                    ·
                      refine ⟨37714127111533868062225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50285502815378490749633 37714127111533868062225)
                      ·
                        rfl

theorem cell23_73448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_73448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73448 prefixEnd_73448 := by exact prefixLift 73448
  have htrace : WordTrace (prefixWord ++ tailWord_73448) baseStart_73448 baseEnd_73448 := by
    simpa [prefixWord, tailWord_73448, baseEnd_73448] using wordTrace_append hprefix tailTrace_73448
  have hstable : (prefixWord ++ tailWord_73448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73448).length < 2 ^ (prefixWord ++ tailWord_73448).sum := by decide
  have hdescent : baseEnd_73448 < baseStart_73448 := by decide
  rcases family_descends (prefixWord ++ tailWord_73448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73454 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_73454 : Nat := 118140960795 + 73454 * 2 ^ 59
def prefixEnd_73454 : Nat := 4983230072969 + 3 ^ 40 * 73454 * 2
def baseEnd_73454 : Nat := 12572402665153614862399

theorem tailTrace_73454 : CollatzResearch.WordTrace tailWord_73454 prefixEnd_73454 12572402665153614862399 := by
  unfold tailWord_73454
  simp only [CollatzResearch.WordTrace]
  refine ⟨334885934487022223694427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1786058317264118526370277 334885934487022223694427)
  ·
    refine ⟨502328901730533335541641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 334885934487022223694427 502328901730533335541641)
    ·
      refine ⟨376746676297900001656231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 502328901730533335541641 376746676297900001656231)
      ·
        refine ⟨565120014446850002484347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376746676297900001656231 565120014446850002484347)
        ·
          refine ⟨847680021670275003726521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565120014446850002484347 847680021670275003726521)
          ·
            refine ⟨635760016252706252794891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 847680021670275003726521 635760016252706252794891)
            ·
              refine ⟨953640024379059379192337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635760016252706252794891 953640024379059379192337)
              ·
                refine ⟨715230018284294534394253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953640024379059379192337 715230018284294534394253)
                ·
                  refine ⟨268211256856610450397845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 715230018284294534394253 268211256856610450397845)
                  ·
                    refine ⟨12572402665153614862399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 268211256856610450397845 12572402665153614862399)
                    ·
                      rfl

theorem cell23_73454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_73454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73454 prefixEnd_73454 := by exact prefixLift 73454
  have htrace : WordTrace (prefixWord ++ tailWord_73454) baseStart_73454 baseEnd_73454 := by
    simpa [prefixWord, tailWord_73454, baseEnd_73454] using wordTrace_append hprefix tailTrace_73454
  have hstable : (prefixWord ++ tailWord_73454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73454).length < 2 ^ (prefixWord ++ tailWord_73454).sum := by decide
  have hdescent : baseEnd_73454 < baseStart_73454 := by decide
  rcases family_descends (prefixWord ++ tailWord_73454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73467 : List Nat := [1, 1, 1, 1, 1, 3, 1, 14]
def baseStart_73467 : Nat := 118140960795 + 73467 * 2 ^ 59
def prefixEnd_73467 : Nat := 4983230072969 + 3 ^ 40 * 73467 * 2
def baseEnd_73467 : Nat := 1397180860887751619431

theorem tailTrace_73467 : CollatzResearch.WordTrace tailWord_73467 prefixEnd_73467 1397180860887751619431 := by
  unfold tailWord_73467
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679561624849081009778655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1786374416566054006519103 2679561624849081009778655)
  ·
    refine ⟨4019342437273621514667983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2679561624849081009778655 4019342437273621514667983)
    ·
      refine ⟨6029013655910432272001975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4019342437273621514667983 6029013655910432272001975)
      ·
        refine ⟨9043520483865648408002963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6029013655910432272001975 9043520483865648408002963)
        ·
          refine ⟨13565280725798472612004445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9043520483865648408002963 13565280725798472612004445)
          ·
            refine ⟨5086980272174427229501667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13565280725798472612004445 5086980272174427229501667)
            ·
              refine ⟨7630470408261640844252501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086980272174427229501667 7630470408261640844252501)
              ·
                refine ⟨1397180860887751619431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 7630470408261640844252501 1397180860887751619431)
                ·
                  rfl

theorem cell23_73467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 14].length) (baseStart_73467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73467 prefixEnd_73467 := by exact prefixLift 73467
  have htrace : WordTrace (prefixWord ++ tailWord_73467) baseStart_73467 baseEnd_73467 := by
    simpa [prefixWord, tailWord_73467, baseEnd_73467] using wordTrace_append hprefix tailTrace_73467
  have hstable : (prefixWord ++ tailWord_73467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73467).length < 2 ^ (prefixWord ++ tailWord_73467).sum := by decide
  have hdescent : baseEnd_73467 < baseStart_73467 := by decide
  rcases family_descends (prefixWord ++ tailWord_73467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73471 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 2, 4]
def baseStart_73471 : Nat := 118140960795 + 73471 * 2 ^ 59
def prefixEnd_73471 : Nat := 4983230072969 + 3 ^ 40 * 73471 * 2
def baseEnd_73471 : Nat := 12575312388862426024873

theorem tailTrace_73471 : CollatzResearch.WordTrace tailWord_73471 prefixEnd_73471 12575312388862426024873 := by
  unfold tailWord_73471
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679707516834589692924267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1786471677889726461949511 2679707516834589692924267)
  ·
    refine ⟨4019561275251884539386401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2679707516834589692924267 4019561275251884539386401)
    ·
      refine ⟨3014670956438913404539801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4019561275251884539386401 3014670956438913404539801)
      ·
        refine ⟨2261003217329185053404851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3014670956438913404539801 2261003217329185053404851)
        ·
          refine ⟨3391504825993777580107277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2261003217329185053404851 3391504825993777580107277)
          ·
            refine ⟨1271814309747666592540229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3391504825993777580107277 1271814309747666592540229)
            ·
              refine ⟨238465183077687486101293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1271814309747666592540229 238465183077687486101293)
              ·
                refine ⟨89424443654132807287985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238465183077687486101293 89424443654132807287985)
                ·
                  refine ⟨67068332740599605465989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89424443654132807287985 67068332740599605465989)
                  ·
                    refine ⟨12575312388862426024873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67068332740599605465989 12575312388862426024873)
                    ·
                      rfl

theorem cell23_73471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 4].length) (baseStart_73471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73471 prefixEnd_73471 := by exact prefixLift 73471
  have htrace : WordTrace (prefixWord ++ tailWord_73471) baseStart_73471 baseEnd_73471 := by
    simpa [prefixWord, tailWord_73471, baseEnd_73471] using wordTrace_append hprefix tailTrace_73471
  have hstable : (prefixWord ++ tailWord_73471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73471).length < 2 ^ (prefixWord ++ tailWord_73471).sum := by decide
  have hdescent : baseEnd_73471 < baseStart_73471 := by decide
  rcases family_descends (prefixWord ++ tailWord_73471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73481 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 1, 2, 3]
def baseStart_73481 : Nat := 118140960795 + 73481 * 2 ^ 59
def prefixEnd_73481 : Nat := 4983230072969 + 3 ^ 40 * 73481 * 2
def baseEnd_73481 : Nat := 37731071973132238949573

theorem tailTrace_73481 : CollatzResearch.WordTrace tailWord_73481 prefixEnd_73481 37731071973132238949573 := by
  unfold tailWord_73481
  simp only [CollatzResearch.WordTrace]
  refine ⟨2680072246798361400788297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1786714831198907600525531 2680072246798361400788297)
  ·
    refine ⟨2010054185098771050591223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2680072246798361400788297 2010054185098771050591223)
    ·
      refine ⟨3015081277648156575886835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2010054185098771050591223 3015081277648156575886835)
      ·
        refine ⟨4522621916472234863830253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015081277648156575886835 4522621916472234863830253)
        ·
          refine ⟨1695983218677088073936345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4522621916472234863830253 1695983218677088073936345)
          ·
            refine ⟨1271987414007816055452259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1695983218677088073936345 1271987414007816055452259)
            ·
              refine ⟨1907981121011724083178389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271987414007816055452259 1907981121011724083178389)
              ·
                refine ⟨89436615047424566398987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1907981121011724083178389 89436615047424566398987)
                ·
                  refine ⟨134154922571136849598481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89436615047424566398987 134154922571136849598481)
                  ·
                    refine ⟨100616191928352637198861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134154922571136849598481 100616191928352637198861)
                    ·
                      refine ⟨37731071973132238949573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 100616191928352637198861 37731071973132238949573)
                      ·
                        rfl

theorem cell23_73481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 2, 3].length) (baseStart_73481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73481 prefixEnd_73481 := by exact prefixLift 73481
  have htrace : WordTrace (prefixWord ++ tailWord_73481) baseStart_73481 baseEnd_73481 := by
    simpa [prefixWord, tailWord_73481, baseEnd_73481] using wordTrace_append hprefix tailTrace_73481
  have hstable : (prefixWord ++ tailWord_73481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73481).length < 2 ^ (prefixWord ++ tailWord_73481).sum := by decide
  have hdescent : baseEnd_73481 < baseStart_73481 := by decide
  rcases family_descends (prefixWord ++ tailWord_73481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73492 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_73492 : Nat := 118140960795 + 73492 * 2 ^ 59
def prefixEnd_73492 : Nat := 4983230072969 + 3 ^ 40 * 73492 * 2
def baseEnd_73492 : Nat := 12578906753443898637341

theorem tailTrace_73492 : CollatzResearch.WordTrace tailWord_73492 prefixEnd_73492 12578906753443898637341 := by
  unfold tailWord_73492
  simp only [CollatzResearch.WordTrace]
  refine ⟨1340236724879255139719365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1786982299839006852959153 1340236724879255139719365)
  ·
    refine ⟨251294385914860338697381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1340236724879255139719365 251294385914860338697381)
    ·
      refine ⟨47117697359036313505759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251294385914860338697381 47117697359036313505759)
      ·
        refine ⟨70676546038554470258639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47117697359036313505759 70676546038554470258639)
        ·
          refine ⟨106014819057831705387959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70676546038554470258639 106014819057831705387959)
          ·
            refine ⟨159022228586747558081939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106014819057831705387959 159022228586747558081939)
            ·
              refine ⟨238533342880121337122909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159022228586747558081939 238533342880121337122909)
              ·
                refine ⟨89450003580045501421091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238533342880121337122909 89450003580045501421091)
                ·
                  refine ⟨134175005370068252131637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89450003580045501421091 134175005370068252131637)
                  ·
                    refine ⟨12578906753443898637341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 134175005370068252131637 12578906753443898637341)
                    ·
                      rfl

theorem cell23_73492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_73492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73492 prefixEnd_73492 := by exact prefixLift 73492
  have htrace : WordTrace (prefixWord ++ tailWord_73492) baseStart_73492 baseEnd_73492 := by
    simpa [prefixWord, tailWord_73492, baseEnd_73492] using wordTrace_append hprefix tailTrace_73492
  have hstable : (prefixWord ++ tailWord_73492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73492).length < 2 ^ (prefixWord ++ tailWord_73492).sum := by decide
  have hdescent : baseEnd_73492 < baseStart_73492 := by decide
  rcases family_descends (prefixWord ++ tailWord_73492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73495 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 1, 1, 4]
def baseStart_73495 : Nat := 118140960795 + 73495 * 2 ^ 59
def prefixEnd_73495 : Nat := 4983230072969 + 3 ^ 40 * 73495 * 2
def baseEnd_73495 : Nat := 37738260702295184174509

theorem tailTrace_73495 : CollatzResearch.WordTrace tailWord_73495 prefixEnd_73495 37738260702295184174509 := by
  unfold tailWord_73495
  simp only [CollatzResearch.WordTrace]
  refine ⟨2680582868747641791797939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1787055245831761194531959 2680582868747641791797939)
  ·
    refine ⟨4020874303121462687696909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2680582868747641791797939 4020874303121462687696909)
    ·
      refine ⟨1507827863670548507886341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4020874303121462687696909 1507827863670548507886341)
      ·
        refine ⟨282717724438227845228689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1507827863670548507886341 282717724438227845228689)
        ·
          refine ⟨212038293328670883921517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282717724438227845228689 212038293328670883921517)
          ·
            refine ⟨79514359998251581470569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212038293328670883921517 79514359998251581470569)
            ·
              refine ⟨59635769998688686102927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79514359998251581470569 59635769998688686102927)
              ·
                refine ⟨89453654998033029154391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59635769998688686102927 89453654998033029154391)
                ·
                  refine ⟨134180482497049543731587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89453654998033029154391 134180482497049543731587)
                  ·
                    refine ⟨201270723745574315597381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134180482497049543731587 201270723745574315597381)
                    ·
                      refine ⟨37738260702295184174509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 201270723745574315597381 37738260702295184174509)
                      ·
                        rfl

theorem cell23_73495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_73495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73495 prefixEnd_73495 := by exact prefixLift 73495
  have htrace : WordTrace (prefixWord ++ tailWord_73495) baseStart_73495 baseEnd_73495 := by
    simpa [prefixWord, tailWord_73495, baseEnd_73495] using wordTrace_append hprefix tailTrace_73495
  have hstable : (prefixWord ++ tailWord_73495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73495).length < 2 ^ (prefixWord ++ tailWord_73495).sum := by decide
  have hdescent : baseEnd_73495 < baseStart_73495 := by decide
  rcases family_descends (prefixWord ++ tailWord_73495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73498 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3]
def baseStart_73498 : Nat := 118140960795 + 73498 * 2 ^ 59
def prefixEnd_73498 : Nat := 4983230072969 + 3 ^ 40 * 73498 * 2
def baseEnd_73498 : Nat := 37739801144258672436995

theorem tailTrace_73498 : CollatzResearch.WordTrace tailWord_73498 prefixEnd_73498 37739801144258672436995 := by
  unfold tailWord_73498
  simp only [CollatzResearch.WordTrace]
  refine ⟨670173071934193326039287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1787128191824515536104765 670173071934193326039287)
  ·
    refine ⟨1005259607901289989058931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 670173071934193326039287 1005259607901289989058931)
    ·
      refine ⟨1507889411851934983588397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005259607901289989058931 1507889411851934983588397)
      ·
        refine ⟨565458529444475618845649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1507889411851934983588397 565458529444475618845649)
        ·
          refine ⟨424093897083356714134237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565458529444475618845649 424093897083356714134237)
          ·
            refine ⟨159035211406258767800339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 424093897083356714134237 159035211406258767800339)
            ·
              refine ⟨238552817109388151700509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159035211406258767800339 238552817109388151700509)
              ·
                refine ⟨89457306416020556887691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238552817109388151700509 89457306416020556887691)
                ·
                  refine ⟨134185959624030835331537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89457306416020556887691 134185959624030835331537)
                  ·
                    refine ⟨100639469718023126498653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134185959624030835331537 100639469718023126498653)
                    ·
                      refine ⟨37739801144258672436995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 100639469718023126498653 37739801144258672436995)
                      ·
                        rfl

theorem cell23_73498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_73498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73498 prefixEnd_73498 := by exact prefixLift 73498
  have htrace : WordTrace (prefixWord ++ tailWord_73498) baseStart_73498 baseEnd_73498 := by
    simpa [prefixWord, tailWord_73498, baseEnd_73498] using wordTrace_append hprefix tailTrace_73498
  have hstable : (prefixWord ++ tailWord_73498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73498).length < 2 ^ (prefixWord ++ tailWord_73498).sum := by decide
  have hdescent : baseEnd_73498 < baseStart_73498 := by decide
  rcases family_descends (prefixWord ++ tailWord_73498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73512 : List Nat := [2, 1, 5, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_73512 : Nat := 118140960795 + 73512 * 2 ^ 59
def prefixEnd_73512 : Nat := 4983230072969 + 3 ^ 40 * 73512 * 2
def baseEnd_73512 : Nat := 37746989873421617661931

theorem tailTrace_73512 : CollatzResearch.WordTrace tailWord_73512 prefixEnd_73512 37746989873421617661931 := by
  unfold tailWord_73512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1340601454843026847583395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1787468606457369130111193 1340601454843026847583395)
  ·
    refine ⟨2010902182264540271375093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1340601454843026847583395 2010902182264540271375093)
    ·
      refine ⟨188522079587300650441415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2010902182264540271375093 188522079587300650441415)
      ·
        refine ⟨282783119380950975662123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188522079587300650441415 282783119380950975662123)
        ·
          refine ⟨424174679071426463493185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282783119380950975662123 424174679071426463493185)
          ·
            refine ⟨318131009303569847619889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424174679071426463493185 318131009303569847619889)
            ·
              refine ⟨238598256977677385714917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318131009303569847619889 238598256977677385714917)
              ·
                refine ⟨44737173183314509821547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238598256977677385714917 44737173183314509821547)
                ·
                  refine ⟨67105759774971764732321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44737173183314509821547 67105759774971764732321)
                  ·
                    refine ⟨50329319831228823549241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67105759774971764732321 50329319831228823549241)
                    ·
                      refine ⟨37746989873421617661931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50329319831228823549241 37746989873421617661931)
                      ·
                        rfl

theorem cell23_73512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_73512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73512 prefixEnd_73512 := by exact prefixLift 73512
  have htrace : WordTrace (prefixWord ++ tailWord_73512) baseStart_73512 baseEnd_73512 := by
    simpa [prefixWord, tailWord_73512, baseEnd_73512] using wordTrace_append hprefix tailTrace_73512
  have hstable : (prefixWord ++ tailWord_73512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73512).length < 2 ^ (prefixWord ++ tailWord_73512).sum := by decide
  have hdescent : baseEnd_73512 < baseStart_73512 := by decide
  rcases family_descends (prefixWord ++ tailWord_73512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73525 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_73525 : Nat := 118140960795 + 73525 * 2 ^ 59
def prefixEnd_73525 : Nat := 4983230072969 + 3 ^ 40 * 73525 * 2
def baseEnd_73525 : Nat := 37753665121930066799371

theorem tailTrace_73525 : CollatzResearch.WordTrace tailWord_73525 prefixEnd_73525 37753665121930066799371 := by
  unfold tailWord_73525
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681677058638956915390029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1787784705759304610260019 2681677058638956915390029)
  ·
    refine ⟨1005628896989608843271261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2681677058638956915390029 1005628896989608843271261)
    ·
      refine ⟨377110836371103316226723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1005628896989608843271261 377110836371103316226723)
      ·
        refine ⟨565666254556654974340085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377110836371103316226723 565666254556654974340085)
        ·
          refine ⟨53031211364686403844383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 565666254556654974340085 53031211364686403844383)
          ·
            refine ⟨79546817047029605766575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53031211364686403844383 79546817047029605766575)
            ·
              refine ⟨119320225570544408649863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79546817047029605766575 119320225570544408649863)
              ·
                refine ⟨178980338355816612974795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119320225570544408649863 178980338355816612974795)
                ·
                  refine ⟨268470507533724919462193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178980338355816612974795 268470507533724919462193)
                  ·
                    refine ⟨201352880650293689596645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 268470507533724919462193 201352880650293689596645)
                    ·
                      refine ⟨37753665121930066799371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 201352880650293689596645 37753665121930066799371)
                      ·
                        rfl

theorem cell23_73525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_73525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73525 prefixEnd_73525 := by exact prefixLift 73525
  have htrace : WordTrace (prefixWord ++ tailWord_73525) baseStart_73525 baseEnd_73525 := by
    simpa [prefixWord, tailWord_73525, baseEnd_73525] using wordTrace_append hprefix tailTrace_73525
  have hstable : (prefixWord ++ tailWord_73525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73525).length < 2 ^ (prefixWord ++ tailWord_73525).sum := by decide
  have hdescent : baseEnd_73525 < baseStart_73525 := by decide
  rcases family_descends (prefixWord ++ tailWord_73525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73528 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 1, 3, 3]
def baseStart_73528 : Nat := 118140960795 + 73528 * 2 ^ 59
def prefixEnd_73528 : Nat := 4983230072969 + 3 ^ 40 * 73528 * 2
def baseEnd_73528 : Nat := 37755205563893555061857

theorem tailTrace_73528 : CollatzResearch.WordTrace tailWord_73528 prefixEnd_73528 37755205563893555061857 := by
  unfold tailWord_73528
  simp only [CollatzResearch.WordTrace]
  refine ⟨1340893238814044213874619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1787857651752058951832825 1340893238814044213874619)
  ·
    refine ⟨2011339858221066320811929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1340893238814044213874619 2011339858221066320811929)
    ·
      refine ⟨1508504893665799740608947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2011339858221066320811929 1508504893665799740608947)
      ·
        refine ⟨2262757340498699610913421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1508504893665799740608947 2262757340498699610913421)
        ·
          refine ⟨848534002687012354092533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2262757340498699610913421 848534002687012354092533)
          ·
            refine ⟨79550062751907408196175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 848534002687012354092533 79550062751907408196175)
            ·
              refine ⟨119325094127861112294263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79550062751907408196175 119325094127861112294263)
              ·
                refine ⟨178987641191791668441395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119325094127861112294263 178987641191791668441395)
                ·
                  refine ⟨268481461787687502662093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178987641191791668441395 268481461787687502662093)
                  ·
                    refine ⟨100680548170382813498285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 268481461787687502662093 100680548170382813498285)
                    ·
                      refine ⟨37755205563893555061857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 100680548170382813498285 37755205563893555061857)
                      ·
                        rfl

theorem cell23_73528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_73528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73528 prefixEnd_73528 := by exact prefixLift 73528
  have htrace : WordTrace (prefixWord ++ tailWord_73528) baseStart_73528 baseEnd_73528 := by
    simpa [prefixWord, tailWord_73528, baseEnd_73528] using wordTrace_append hprefix tailTrace_73528
  have hstable : (prefixWord ++ tailWord_73528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73528).length < 2 ^ (prefixWord ++ tailWord_73528).sum := by decide
  have hdescent : baseEnd_73528 < baseStart_73528 := by decide
  rcases family_descends (prefixWord ++ tailWord_73528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73581 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_73581 : Nat := 118140960795 + 73581 * 2 ^ 59
def prefixEnd_73581 : Nat := 4983230072969 + 3 ^ 40 * 73581 * 2
def baseEnd_73581 : Nat := 37782420038581847699113

theorem tailTrace_73581 : CollatzResearch.WordTrace tailWord_73581 prefixEnd_73581 37782420038581847699113 := by
  unfold tailWord_73581
  simp only [CollatzResearch.WordTrace]
  refine ⟨2683719546436078479428597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1789146364290718986285731 2683719546436078479428597)
  ·
    refine ⟨251598707478382357446431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2683719546436078479428597 251598707478382357446431)
    ·
      refine ⟨377398061217573536169647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251598707478382357446431 377398061217573536169647)
      ·
        refine ⟨566097091826360304254471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377398061217573536169647 566097091826360304254471)
        ·
          refine ⟨849145637739540456381707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566097091826360304254471 849145637739540456381707)
          ·
            refine ⟨1273718456609310684572561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849145637739540456381707 1273718456609310684572561)
            ·
              refine ⟨955288842456983013429421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273718456609310684572561 955288842456983013429421)
              ·
                refine ⟨358233315921368630036033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 955288842456983013429421 358233315921368630036033)
                ·
                  refine ⟨268674986941026472527025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358233315921368630036033 268674986941026472527025)
                  ·
                    refine ⟨201506240205769854395269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 268674986941026472527025 201506240205769854395269)
                    ·
                      refine ⟨37782420038581847699113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 201506240205769854395269 37782420038581847699113)
                      ·
                        rfl

theorem cell23_73581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_73581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73581 prefixEnd_73581 := by exact prefixLift 73581
  have htrace : WordTrace (prefixWord ++ tailWord_73581) baseStart_73581 baseEnd_73581 := by
    simpa [prefixWord, tailWord_73581, baseEnd_73581] using wordTrace_append hprefix tailTrace_73581
  have hstable : (prefixWord ++ tailWord_73581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73581).length < 2 ^ (prefixWord ++ tailWord_73581).sum := by decide
  have hdescent : baseEnd_73581 < baseStart_73581 := by decide
  rcases family_descends (prefixWord ++ tailWord_73581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73585 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 2, 2, 2]
def baseStart_73585 : Nat := 118140960795 + 73585 * 2 ^ 59
def prefixEnd_73585 : Nat := 4983230072969 + 3 ^ 40 * 73585 * 2
def baseEnd_73585 : Nat := 37784473961199832049095

theorem tailTrace_73585 : CollatzResearch.WordTrace tailWord_73585 prefixEnd_73585 37784473961199832049095 := by
  unfold tailWord_73585
  simp only [CollatzResearch.WordTrace]
  refine ⟨2683865438421587162574209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1789243625614391441716139 2683865438421587162574209)
  ·
    refine ⟨2012899078816190371930657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2683865438421587162574209 2012899078816190371930657)
    ·
      refine ⟨1509674309112142778947993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2012899078816190371930657 1509674309112142778947993)
      ·
        refine ⟨1132255731834107084210995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1509674309112142778947993 1132255731834107084210995)
        ·
          refine ⟨1698383597751160626316493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132255731834107084210995 1698383597751160626316493)
          ·
            refine ⟨636893849156685234868685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1698383597751160626316493 636893849156685234868685)
            ·
              refine ⟨238835193433756963075757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 636893849156685234868685 238835193433756963075757)
              ·
                refine ⟨89563197537658861153409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238835193433756963075757 89563197537658861153409)
                ·
                  refine ⟨67172398153244145865057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89563197537658861153409 67172398153244145865057)
                  ·
                    refine ⟨50379298614933109398793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67172398153244145865057 50379298614933109398793)
                    ·
                      refine ⟨37784473961199832049095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50379298614933109398793 37784473961199832049095)
                      ·
                        rfl

theorem cell23_73585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_73585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73585 prefixEnd_73585 := by exact prefixLift 73585
  have htrace : WordTrace (prefixWord ++ tailWord_73585) baseStart_73585 baseEnd_73585 := by
    simpa [prefixWord, tailWord_73585, baseEnd_73585] using wordTrace_append hprefix tailTrace_73585
  have hstable : (prefixWord ++ tailWord_73585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73585).length < 2 ^ (prefixWord ++ tailWord_73585).sum := by decide
  have hdescent : baseEnd_73585 < baseStart_73585 := by decide
  rcases family_descends (prefixWord ++ tailWord_73585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73621 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_73621 : Nat := 118140960795 + 73621 * 2 ^ 59
def prefixEnd_73621 : Nat := 4983230072969 + 3 ^ 40 * 73621 * 2
def baseEnd_73621 : Nat := 12600986421587230399643

theorem tailTrace_73621 : CollatzResearch.WordTrace tailWord_73621 prefixEnd_73621 12600986421587230399643 := by
  unfold tailWord_73621
  simp only [CollatzResearch.WordTrace]
  refine ⟨2685178466291165310884717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1790118977527443540589811 2685178466291165310884717)
  ·
    refine ⟨1006941924859186991581769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2685178466291165310884717 1006941924859186991581769)
    ·
      refine ⟨755206443644390243686327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1006941924859186991581769 755206443644390243686327)
      ·
        refine ⟨1132809665466585365529491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755206443644390243686327 1132809665466585365529491)
        ·
          refine ⟨1699214498199878048294237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132809665466585365529491 1699214498199878048294237)
          ·
            refine ⟨637205436824954268110339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1699214498199878048294237 637205436824954268110339)
            ·
              refine ⟨955808155237431402165509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637205436824954268110339 955808155237431402165509)
              ·
                refine ⟨179214029107018387906033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 955808155237431402165509 179214029107018387906033)
                ·
                  refine ⟨134410521830263790929525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179214029107018387906033 134410521830263790929525)
                  ·
                    refine ⟨12600986421587230399643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 134410521830263790929525 12600986421587230399643)
                    ·
                      rfl

theorem cell23_73621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_73621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73621 prefixEnd_73621 := by exact prefixLift 73621
  have htrace : WordTrace (prefixWord ++ tailWord_73621) baseStart_73621 baseEnd_73621 := by
    simpa [prefixWord, tailWord_73621, baseEnd_73621] using wordTrace_append hprefix tailTrace_73621
  have hstable : (prefixWord ++ tailWord_73621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73621).length < 2 ^ (prefixWord ++ tailWord_73621).sum := by decide
  have hdescent : baseEnd_73621 < baseStart_73621 := by decide
  rcases family_descends (prefixWord ++ tailWord_73621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73678 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_73678 : Nat := 118140960795 + 73678 * 2 ^ 59
def prefixEnd_73678 : Nat := 4983230072969 + 3 ^ 40 * 73678 * 2
def baseEnd_73678 : Nat := 37832227662067968186167

theorem tailTrace_73678 : CollatzResearch.WordTrace tailWord_73678 prefixEnd_73678 37832227662067968186167 := by
  unfold tailWord_73678
  simp only [CollatzResearch.WordTrace]
  refine ⟨335907178385583005713711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1791504951389776030473125 335907178385583005713711)
  ·
    refine ⟨503860767578374508570567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 335907178385583005713711 503860767578374508570567)
    ·
      refine ⟨755791151367561762855851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 503860767578374508570567 755791151367561762855851)
      ·
        refine ⟨1133686727051342644283777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755791151367561762855851 1133686727051342644283777)
        ·
          refine ⟨850265045288506983212833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1133686727051342644283777 850265045288506983212833)
          ·
            refine ⟨637698783966380237409625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 850265045288506983212833 637698783966380237409625)
            ·
              refine ⟨478274087974785178057219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637698783966380237409625 478274087974785178057219)
              ·
                refine ⟨717411131962177767085829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478274087974785178057219 717411131962177767085829)
                ·
                  refine ⟨134514587242908331328593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717411131962177767085829 134514587242908331328593)
                  ·
                    refine ⟨100885940432181248496445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134514587242908331328593 100885940432181248496445)
                    ·
                      refine ⟨37832227662067968186167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 100885940432181248496445 37832227662067968186167)
                      ·
                        rfl

theorem cell23_73678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_73678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73678 prefixEnd_73678 := by exact prefixLift 73678
  have htrace : WordTrace (prefixWord ++ tailWord_73678) baseStart_73678 baseEnd_73678 := by
    simpa [prefixWord, tailWord_73678, baseEnd_73678] using wordTrace_append hprefix tailTrace_73678
  have hstable : (prefixWord ++ tailWord_73678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73678).length < 2 ^ (prefixWord ++ tailWord_73678).sum := by decide
  have hdescent : baseEnd_73678 < baseStart_73678 := by decide
  rcases family_descends (prefixWord ++ tailWord_73678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73681 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 6]
def baseStart_73681 : Nat := 118140960795 + 73681 * 2 ^ 59
def prefixEnd_73681 : Nat := 4983230072969 + 3 ^ 40 * 73681 * 2
def baseEnd_73681 : Nat := 4203752011559050716517

theorem tailTrace_73681 : CollatzResearch.WordTrace tailWord_73681 prefixEnd_73681 4203752011559050716517 := by
  unfold tailWord_73681
  simp only [CollatzResearch.WordTrace]
  refine ⟨2687366846073795558068897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1791577897382530372045931 2687366846073795558068897)
  ·
    refine ⟨2015525134555346668551673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2687366846073795558068897 2015525134555346668551673)
    ·
      refine ⟨1511643850916510001413755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2015525134555346668551673 1511643850916510001413755)
      ·
        refine ⟨2267465776374765002120633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511643850916510001413755 2267465776374765002120633)
        ·
          refine ⟨1700599332281073751590475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2267465776374765002120633 1700599332281073751590475)
          ·
            refine ⟨2550898998421610627385713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700599332281073751590475 2550898998421610627385713)
            ·
              refine ⟨1913174248816207970539285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2550898998421610627385713 1913174248816207970539285)
              ·
                refine ⟨89680042913259748619029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1913174248816207970539285 89680042913259748619029)
                ·
                  refine ⟨4203752011559050716517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89680042913259748619029 4203752011559050716517)
                  ·
                    rfl

theorem cell23_73681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 6].length) (baseStart_73681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73681 prefixEnd_73681 := by exact prefixLift 73681
  have htrace : WordTrace (prefixWord ++ tailWord_73681) baseStart_73681 baseEnd_73681 := by
    simpa [prefixWord, tailWord_73681, baseEnd_73681] using wordTrace_append hprefix tailTrace_73681
  have hstable : (prefixWord ++ tailWord_73681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73681).length < 2 ^ (prefixWord ++ tailWord_73681).sum := by decide
  have hdescent : baseEnd_73681 < baseStart_73681 := by decide
  rcases family_descends (prefixWord ++ tailWord_73681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73685 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 3, 4]
def baseStart_73685 : Nat := 118140960795 + 73685 * 2 ^ 59
def prefixEnd_73685 : Nat := 4983230072969 + 3 ^ 40 * 73685 * 2
def baseEnd_73685 : Nat := 12611940675549813599545

theorem tailTrace_73685 : CollatzResearch.WordTrace tailWord_73685 prefixEnd_73685 12611940675549813599545 := by
  unfold tailWord_73685
  simp only [CollatzResearch.WordTrace]
  refine ⟨2687512738059304241214509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1791675158706202827476339 2687512738059304241214509)
  ·
    refine ⟨1007817276772239090455441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2687512738059304241214509 1007817276772239090455441)
    ·
      refine ⟨755862957579179317841581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1007817276772239090455441 755862957579179317841581)
      ·
        refine ⟨283448609092192244190593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 755862957579179317841581 283448609092192244190593)
        ·
          refine ⟨212586456819144183142945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283448609092192244190593 212586456819144183142945)
          ·
            refine ⟨159439842614358137357209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212586456819144183142945 159439842614358137357209)
            ·
              refine ⟨119579881960768603017907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159439842614358137357209 119579881960768603017907)
              ·
                refine ⟨179369822941152904526861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119579881960768603017907 179369822941152904526861)
                ·
                  refine ⟨67263683602932339197573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179369822941152904526861 67263683602932339197573)
                  ·
                    refine ⟨12611940675549813599545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67263683602932339197573 12611940675549813599545)
                    ·
                      rfl

theorem cell23_73685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_73685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73685 prefixEnd_73685 := by exact prefixLift 73685
  have htrace : WordTrace (prefixWord ++ tailWord_73685) baseStart_73685 baseEnd_73685 := by
    simpa [prefixWord, tailWord_73685, baseEnd_73685] using wordTrace_append hprefix tailTrace_73685
  have hstable : (prefixWord ++ tailWord_73685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73685).length < 2 ^ (prefixWord ++ tailWord_73685).sum := by decide
  have hdescent : baseEnd_73685 < baseStart_73685 := by decide
  rcases family_descends (prefixWord ++ tailWord_73685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73735 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 4, 3, 2]
def baseStart_73735 : Nat := 118140960795 + 73735 * 2 ^ 59
def prefixEnd_73735 : Nat := 4983230072969 + 3 ^ 40 * 73735 * 2
def baseEnd_73735 : Nat := 37861496059374245173405

theorem tailTrace_73735 : CollatzResearch.WordTrace tailWord_73735 prefixEnd_73735 37861496059374245173405 := by
  unfold tailWord_73735
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689336387878162780534659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1792890925252108520356439 2689336387878162780534659)
  ·
    refine ⟨4034004581817244170801989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2689336387878162780534659 4034004581817244170801989)
    ·
      refine ⟨756375859090733282025373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4034004581817244170801989 756375859090733282025373)
      ·
        refine ⟨283640947159024980759515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 756375859090733282025373 283640947159024980759515)
        ·
          refine ⟨425461420738537471139273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283640947159024980759515 425461420738537471139273)
          ·
            refine ⟨319096065553903103354455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 425461420738537471139273 319096065553903103354455)
            ·
              refine ⟨478644098330854655031683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319096065553903103354455 478644098330854655031683)
              ·
                refine ⟨717966147496281982547525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478644098330854655031683 717966147496281982547525)
                ·
                  refine ⟨134618652655552871727661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717966147496281982547525 134618652655552871727661)
                  ·
                    refine ⟨50481994745832326897873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134618652655552871727661 50481994745832326897873)
                    ·
                      refine ⟨37861496059374245173405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50481994745832326897873 37861496059374245173405)
                      ·
                        rfl

theorem cell23_73735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_73735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73735 prefixEnd_73735 := by exact prefixLift 73735
  have htrace : WordTrace (prefixWord ++ tailWord_73735) baseStart_73735 baseEnd_73735 := by
    simpa [prefixWord, tailWord_73735, baseEnd_73735] using wordTrace_append hprefix tailTrace_73735
  have hstable : (prefixWord ++ tailWord_73735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73735).length < 2 ^ (prefixWord ++ tailWord_73735).sum := by decide
  have hdescent : baseEnd_73735 < baseStart_73735 := by decide
  rcases family_descends (prefixWord ++ tailWord_73735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73765 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 4]
def baseStart_73765 : Nat := 118140960795 + 73765 * 2 ^ 59
def prefixEnd_73765 : Nat := 4983230072969 + 3 ^ 40 * 73765 * 2
def baseEnd_73765 : Nat := 37876900479009127798267

theorem tailTrace_73765 : CollatzResearch.WordTrace tailWord_73765 prefixEnd_73765 37876900479009127798267 := by
  unfold tailWord_73765
  simp only [CollatzResearch.WordTrace]
  refine ⟨2690430577769477904126749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1793620385179651936084499 2690430577769477904126749)
  ·
    refine ⟨1008911466663554214047531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2690430577769477904126749 1008911466663554214047531)
    ·
      refine ⟨1513367199995331321071297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1008911466663554214047531 1513367199995331321071297)
      ·
        refine ⟨1135025399996498490803473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1513367199995331321071297 1135025399996498490803473)
        ·
          refine ⟨851269049997373868102605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1135025399996498490803473 851269049997373868102605)
          ·
            refine ⟨319225893749015200538477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 851269049997373868102605 319225893749015200538477)
            ·
              refine ⟨119709710155880700201929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 319225893749015200538477 119709710155880700201929)
              ·
                refine ⟨89782282616910525151447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119709710155880700201929 89782282616910525151447)
                ·
                  refine ⟨134673423925365787727171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89782282616910525151447 134673423925365787727171)
                  ·
                    refine ⟨202010135888048681590757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134673423925365787727171 202010135888048681590757)
                    ·
                      refine ⟨37876900479009127798267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 202010135888048681590757 37876900479009127798267)
                      ·
                        rfl

theorem cell23_73765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_73765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73765 prefixEnd_73765 := by exact prefixLift 73765
  have htrace : WordTrace (prefixWord ++ tailWord_73765) baseStart_73765 baseEnd_73765 := by
    simpa [prefixWord, tailWord_73765, baseEnd_73765] using wordTrace_append hprefix tailTrace_73765
  have hstable : (prefixWord ++ tailWord_73765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73765).length < 2 ^ (prefixWord ++ tailWord_73765).sum := by decide
  have hdescent : baseEnd_73765 < baseStart_73765 := by decide
  rcases family_descends (prefixWord ++ tailWord_73765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73778 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_73778 : Nat := 118140960795 + 73778 * 2 ^ 59
def prefixEnd_73778 : Nat := 4983230072969 + 3 ^ 40 * 73778 * 2
def baseEnd_73778 : Nat := 37883575727517576935707

theorem tailTrace_73778 : CollatzResearch.WordTrace tailWord_73778 prefixEnd_73778 37883575727517576935707 := by
  unfold tailWord_73778
  simp only [CollatzResearch.WordTrace]
  refine ⟨672726181680595281087497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1793936484481587416233325 672726181680595281087497)
  ·
    refine ⟨504544636260446460815623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 672726181680595281087497 504544636260446460815623)
    ·
      refine ⟨756816954390669691223435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 504544636260446460815623 756816954390669691223435)
      ·
        refine ⟨1135225431586004536835153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756816954390669691223435 1135225431586004536835153)
        ·
          refine ⟨851419073689503402626365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1135225431586004536835153 851419073689503402626365)
          ·
            refine ⟨319282152633563775984887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 851419073689503402626365 319282152633563775984887)
            ·
              refine ⟨478923228950345663977331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319282152633563775984887 478923228950345663977331)
              ·
                refine ⟨718384843425518495965997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478923228950345663977331 718384843425518495965997)
                ·
                  refine ⟨269394316284569435987249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718384843425518495965997 269394316284569435987249)
                  ·
                    refine ⟨202045737213427076990437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 269394316284569435987249 202045737213427076990437)
                    ·
                      refine ⟨37883575727517576935707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 202045737213427076990437 37883575727517576935707)
                      ·
                        rfl

theorem cell23_73778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_73778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73778 prefixEnd_73778 := by exact prefixLift 73778
  have htrace : WordTrace (prefixWord ++ tailWord_73778) baseStart_73778 baseEnd_73778 := by
    simpa [prefixWord, tailWord_73778, baseEnd_73778] using wordTrace_append hprefix tailTrace_73778
  have hstable : (prefixWord ++ tailWord_73778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73778).length < 2 ^ (prefixWord ++ tailWord_73778).sum := by decide
  have hdescent : baseEnd_73778 < baseStart_73778 := by decide
  rcases family_descends (prefixWord ++ tailWord_73778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73799 : List Nat := [1, 1, 4, 1, 3, 1, 3, 4, 1, 2, 2]
def baseStart_73799 : Nat := 118140960795 + 73799 * 2 ^ 59
def prefixEnd_73799 : Nat := 4983230072969 + 3 ^ 40 * 73799 * 2
def baseEnd_73799 : Nat := 37894358821261994773111

theorem tailTrace_73799 : CollatzResearch.WordTrace tailWord_73799 prefixEnd_73799 37894358821261994773111 := by
  unfold tailWord_73799
  simp only [CollatzResearch.WordTrace]
  refine ⟨2691670659646301710864451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1794447106430867807242967 2691670659646301710864451)
  ·
    refine ⟨4037505989469452566296677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2691670659646301710864451 4037505989469452566296677)
    ·
      refine ⟨757032373025522356180627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4037505989469452566296677 757032373025522356180627)
      ·
        refine ⟨1135548559538283534270941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 757032373025522356180627 1135548559538283534270941)
        ·
          refine ⟨425830709826856325351603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1135548559538283534270941 425830709826856325351603)
          ·
            refine ⟨638746064740284488027405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425830709826856325351603 638746064740284488027405)
            ·
              refine ⟨239529774277606683010277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 638746064740284488027405 239529774277606683010277)
              ·
                refine ⟨44911832677051253064427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239529774277606683010277 44911832677051253064427)
                ·
                  refine ⟨67367749015576879596641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44911832677051253064427 67367749015576879596641)
                  ·
                    refine ⟨50525811761682659697481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67367749015576879596641 50525811761682659697481)
                    ·
                      refine ⟨37894358821261994773111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50525811761682659697481 37894358821261994773111)
                      ·
                        rfl

theorem cell23_73799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_73799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73799 prefixEnd_73799 := by exact prefixLift 73799
  have htrace : WordTrace (prefixWord ++ tailWord_73799) baseStart_73799 baseEnd_73799 := by
    simpa [prefixWord, tailWord_73799, baseEnd_73799] using wordTrace_append hprefix tailTrace_73799
  have hstable : (prefixWord ++ tailWord_73799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73799).length < 2 ^ (prefixWord ++ tailWord_73799).sum := by decide
  have hdescent : baseEnd_73799 < baseStart_73799 := by decide
  rcases family_descends (prefixWord ++ tailWord_73799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73801 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 1, 9]
def baseStart_73801 : Nat := 118140960795 + 73801 * 2 ^ 59
def prefixEnd_73801 : Nat := 4983230072969 + 3 ^ 40 * 73801 * 2
def baseEnd_73801 : Nat := 12631795260856995649367

theorem tailTrace_73801 : CollatzResearch.WordTrace tailWord_73801 prefixEnd_73801 12631795260856995649367 := by
  unfold tailWord_73801
  simp only [CollatzResearch.WordTrace]
  refine ⟨2691743605639056052437257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1794495737092704034958171 2691743605639056052437257)
  ·
    refine ⟨2018807704229292039327943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2691743605639056052437257 2018807704229292039327943)
    ·
      refine ⟨3028211556343938058991915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2018807704229292039327943 3028211556343938058991915)
      ·
        refine ⟨4542317334515907088487873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3028211556343938058991915 4542317334515907088487873)
        ·
          refine ⟨3406738000886930316365905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4542317334515907088487873 3406738000886930316365905)
          ·
            refine ⟨2555053500665197737274429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3406738000886930316365905 2555053500665197737274429)
            ·
              refine ⟨958145062749449151477911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2555053500665197737274429 958145062749449151477911)
              ·
                refine ⟨1437217594124173727216867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958145062749449151477911 1437217594124173727216867)
                ·
                  refine ⟨2155826391186260590825301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437217594124173727216867 2155826391186260590825301)
                  ·
                    refine ⟨12631795260856995649367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2155826391186260590825301 12631795260856995649367)
                    ·
                      rfl

theorem cell23_73801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_73801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73801 prefixEnd_73801 := by exact prefixLift 73801
  have htrace : WordTrace (prefixWord ++ tailWord_73801) baseStart_73801 baseEnd_73801 := by
    simpa [prefixWord, tailWord_73801, baseEnd_73801] using wordTrace_append hprefix tailTrace_73801
  have hstable : (prefixWord ++ tailWord_73801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73801).length < 2 ^ (prefixWord ++ tailWord_73801).sum := by decide
  have hdescent : baseEnd_73801 < baseStart_73801 := by decide
  rcases family_descends (prefixWord ++ tailWord_73801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73849 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 2, 1, 3]
def baseStart_73849 : Nat := 118140960795 + 73849 * 2 ^ 59
def prefixEnd_73849 : Nat := 4983230072969 + 3 ^ 40 * 73849 * 2
def baseEnd_73849 : Nat := 37920032853986799147881

theorem tailTrace_73849 : CollatzResearch.WordTrace tailWord_73849 prefixEnd_73849 37920032853986799147881 := by
  unfold tailWord_73849
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693494309465160250184601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1795662872976773500123067 2693494309465160250184601)
  ·
    refine ⟨2020120732098870187638451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2693494309465160250184601 2020120732098870187638451)
    ·
      refine ⟨3030181098148305281457677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2020120732098870187638451 3030181098148305281457677)
      ·
        refine ⟨1136317911805614480546629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3030181098148305281457677 1136317911805614480546629)
        ·
          refine ⟨213059608463552715102493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1136317911805614480546629 213059608463552715102493)
          ·
            refine ⟨79897353173832268163435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213059608463552715102493 79897353173832268163435)
            ·
              refine ⟨119846029760748402245153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79897353173832268163435 119846029760748402245153)
              ·
                refine ⟨89884522320561301683865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119846029760748402245153 89884522320561301683865)
                ·
                  refine ⟨67413391740420976262899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89884522320561301683865 67413391740420976262899)
                  ·
                    refine ⟨101120087610631464394349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67413391740420976262899 101120087610631464394349)
                    ·
                      refine ⟨37920032853986799147881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 101120087610631464394349 37920032853986799147881)
                      ·
                        rfl

theorem cell23_73849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_73849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73849 prefixEnd_73849 := by exact prefixLift 73849
  have htrace : WordTrace (prefixWord ++ tailWord_73849) baseStart_73849 baseEnd_73849 := by
    simpa [prefixWord, tailWord_73849, baseEnd_73849] using wordTrace_append hprefix tailTrace_73849
  have hstable : (prefixWord ++ tailWord_73849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73849).length < 2 ^ (prefixWord ++ tailWord_73849).sum := by decide
  have hdescent : baseEnd_73849 < baseStart_73849 := by decide
  rcases family_descends (prefixWord ++ tailWord_73849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73912 : List Nat := [2, 1, 2, 1, 2, 1, 7, 2, 5]
def baseStart_73912 : Nat := 118140960795 + 73912 * 2 ^ 59
def prefixEnd_73912 : Nat := 4983230072969 + 3 ^ 40 * 73912 * 2
def baseEnd_73912 : Nat := 4216931348357783628899

theorem tailTrace_73912 : CollatzResearch.WordTrace tailWord_73912 prefixEnd_73912 4216931348357783628899 := by
  unfold tailWord_73912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1347896054118461004863995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1797194738824614673151993 1347896054118461004863995)
  ·
    refine ⟨2021844081177691507295993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1347896054118461004863995 2021844081177691507295993)
    ·
      refine ⟨1516383060883268630471995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2021844081177691507295993 1516383060883268630471995)
      ·
        refine ⟨2274574591324902945707993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1516383060883268630471995 2274574591324902945707993)
        ·
          refine ⟨1705930943493677209280995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2274574591324902945707993 1705930943493677209280995)
          ·
            refine ⟨2558896415240515813921493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705930943493677209280995 2558896415240515813921493)
            ·
              refine ⟨59974134732199589388785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2558896415240515813921493 59974134732199589388785)
              ·
                refine ⟨44980601049149692041589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59974134732199589388785 44980601049149692041589)
                ·
                  refine ⟨4216931348357783628899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44980601049149692041589 4216931348357783628899)
                  ·
                    rfl

theorem cell23_73912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 5].length) (baseStart_73912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73912 prefixEnd_73912 := by exact prefixLift 73912
  have htrace : WordTrace (prefixWord ++ tailWord_73912) baseStart_73912 baseEnd_73912 := by
    simpa [prefixWord, tailWord_73912, baseEnd_73912] using wordTrace_append hprefix tailTrace_73912
  have hstable : (prefixWord ++ tailWord_73912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73912).length < 2 ^ (prefixWord ++ tailWord_73912).sum := by decide
  have hdescent : baseEnd_73912 < baseStart_73912 := by decide
  rcases family_descends (prefixWord ++ tailWord_73912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73915 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 2, 5, 2]
def baseStart_73915 : Nat := 118140960795 + 73915 * 2 ^ 59
def prefixEnd_73915 : Nat := 4983230072969 + 3 ^ 40 * 73915 * 2
def baseEnd_73915 : Nat := 37953922577183540922577

theorem tailTrace_73915 : CollatzResearch.WordTrace tailWord_73915 prefixEnd_73915 37953922577183540922577 := by
  unfold tailWord_73915
  simp only [CollatzResearch.WordTrace]
  refine ⟨2695901527226053522087199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1797267684817369014724799 2695901527226053522087199)
  ·
    refine ⟨4043852290839080283130799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2695901527226053522087199 4043852290839080283130799)
    ·
      refine ⟨6065778436258620424696199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4043852290839080283130799 6065778436258620424696199)
      ·
        refine ⟨9098667654387930637044299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6065778436258620424696199 9098667654387930637044299)
        ·
          refine ⟨13648001481581895955566449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9098667654387930637044299 13648001481581895955566449)
          ·
            refine ⟨10236001111186421966674837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13648001481581895955566449 10236001111186421966674837)
            ·
              refine ⟨479812552086863529687883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10236001111186421966674837 479812552086863529687883)
              ·
                refine ⟨719718828130295294531825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479812552086863529687883 719718828130295294531825)
                ·
                  refine ⟨539789121097721470898869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 719718828130295294531825 539789121097721470898869)
                  ·
                    refine ⟨50605230102911387896769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 539789121097721470898869 50605230102911387896769)
                    ·
                      refine ⟨37953922577183540922577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50605230102911387896769 37953922577183540922577)
                      ·
                        rfl

theorem cell23_73915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 5, 2].length) (baseStart_73915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73915 prefixEnd_73915 := by exact prefixLift 73915
  have htrace : WordTrace (prefixWord ++ tailWord_73915) baseStart_73915 baseEnd_73915 := by
    simpa [prefixWord, tailWord_73915, baseEnd_73915] using wordTrace_append hprefix tailTrace_73915
  have hstable : (prefixWord ++ tailWord_73915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73915).length < 2 ^ (prefixWord ++ tailWord_73915).sum := by decide
  have hdescent : baseEnd_73915 < baseStart_73915 := by decide
  rcases family_descends (prefixWord ++ tailWord_73915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73945 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 4]
def baseStart_73945 : Nat := 118140960795 + 73945 * 2 ^ 59
def prefixEnd_73945 : Nat := 4983230072969 + 3 ^ 40 * 73945 * 2
def baseEnd_73945 : Nat := 37969326996818423547439

theorem tailTrace_73945 : CollatzResearch.WordTrace tailWord_73945 prefixEnd_73945 37969326996818423547439 := by
  unfold tailWord_73945
  simp only [CollatzResearch.WordTrace]
  refine ⟨2696995717117368645679289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1797997144744912430452859 2696995717117368645679289)
  ·
    refine ⟨2022746787838026484259467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2696995717117368645679289 2022746787838026484259467)
    ·
      refine ⟨3034120181757039726389201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2022746787838026484259467 3034120181757039726389201)
      ·
        refine ⟨2275590136317779794791901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3034120181757039726389201 2275590136317779794791901)
        ·
          refine ⟨853346301119167423046963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2275590136317779794791901 853346301119167423046963)
          ·
            refine ⟨1280019451678751134570445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853346301119167423046963 1280019451678751134570445)
            ·
              refine ⟨480007294379531675463917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1280019451678751134570445 480007294379531675463917)
              ·
                refine ⟨180002735392324378298969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 480007294379531675463917 180002735392324378298969)
                ·
                  refine ⟨135002051544243283724227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180002735392324378298969 135002051544243283724227)
                  ·
                    refine ⟨202503077316364925586341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 135002051544243283724227 202503077316364925586341)
                    ·
                      refine ⟨37969326996818423547439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 202503077316364925586341 37969326996818423547439)
                      ·
                        rfl

theorem cell23_73945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_73945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73945 prefixEnd_73945 := by exact prefixLift 73945
  have htrace : WordTrace (prefixWord ++ tailWord_73945) baseStart_73945 baseEnd_73945 := by
    simpa [prefixWord, tailWord_73945, baseEnd_73945] using wordTrace_append hprefix tailTrace_73945
  have hstable : (prefixWord ++ tailWord_73945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73945).length < 2 ^ (prefixWord ++ tailWord_73945).sum := by decide
  have hdescent : baseEnd_73945 < baseStart_73945 := by decide
  rcases family_descends (prefixWord ++ tailWord_73945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73962 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_73962 : Nat := 118140960795 + 73962 * 2 ^ 59
def prefixEnd_73962 : Nat := 4983230072969 + 3 ^ 40 * 73962 * 2
def baseEnd_73962 : Nat := 37978056167944857034861

theorem tailTrace_73962 : CollatzResearch.WordTrace tailWord_73962 prefixEnd_73962 37978056167944857034861 := by
  unfold tailWord_73962
  simp only [CollatzResearch.WordTrace]
  refine ⟨674403939513945137262035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1798410505370520366032093 674403939513945137262035)
  ·
    refine ⟨1011605909270917705893053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 674403939513945137262035 1011605909270917705893053)
    ·
      refine ⟨379352215976594139709895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1011605909270917705893053 379352215976594139709895)
      ·
        refine ⟨569028323964891209564843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379352215976594139709895 569028323964891209564843)
        ·
          refine ⟨853542485947336814347265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569028323964891209564843 853542485947336814347265)
          ·
            refine ⟨640156864460502610760449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 853542485947336814347265 640156864460502610760449)
            ·
              refine ⟨480117648345376958070337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640156864460502610760449 480117648345376958070337)
              ·
                refine ⟨360088236259032718552753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480117648345376958070337 360088236259032718552753)
                ·
                  refine ⟨270066177194274538914565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360088236259032718552753 270066177194274538914565)
                  ·
                    refine ⟨50637408223926476046481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270066177194274538914565 50637408223926476046481)
                    ·
                      refine ⟨37978056167944857034861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50637408223926476046481 37978056167944857034861)
                      ·
                        rfl

theorem cell23_73962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_73962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73962 prefixEnd_73962 := by exact prefixLift 73962
  have htrace : WordTrace (prefixWord ++ tailWord_73962) baseStart_73962 baseEnd_73962 := by
    simpa [prefixWord, tailWord_73962, baseEnd_73962] using wordTrace_append hprefix tailTrace_73962
  have hstable : (prefixWord ++ tailWord_73962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73962).length < 2 ^ (prefixWord ++ tailWord_73962).sum := by decide
  have hdescent : baseEnd_73962 < baseStart_73962 := by decide
  rcases family_descends (prefixWord ++ tailWord_73962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73968 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 8]
def baseStart_73968 : Nat := 118140960795 + 73968 * 2 ^ 59
def prefixEnd_73968 : Nat := 4983230072969 + 3 ^ 40 * 73968 * 2
def baseEnd_73968 : Nat := 4220126339096870395537

theorem tailTrace_73968 : CollatzResearch.WordTrace tailWord_73968 prefixEnd_73968 4220126339096870395537 := by
  unfold tailWord_73968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1348917298017021786883279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1798556397356029049177705 1348917298017021786883279)
  ·
    refine ⟨2023375947025532680324919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1348917298017021786883279 2023375947025532680324919)
    ·
      refine ⟨3035063920538299020487379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2023375947025532680324919 3035063920538299020487379)
      ·
        refine ⟨4552595880807448530731069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3035063920538299020487379 4552595880807448530731069)
        ·
          refine ⟨1707223455302793199024151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4552595880807448530731069 1707223455302793199024151)
          ·
            refine ⟨2560835182954189798536227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707223455302793199024151 2560835182954189798536227)
            ·
              refine ⟨3841252774431284697804341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560835182954189798536227 3841252774431284697804341)
              ·
                refine ⟨360117447602932940419157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3841252774431284697804341 360117447602932940419157)
                ·
                  refine ⟨4220126339096870395537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 360117447602932940419157 4220126339096870395537)
                  ·
                    rfl

theorem cell23_73968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 8].length) (baseStart_73968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73968 prefixEnd_73968 := by exact prefixLift 73968
  have htrace : WordTrace (prefixWord ++ tailWord_73968) baseStart_73968 baseEnd_73968 := by
    simpa [prefixWord, tailWord_73968, baseEnd_73968] using wordTrace_append hprefix tailTrace_73968
  have hstable : (prefixWord ++ tailWord_73968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73968).length < 2 ^ (prefixWord ++ tailWord_73968).sum := by decide
  have hdescent : baseEnd_73968 < baseStart_73968 := by decide
  rcases family_descends (prefixWord ++ tailWord_73968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73982 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_73982 : Nat := 118140960795 + 73982 * 2 ^ 59
def prefixEnd_73982 : Nat := 4983230072969 + 3 ^ 40 * 73982 * 2
def baseEnd_73982 : Nat := 37988325781034778784769

theorem tailTrace_73982 : CollatzResearch.WordTrace tailWord_73982 prefixEnd_73982 37988325781034778784769 := by
  unfold tailWord_73982
  simp only [CollatzResearch.WordTrace]
  refine ⟨337293152247915495597025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1798896811988882643184133 337293152247915495597025)
  ·
    refine ⟨252969864185936621697769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 337293152247915495597025 252969864185936621697769)
    ·
      refine ⟨189727398139452466273327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252969864185936621697769 189727398139452466273327)
      ·
        refine ⟨284591097209178699409991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189727398139452466273327 284591097209178699409991)
        ·
          refine ⟨426886645813768049114987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284591097209178699409991 426886645813768049114987)
          ·
            refine ⟨640329968720652073672481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426886645813768049114987 640329968720652073672481)
            ·
              refine ⟨480247476540489055254361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640329968720652073672481 480247476540489055254361)
              ·
                refine ⟨360185607405366791440771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480247476540489055254361 360185607405366791440771)
                ·
                  refine ⟨540278411108050187161157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360185607405366791440771 540278411108050187161157)
                  ·
                    refine ⟨101302202082759410092717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 540278411108050187161157 101302202082759410092717)
                    ·
                      refine ⟨37988325781034778784769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 101302202082759410092717 37988325781034778784769)
                      ·
                        rfl

theorem cell23_73982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_73982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73982 prefixEnd_73982 := by exact prefixLift 73982
  have htrace : WordTrace (prefixWord ++ tailWord_73982) baseStart_73982 baseEnd_73982 := by
    simpa [prefixWord, tailWord_73982, baseEnd_73982] using wordTrace_append hprefix tailTrace_73982
  have hstable : (prefixWord ++ tailWord_73982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73982).length < 2 ^ (prefixWord ++ tailWord_73982).sum := by decide
  have hdescent : baseEnd_73982 < baseStart_73982 := by decide
  rcases family_descends (prefixWord ++ tailWord_73982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73985 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 6]
def baseStart_73985 : Nat := 118140960795 + 73985 * 2 ^ 59
def prefixEnd_73985 : Nat := 4983230072969 + 3 ^ 40 * 73985 * 2
def baseEnd_73985 : Nat := 4221096246999807449695

theorem tailTrace_73985 : CollatzResearch.WordTrace tailWord_73985 prefixEnd_73985 4221096246999807449695 := by
  unfold tailWord_73985
  simp only [CollatzResearch.WordTrace]
  refine ⟨2698454636972455477135409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1798969757981636984756939 2698454636972455477135409)
  ·
    refine ⟨2023840977729341607851557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2698454636972455477135409 2023840977729341607851557)
    ·
      refine ⟨379470183324251551472167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2023840977729341607851557 379470183324251551472167)
      ·
        refine ⟨569205274986377327208251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379470183324251551472167 569205274986377327208251)
        ·
          refine ⟨853807912479565990812377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569205274986377327208251 853807912479565990812377)
          ·
            refine ⟨640355934359674493109283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 853807912479565990812377 640355934359674493109283)
            ·
              refine ⟨960533901539511739663925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640355934359674493109283 960533901539511739663925)
              ·
                refine ⟨90050053269329225593493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 960533901539511739663925 90050053269329225593493)
                ·
                  refine ⟨4221096246999807449695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90050053269329225593493 4221096246999807449695)
                  ·
                    rfl

theorem cell23_73985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 6].length) (baseStart_73985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_73985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_73985 prefixEnd_73985 := by exact prefixLift 73985
  have htrace : WordTrace (prefixWord ++ tailWord_73985) baseStart_73985 baseEnd_73985 := by
    simpa [prefixWord, tailWord_73985, baseEnd_73985] using wordTrace_append hprefix tailTrace_73985
  have hstable : (prefixWord ++ tailWord_73985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73985).length < 2 ^ (prefixWord ++ tailWord_73985).sum := by decide
  have hdescent : baseEnd_73985 < baseStart_73985 := by decide
  rcases family_descends (prefixWord ++ tailWord_73985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74012 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_74012 : Nat := 118140960795 + 74012 * 2 ^ 59
def prefixEnd_74012 : Nat := 4983230072969 + 3 ^ 40 * 74012 * 2
def baseEnd_74012 : Nat := 38003730200669661409631

theorem tailTrace_74012 : CollatzResearch.WordTrace tailWord_74012 prefixEnd_74012 38003730200669661409631 := by
  unfold tailWord_74012
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349719703937319544184145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1799626271916426058912193 1349719703937319544184145)
  ·
    refine ⟨1012289777952989658138109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1349719703937319544184145 1012289777952989658138109)
    ·
      refine ⟨379608666732371121801791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1012289777952989658138109 379608666732371121801791)
      ·
        refine ⟨569413000098556682702687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379608666732371121801791 569413000098556682702687)
        ·
          refine ⟨854119500147835024054031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569413000098556682702687 854119500147835024054031)
          ·
            refine ⟨1281179250221752536081047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854119500147835024054031 1281179250221752536081047)
            ·
              refine ⟨1921768875332628804121571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281179250221752536081047 1921768875332628804121571)
              ·
                refine ⟨2882653312998943206182357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921768875332628804121571 2882653312998943206182357)
                ·
                  refine ⟨67562187023412731394899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2882653312998943206182357 67562187023412731394899)
                  ·
                    refine ⟨101343280535119097092349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67562187023412731394899 101343280535119097092349)
                    ·
                      refine ⟨38003730200669661409631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 101343280535119097092349 38003730200669661409631)
                      ·
                        rfl

theorem cell23_74012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_74012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74012 prefixEnd_74012 := by exact prefixLift 74012
  have htrace : WordTrace (prefixWord ++ tailWord_74012) baseStart_74012 baseEnd_74012 := by
    simpa [prefixWord, tailWord_74012, baseEnd_74012] using wordTrace_append hprefix tailTrace_74012
  have hstable : (prefixWord ++ tailWord_74012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74012).length < 2 ^ (prefixWord ++ tailWord_74012).sum := by decide
  have hdescent : baseEnd_74012 < baseStart_74012 := by decide
  rcases family_descends (prefixWord ++ tailWord_74012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74023 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 3, 4]
def baseStart_74023 : Nat := 118140960795 + 74023 * 2 ^ 59
def prefixEnd_74023 : Nat := 4983230072969 + 3 ^ 40 * 74023 * 2
def baseEnd_74023 : Nat := 12669792829289706124027

theorem tailTrace_74023 : CollatzResearch.WordTrace tailWord_74023 prefixEnd_74023 12669792829289706124027 := by
  unfold tailWord_74023
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699840610834787967018723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1799893740556525311345815 2699840610834787967018723)
  ·
    refine ⟨4049760916252181950528085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2699840610834787967018723 4049760916252181950528085)
    ·
      refine ⟨47458135737330257232751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 4049760916252181950528085 47458135737330257232751)
      ·
        refine ⟨71187203605995385849127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47458135737330257232751 71187203605995385849127)
        ·
          refine ⟨106780805408993078773691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71187203605995385849127 106780805408993078773691)
          ·
            refine ⟨160171208113489618160537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106780805408993078773691 160171208113489618160537)
            ·
              refine ⟨120128406085117213620403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160171208113489618160537 120128406085117213620403)
              ·
                refine ⟨180192609127675820430605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120128406085117213620403 180192609127675820430605)
                ·
                  refine ⟨67572228422878432661477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180192609127675820430605 67572228422878432661477)
                  ·
                    refine ⟨12669792829289706124027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67572228422878432661477 12669792829289706124027)
                    ·
                      rfl

theorem cell23_74023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_74023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74023 prefixEnd_74023 := by exact prefixLift 74023
  have htrace : WordTrace (prefixWord ++ tailWord_74023) baseStart_74023 baseEnd_74023 := by
    simpa [prefixWord, tailWord_74023, baseEnd_74023] using wordTrace_append hprefix tailTrace_74023
  have hstable : (prefixWord ++ tailWord_74023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74023).length < 2 ^ (prefixWord ++ tailWord_74023).sum := by decide
  have hdescent : baseEnd_74023 < baseStart_74023 := by decide
  rcases family_descends (prefixWord ++ tailWord_74023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74055 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_74055 : Nat := 118140960795 + 74055 * 2 ^ 59
def prefixEnd_74055 : Nat := 4983230072969 + 3 ^ 40 * 74055 * 2
def baseEnd_74055 : Nat := 38025809868812993171933

theorem tailTrace_74055 : CollatzResearch.WordTrace tailWord_74055 prefixEnd_74055 38025809868812993171933 := by
  unfold tailWord_74055
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701007746718857432183619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1800671831145904954789079 2701007746718857432183619)
  ·
    refine ⟨4051511620078286148275429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2701007746718857432183619 4051511620078286148275429)
    ·
      refine ⟨759658428764678652801643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4051511620078286148275429 759658428764678652801643)
      ·
        refine ⟨1139487643147017979202465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759658428764678652801643 1139487643147017979202465)
        ·
          refine ⟨854615732360263484401849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1139487643147017979202465 854615732360263484401849)
          ·
            refine ⟨640961799270197613301387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 854615732360263484401849 640961799270197613301387)
            ·
              refine ⟨961442698905296419952081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640961799270197613301387 961442698905296419952081)
              ·
                refine ⟨721082024178972314964061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961442698905296419952081 721082024178972314964061)
                ·
                  refine ⟨270405759067114618111523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721082024178972314964061 270405759067114618111523)
                  ·
                    refine ⟨405608638600671927167285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 270405759067114618111523 405608638600671927167285)
                    ·
                      refine ⟨38025809868812993171933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 405608638600671927167285 38025809868812993171933)
                      ·
                        rfl

theorem cell23_74055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_74055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74055 prefixEnd_74055 := by exact prefixLift 74055
  have htrace : WordTrace (prefixWord ++ tailWord_74055) baseStart_74055 baseEnd_74055 := by
    simpa [prefixWord, tailWord_74055, baseEnd_74055] using wordTrace_append hprefix tailTrace_74055
  have hstable : (prefixWord ++ tailWord_74055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74055).length < 2 ^ (prefixWord ++ tailWord_74055).sum := by decide
  have hdescent : baseEnd_74055 < baseStart_74055 := by decide
  rcases family_descends (prefixWord ++ tailWord_74055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74082 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_74082 : Nat := 118140960795 + 74082 * 2 ^ 59
def prefixEnd_74082 : Nat := 4983230072969 + 3 ^ 40 * 74082 * 2
def baseEnd_74082 : Nat := 38039673846484387534309

theorem tailTrace_74082 : CollatzResearch.WordTrace tailWord_74082 prefixEnd_74082 38039673846484387534309 := by
  unfold tailWord_74082
  simp only [CollatzResearch.WordTrace]
  refine ⟨675498129405260260854125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1801328345080694028944333 675498129405260260854125)
  ·
    refine ⟨253311798526972597820297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 675498129405260260854125 253311798526972597820297)
    ·
      refine ⟨189983848895229448365223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253311798526972597820297 189983848895229448365223)
      ·
        refine ⟨284975773342844172547835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189983848895229448365223 284975773342844172547835)
        ·
          refine ⟨427463660014266258821753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284975773342844172547835 427463660014266258821753)
          ·
            refine ⟨320597745010699694116315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427463660014266258821753 320597745010699694116315)
            ·
              refine ⟨480896617516049541174473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320597745010699694116315 480896617516049541174473)
              ·
                refine ⟨360672463137037155880855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480896617516049541174473 360672463137037155880855)
                ·
                  refine ⟨541008694705555733821283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360672463137037155880855 541008694705555733821283)
                  ·
                    refine ⟨811513042058333600731925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 541008694705555733821283 811513042058333600731925)
                    ·
                      refine ⟨38039673846484387534309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 811513042058333600731925 38039673846484387534309)
                      ·
                        rfl

theorem cell23_74082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_74082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74082 prefixEnd_74082 := by exact prefixLift 74082
  have htrace : WordTrace (prefixWord ++ tailWord_74082) baseStart_74082 baseEnd_74082 := by
    simpa [prefixWord, tailWord_74082, baseEnd_74082] using wordTrace_append hprefix tailTrace_74082
  have hstable : (prefixWord ++ tailWord_74082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74082).length < 2 ^ (prefixWord ++ tailWord_74082).sum := by decide
  have hdescent : baseEnd_74082 < baseStart_74082 := by decide
  rcases family_descends (prefixWord ++ tailWord_74082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74092 : List Nat := [2, 2, 1, 1, 6, 1, 2, 8]
def baseStart_74092 : Nat := 118140960795 + 74092 * 2 ^ 59
def prefixEnd_74092 : Nat := 4983230072969 + 3 ^ 40 * 74092 * 2
def baseEnd_74092 : Nat := 1409066987149235126269

theorem tailTrace_74092 : CollatzResearch.WordTrace tailWord_74092 prefixEnd_74092 1409066987149235126269 := by
  unfold tailWord_74092
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351178623792406375640265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1801571498389875167520353 1351178623792406375640265)
  ·
    refine ⟨1013383967844304781730199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1351178623792406375640265 1013383967844304781730199)
    ·
      refine ⟨1520075951766457172595299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1013383967844304781730199 1520075951766457172595299)
      ·
        refine ⟨2280113927649685758892949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520075951766457172595299 2280113927649685758892949)
        ·
          refine ⟨106880340358579019948107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2280113927649685758892949 106880340358579019948107)
          ·
            refine ⟨160320510537868529922161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106880340358579019948107 160320510537868529922161)
            ·
              refine ⟨120240382903401397441621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160320510537868529922161 120240382903401397441621)
              ·
                refine ⟨1409066987149235126269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 120240382903401397441621 1409066987149235126269)
                ·
                  rfl

theorem cell23_74092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 8].length) (baseStart_74092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74092 prefixEnd_74092 := by exact prefixLift 74092
  have htrace : WordTrace (prefixWord ++ tailWord_74092) baseStart_74092 baseEnd_74092 := by
    simpa [prefixWord, tailWord_74092, baseEnd_74092] using wordTrace_append hprefix tailTrace_74092
  have hstable : (prefixWord ++ tailWord_74092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74092).length < 2 ^ (prefixWord ++ tailWord_74092).sum := by decide
  have hdescent : baseEnd_74092 < baseStart_74092 := by decide
  rcases family_descends (prefixWord ++ tailWord_74092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74096 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 2, 4]
def baseStart_74096 : Nat := 118140960795 + 74096 * 2 ^ 59
def prefixEnd_74096 : Nat := 4983230072969 + 3 ^ 40 * 74096 * 2
def baseEnd_74096 : Nat := 12682287525215777586415

theorem tailTrace_74096 : CollatzResearch.WordTrace tailWord_74096 prefixEnd_74096 12682287525215777586415 := by
  unfold tailWord_74096
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351251569785160717213071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1801668759713547622950761 1351251569785160717213071)
  ·
    refine ⟨2026877354677741075819607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1351251569785160717213071 2026877354677741075819607)
    ·
      refine ⟨3040316032016611613729411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2026877354677741075819607 3040316032016611613729411)
      ·
        refine ⟨4560474048024917420594117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040316032016611613729411 4560474048024917420594117)
        ·
          refine ⟨855088884004672016361397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4560474048024917420594117 855088884004672016361397)
          ·
            refine ⟨80164582875438001533881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 855088884004672016361397 80164582875438001533881)
            ·
              refine ⟨60123437156578501150411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80164582875438001533881 60123437156578501150411)
              ·
                refine ⟨90185155734867751725617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60123437156578501150411 90185155734867751725617)
                ·
                  refine ⟨67638866801150813794213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90185155734867751725617 67638866801150813794213)
                  ·
                    refine ⟨12682287525215777586415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67638866801150813794213 12682287525215777586415)
                    ·
                      rfl

theorem cell23_74096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 2, 4].length) (baseStart_74096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74096 prefixEnd_74096 := by exact prefixLift 74096
  have htrace : WordTrace (prefixWord ++ tailWord_74096) baseStart_74096 baseEnd_74096 := by
    simpa [prefixWord, tailWord_74096, baseEnd_74096] using wordTrace_append hprefix tailTrace_74096
  have hstable : (prefixWord ++ tailWord_74096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74096).length < 2 ^ (prefixWord ++ tailWord_74096).sum := by decide
  have hdescent : baseEnd_74096 < baseStart_74096 := by decide
  rcases family_descends (prefixWord ++ tailWord_74096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74136 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 2, 1, 3]
def baseStart_74136 : Nat := 118140960795 + 74136 * 2 ^ 59
def prefixEnd_74136 : Nat := 4983230072969 + 3 ^ 40 * 74136 * 2
def baseEnd_74136 : Nat := 38067401801827176259061

theorem tailTrace_74136 : CollatzResearch.WordTrace tailWord_74136 prefixEnd_74136 38067401801827176259061 := by
  unfold tailWord_74136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351981029712704132941131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1802641372950272177254841 1351981029712704132941131)
  ·
    refine ⟨2027971544569056199411697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1351981029712704132941131 2027971544569056199411697)
    ·
      refine ⟨1520978658426792149558773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2027971544569056199411697 1520978658426792149558773)
      ·
        refine ⟨142591749227511764021135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1520978658426792149558773 142591749227511764021135)
        ·
          refine ⟨213887623841267646031703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142591749227511764021135 213887623841267646031703)
          ·
            refine ⟨320831435761901469047555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213887623841267646031703 320831435761901469047555)
            ·
              refine ⟨481247153642852203571333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320831435761901469047555 481247153642852203571333)
              ·
                refine ⟨90233841308034788169625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 481247153642852203571333 90233841308034788169625)
                ·
                  refine ⟨67675380981026091127219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90233841308034788169625 67675380981026091127219)
                  ·
                    refine ⟨101513071471539136690829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67675380981026091127219 101513071471539136690829)
                    ·
                      refine ⟨38067401801827176259061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 101513071471539136690829 38067401801827176259061)
                      ·
                        rfl

theorem cell23_74136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_74136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74136 prefixEnd_74136 := by exact prefixLift 74136
  have htrace : WordTrace (prefixWord ++ tailWord_74136) baseStart_74136 baseEnd_74136 := by
    simpa [prefixWord, tailWord_74136, baseEnd_74136] using wordTrace_append hprefix tailTrace_74136
  have hstable : (prefixWord ++ tailWord_74136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74136).length < 2 ^ (prefixWord ++ tailWord_74136).sum := by decide
  have hdescent : baseEnd_74136 < baseStart_74136 := by decide
  rcases family_descends (prefixWord ++ tailWord_74136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74159 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 8, 2, 2]
def baseStart_74159 : Nat := 118140960795 + 74159 * 2 ^ 59
def prefixEnd_74159 : Nat := 4983230072969 + 3 ^ 40 * 74159 * 2
def baseEnd_74159 : Nat := 38079211856880586271455

theorem tailTrace_74159 : CollatzResearch.WordTrace tailWord_74159 prefixEnd_74159 38079211856880586271455 := by
  unfold tailWord_74159
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704800938342083193969531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1803200625561388795979687 2704800938342083193969531)
  ·
    refine ⟨4057201407513124790954297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2704800938342083193969531 4057201407513124790954297)
    ·
      refine ⟨3042901055634843593215723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4057201407513124790954297 3042901055634843593215723)
      ·
        refine ⟨4564351583452265389823585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3042901055634843593215723 4564351583452265389823585)
        ·
          refine ⟨3423263687589199042367689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4564351583452265389823585 3423263687589199042367689)
          ·
            refine ⟨2567447765691899281775767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3423263687589199042367689 2567447765691899281775767)
            ·
              refine ⟨3851171648537848922663651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567447765691899281775767 3851171648537848922663651)
              ·
                refine ⟨5776757472806773383995477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3851171648537848922663651 5776757472806773383995477)
                ·
                  refine ⟨67696376634454375593697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5776757472806773383995477 67696376634454375593697)
                  ·
                    refine ⟨50772282475840781695273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67696376634454375593697 50772282475840781695273)
                    ·
                      refine ⟨38079211856880586271455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50772282475840781695273 38079211856880586271455)
                      ·
                        rfl

theorem cell23_74159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 2, 2].length) (baseStart_74159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74159 prefixEnd_74159 := by exact prefixLift 74159
  have htrace : WordTrace (prefixWord ++ tailWord_74159) baseStart_74159 baseEnd_74159 := by
    simpa [prefixWord, tailWord_74159, baseEnd_74159] using wordTrace_append hprefix tailTrace_74159
  have hstable : (prefixWord ++ tailWord_74159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74159).length < 2 ^ (prefixWord ++ tailWord_74159).sum := by decide
  have hdescent : baseEnd_74159 < baseStart_74159 := by decide
  rcases family_descends (prefixWord ++ tailWord_74159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74162 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_74162 : Nat := 118140960795 + 74162 * 2 ^ 59
def prefixEnd_74162 : Nat := 4983230072969 + 3 ^ 40 * 74162 * 2
def baseEnd_74162 : Nat := 38080752298844074533941

theorem tailTrace_74162 : CollatzResearch.WordTrace tailWord_74162 prefixEnd_74162 38080752298844074533941 := by
  unfold tailWord_74162
  simp only [CollatzResearch.WordTrace]
  refine ⟨676227589332803676582185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1803273571554143137552493 676227589332803676582185)
  ·
    refine ⟨507170691999602757436639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 676227589332803676582185 507170691999602757436639)
    ·
      refine ⟨760756037999404136154959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 507170691999602757436639 760756037999404136154959)
      ·
        refine ⟨1141134056999106204232439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760756037999404136154959 1141134056999106204232439)
        ·
          refine ⟨1711701085498659306348659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1141134056999106204232439 1711701085498659306348659)
          ·
            refine ⟨2567551628247988959522989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711701085498659306348659 2567551628247988959522989)
            ·
              refine ⟨962831860592995859821121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2567551628247988959522989 962831860592995859821121)
              ·
                refine ⟨722123895444746894865841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962831860592995859821121 722123895444746894865841)
                ·
                  refine ⟨541592921583560171149381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 722123895444746894865841 541592921583560171149381)
                  ·
                    refine ⟨101548672796917532090509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 541592921583560171149381 101548672796917532090509)
                    ·
                      refine ⟨38080752298844074533941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 101548672796917532090509 38080752298844074533941)
                      ·
                        rfl

theorem cell23_74162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_74162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74162 prefixEnd_74162 := by exact prefixLift 74162
  have htrace : WordTrace (prefixWord ++ tailWord_74162) baseStart_74162 baseEnd_74162 := by
    simpa [prefixWord, tailWord_74162, baseEnd_74162] using wordTrace_append hprefix tailTrace_74162
  have hstable : (prefixWord ++ tailWord_74162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74162).length < 2 ^ (prefixWord ++ tailWord_74162).sum := by decide
  have hdescent : baseEnd_74162 < baseStart_74162 := by decide
  rcases family_descends (prefixWord ++ tailWord_74162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74175 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_74175 : Nat := 118140960795 + 74175 * 2 ^ 59
def prefixEnd_74175 : Nat := 4983230072969 + 3 ^ 40 * 74175 * 2
def baseEnd_74175 : Nat := 38087427547352523671381

theorem tailTrace_74175 : CollatzResearch.WordTrace tailWord_74175 prefixEnd_74175 38087427547352523671381 := by
  unfold tailWord_74175
  simp only [CollatzResearch.WordTrace]
  refine ⟨2705384506284117926551979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1803589670856078617701319 2705384506284117926551979)
  ·
    refine ⟨4058076759426176889827969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2705384506284117926551979 4058076759426176889827969)
    ·
      refine ⟨3043557569569632667370977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4058076759426176889827969 3043557569569632667370977)
      ·
        refine ⟨2282668177177224500528233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3043557569569632667370977 2282668177177224500528233)
        ·
          refine ⟨1712001132882918375396175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2282668177177224500528233 1712001132882918375396175)
          ·
            refine ⟨2568001699324377563094263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712001132882918375396175 2568001699324377563094263)
            ·
              refine ⟨3852002548986566344641395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2568001699324377563094263 3852002548986566344641395)
              ·
                refine ⟨5778003823479849516962093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3852002548986566344641395 5778003823479849516962093)
                ·
                  refine ⟨2166751433804943568860785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5778003823479849516962093 2166751433804943568860785)
                  ·
                    refine ⟨1625063575353707676645589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2166751433804943568860785 1625063575353707676645589)
                    ·
                      refine ⟨38087427547352523671381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1625063575353707676645589 38087427547352523671381)
                      ·
                        rfl

theorem cell23_74175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_74175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74175 prefixEnd_74175 := by exact prefixLift 74175
  have htrace : WordTrace (prefixWord ++ tailWord_74175) baseStart_74175 baseEnd_74175 := by
    simpa [prefixWord, tailWord_74175, baseEnd_74175] using wordTrace_append hprefix tailTrace_74175
  have hstable : (prefixWord ++ tailWord_74175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74175).length < 2 ^ (prefixWord ++ tailWord_74175).sum := by decide
  have hdescent : baseEnd_74175 < baseStart_74175 := by decide
  rcases family_descends (prefixWord ++ tailWord_74175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74232 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_74232 : Nat := 118140960795 + 74232 * 2 ^ 59
def prefixEnd_74232 : Nat := 4983230072969 + 3 ^ 40 * 74232 * 2
def baseEnd_74232 : Nat := 38116695944658800658619

theorem tailTrace_74232 : CollatzResearch.WordTrace tailWord_74232 prefixEnd_74232 38116695944658800658619 := by
  unfold tailWord_74232
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353731733538808330688475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1804975644718411107584633 1353731733538808330688475)
  ·
    refine ⟨2030597600308212496032713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1353731733538808330688475 2030597600308212496032713)
    ·
      refine ⟨1522948200231159372024535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2030597600308212496032713 1522948200231159372024535)
      ·
        refine ⟨2284422300346739058036803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522948200231159372024535 2284422300346739058036803)
        ·
          refine ⟨3426633450520108587055205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2284422300346739058036803 3426633450520108587055205)
          ·
            refine ⟨642493771972520360072851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3426633450520108587055205 642493771972520360072851)
            ·
              refine ⟨963740657958780540109277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642493771972520360072851 963740657958780540109277)
              ·
                refine ⟨361402746734542702540979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 963740657958780540109277 361402746734542702540979)
                ·
                  refine ⟨542104120101814053811469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361402746734542702540979 542104120101814053811469)
                  ·
                    refine ⟨203289045038180270179301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 542104120101814053811469 203289045038180270179301)
                    ·
                      refine ⟨38116695944658800658619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 203289045038180270179301 38116695944658800658619)
                      ·
                        rfl

theorem cell23_74232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_74232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74232 prefixEnd_74232 := by exact prefixLift 74232
  have htrace : WordTrace (prefixWord ++ tailWord_74232) baseStart_74232 baseEnd_74232 := by
    simpa [prefixWord, tailWord_74232, baseEnd_74232] using wordTrace_append hprefix tailTrace_74232
  have hstable : (prefixWord ++ tailWord_74232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74232).length < 2 ^ (prefixWord ++ tailWord_74232).sum := by decide
  have hdescent : baseEnd_74232 < baseStart_74232 := by decide
  rcases family_descends (prefixWord ++ tailWord_74232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74249 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 2, 4, 2]
def baseStart_74249 : Nat := 118140960795 + 74249 * 2 ^ 59
def prefixEnd_74249 : Nat := 4983230072969 + 3 ^ 40 * 74249 * 2
def baseEnd_74249 : Nat := 38125425115785234146041

theorem tailTrace_74249 : CollatzResearch.WordTrace tailWord_74249 prefixEnd_74249 38125425115785234146041 := by
  unfold tailWord_74249
  simp only [CollatzResearch.WordTrace]
  refine ⟨2708083508016028564745801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1805389005344019043163867 2708083508016028564745801)
  ·
    refine ⟨2031062631012021423559351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2708083508016028564745801 2031062631012021423559351)
    ·
      refine ⟨3046593946518032135339027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2031062631012021423559351 3046593946518032135339027)
      ·
        refine ⟨4569890919777048203008541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3046593946518032135339027 4569890919777048203008541)
        ·
          refine ⟨1713709094916393076128203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4569890919777048203008541 1713709094916393076128203)
          ·
            refine ⟨2570563642374589614192305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713709094916393076128203 2570563642374589614192305)
            ·
              refine ⟨1927922731780942210644229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2570563642374589614192305 1927922731780942210644229)
              ·
                refine ⟨361485512208926664495793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1927922731780942210644229 361485512208926664495793)
                ·
                  refine ⟨271114134156694998371845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361485512208926664495793 271114134156694998371845)
                  ·
                    refine ⟨50833900154380312194721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 271114134156694998371845 50833900154380312194721)
                    ·
                      refine ⟨38125425115785234146041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50833900154380312194721 38125425115785234146041)
                      ·
                        rfl

theorem cell23_74249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 4, 2].length) (baseStart_74249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74249 prefixEnd_74249 := by exact prefixLift 74249
  have htrace : WordTrace (prefixWord ++ tailWord_74249) baseStart_74249 baseEnd_74249 := by
    simpa [prefixWord, tailWord_74249, baseEnd_74249] using wordTrace_append hprefix tailTrace_74249
  have hstable : (prefixWord ++ tailWord_74249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74249).length < 2 ^ (prefixWord ++ tailWord_74249).sum := by decide
  have hdescent : baseEnd_74249 < baseStart_74249 := by decide
  rcases family_descends (prefixWord ++ tailWord_74249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74312 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_74312 : Nat := 118140960795 + 74312 * 2 ^ 59
def prefixEnd_74312 : Nat := 4983230072969 + 3 ^ 40 * 74312 * 2
def baseEnd_74312 : Nat := 38157774397018487658251

theorem tailTrace_74312 : CollatzResearch.WordTrace tailWord_74312 prefixEnd_74312 38157774397018487658251 := by
  unfold tailWord_74312
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355190653393895162144595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1806920871191860216192793 1355190653393895162144595)
  ·
    refine ⟨2032785980090842743216893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1355190653393895162144595 2032785980090842743216893)
    ·
      refine ⟨762294742534066028706335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2032785980090842743216893 762294742534066028706335)
      ·
        refine ⟨1143442113801099043059503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762294742534066028706335 1143442113801099043059503)
        ·
          refine ⟨1715163170701648564589255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143442113801099043059503 1715163170701648564589255)
          ·
            refine ⟨2572744756052472846883883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715163170701648564589255 2572744756052472846883883)
            ·
              refine ⟨3859117134078709270325825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2572744756052472846883883 3859117134078709270325825)
              ·
                refine ⟨2894337850559031952744369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3859117134078709270325825 2894337850559031952744369)
                ·
                  refine ⟨2170753387919273964558277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2894337850559031952744369 2170753387919273964558277)
                  ·
                    refine ⟨407016260234863868354677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2170753387919273964558277 407016260234863868354677)
                    ·
                      refine ⟨38157774397018487658251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 407016260234863868354677 38157774397018487658251)
                      ·
                        rfl

theorem cell23_74312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_74312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74312 prefixEnd_74312 := by exact prefixLift 74312
  have htrace : WordTrace (prefixWord ++ tailWord_74312) baseStart_74312 baseEnd_74312 := by
    simpa [prefixWord, tailWord_74312, baseEnd_74312] using wordTrace_append hprefix tailTrace_74312
  have hstable : (prefixWord ++ tailWord_74312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74312).length < 2 ^ (prefixWord ++ tailWord_74312).sum := by decide
  have hdescent : baseEnd_74312 < baseStart_74312 := by decide
  rcases family_descends (prefixWord ++ tailWord_74312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74316 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 3, 1, 3]
def baseStart_74316 : Nat := 118140960795 + 74316 * 2 ^ 59
def prefixEnd_74316 : Nat := 4983230072969 + 3 ^ 40 * 74316 * 2
def baseEnd_74316 : Nat := 38159828319636472008233

theorem tailTrace_74316 : CollatzResearch.WordTrace tailWord_74316 prefixEnd_74316 38159828319636472008233 := by
  unfold tailWord_74316
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355263599386649503717401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1807018132515532671623201 1355263599386649503717401)
  ·
    refine ⟨1016447699539987127788051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1355263599386649503717401 1016447699539987127788051)
    ·
      refine ⟨1524671549309980691682077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1016447699539987127788051 1524671549309980691682077)
      ·
        refine ⟨571751830991242759380779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1524671549309980691682077 571751830991242759380779)
        ·
          refine ⟨857627746486864139071169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571751830991242759380779 857627746486864139071169)
          ·
            refine ⟨643220809865148104303377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 857627746486864139071169 643220809865148104303377)
            ·
              refine ⟨482415607398861078227533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643220809865148104303377 482415607398861078227533)
              ·
                refine ⟨180905852774572904335325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 482415607398861078227533 180905852774572904335325)
                ·
                  refine ⟨67839694790464839125747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180905852774572904335325 67839694790464839125747)
                  ·
                    refine ⟨101759542185697258688621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67839694790464839125747 101759542185697258688621)
                    ·
                      refine ⟨38159828319636472008233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 101759542185697258688621 38159828319636472008233)
                      ·
                        rfl

theorem cell23_74316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_74316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74316 prefixEnd_74316 := by exact prefixLift 74316
  have htrace : WordTrace (prefixWord ++ tailWord_74316) baseStart_74316 baseEnd_74316 := by
    simpa [prefixWord, tailWord_74316, baseEnd_74316] using wordTrace_append hprefix tailTrace_74316
  have hstable : (prefixWord ++ tailWord_74316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74316).length < 2 ^ (prefixWord ++ tailWord_74316).sum := by decide
  have hdescent : baseEnd_74316 < baseStart_74316 := by decide
  rcases family_descends (prefixWord ++ tailWord_74316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74334 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_74334 : Nat := 118140960795 + 74334 * 2 ^ 59
def prefixEnd_74334 : Nat := 4983230072969 + 3 ^ 40 * 74334 * 2
def baseEnd_74334 : Nat := 38169070971417401583151

theorem tailTrace_74334 : CollatzResearch.WordTrace tailWord_74334 prefixEnd_74334 38169070971417401583151 := by
  unfold tailWord_74334
  simp only [CollatzResearch.WordTrace]
  refine ⟨338897964088511010198757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1807455808472058721060037 338897964088511010198757)
  ·
    refine ⟨63543368266595814412267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 338897964088511010198757 63543368266595814412267)
    ·
      refine ⟨95315052399893721618401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63543368266595814412267 95315052399893721618401)
      ·
        refine ⟨71486289299920291213801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95315052399893721618401 71486289299920291213801)
        ·
          refine ⟨53614716974940218410351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71486289299920291213801 53614716974940218410351)
          ·
            refine ⟨80422075462410327615527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53614716974940218410351 80422075462410327615527)
            ·
              refine ⟨120633113193615491423291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80422075462410327615527 120633113193615491423291)
              ·
                refine ⟨180949669790423237134937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120633113193615491423291 180949669790423237134937)
                ·
                  refine ⟨135712252342817427851203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180949669790423237134937 135712252342817427851203)
                  ·
                    refine ⟨203568378514226141776805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 135712252342817427851203 203568378514226141776805)
                    ·
                      refine ⟨38169070971417401583151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 203568378514226141776805 38169070971417401583151)
                      ·
                        rfl

theorem cell23_74334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_74334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74334 prefixEnd_74334 := by exact prefixLift 74334
  have htrace : WordTrace (prefixWord ++ tailWord_74334) baseStart_74334 baseEnd_74334 := by
    simpa [prefixWord, tailWord_74334, baseEnd_74334] using wordTrace_append hprefix tailTrace_74334
  have hstable : (prefixWord ++ tailWord_74334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74334).length < 2 ^ (prefixWord ++ tailWord_74334).sum := by decide
  have hdescent : baseEnd_74334 < baseStart_74334 := by decide
  rcases family_descends (prefixWord ++ tailWord_74334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74339 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 4]
def baseStart_74339 : Nat := 118140960795 + 74339 * 2 ^ 59
def prefixEnd_74339 : Nat := 4983230072969 + 3 ^ 40 * 74339 * 2
def baseEnd_74339 : Nat := 38171638374689882020627

theorem tailTrace_74339 : CollatzResearch.WordTrace tailWord_74339 prefixEnd_74339 38171638374689882020627 := by
  unfold tailWord_74339
  simp only [CollatzResearch.WordTrace]
  refine ⟨2711366077689973935522071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1807577385126649290348047 2711366077689973935522071)
  ·
    refine ⟨4067049116534960903283107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2711366077689973935522071 4067049116534960903283107)
    ·
      refine ⟨6100573674802441354924661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4067049116534960903283107 6100573674802441354924661)
      ·
        refine ⟨571928782012728877024187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6100573674802441354924661 571928782012728877024187)
        ·
          refine ⟨857893173019093315536281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571928782012728877024187 857893173019093315536281)
          ·
            refine ⟨643419879764319986652211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 857893173019093315536281 643419879764319986652211)
            ·
              refine ⟨965129819646479979978317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643419879764319986652211 965129819646479979978317)
              ·
                refine ⟨361923682367429992491869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 965129819646479979978317 361923682367429992491869)
                ·
                  refine ⟨135721380887786247184451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361923682367429992491869 135721380887786247184451)
                  ·
                    refine ⟨203582071331679370776677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 135721380887786247184451 203582071331679370776677)
                    ·
                      refine ⟨38171638374689882020627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 203582071331679370776677 38171638374689882020627)
                      ·
                        rfl

theorem cell23_74339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_74339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74339 prefixEnd_74339 := by exact prefixLift 74339
  have htrace : WordTrace (prefixWord ++ tailWord_74339) baseStart_74339 baseEnd_74339 := by
    simpa [prefixWord, tailWord_74339, baseEnd_74339] using wordTrace_append hprefix tailTrace_74339
  have hstable : (prefixWord ++ tailWord_74339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74339).length < 2 ^ (prefixWord ++ tailWord_74339).sum := by decide
  have hdescent : baseEnd_74339 < baseStart_74339 := by decide
  rcases family_descends (prefixWord ++ tailWord_74339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74350 : List Nat := [4, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_74350 : Nat := 118140960795 + 74350 * 2 ^ 59
def prefixEnd_74350 : Nat := 4983230072969 + 3 ^ 40 * 74350 * 2
def baseEnd_74350 : Nat := 38177286661889338983077

theorem tailTrace_74350 : CollatzResearch.WordTrace tailWord_74350 prefixEnd_74350 38177286661889338983077 := by
  unfold tailWord_74350
  simp only [CollatzResearch.WordTrace]
  refine ⟨338970910081265351771563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1807844853766748542781669 338970910081265351771563)
  ·
    refine ⟨508456365121898027657345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 338970910081265351771563 508456365121898027657345)
    ·
      refine ⟨381342273841423520743009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 508456365121898027657345 381342273841423520743009)
      ·
        refine ⟨286006705381067640557257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381342273841423520743009 286006705381067640557257)
        ·
          refine ⟨214505029035800730417943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286006705381067640557257 214505029035800730417943)
          ·
            refine ⟨321757543553701095626915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214505029035800730417943 321757543553701095626915)
            ·
              refine ⟨482636315330551643440373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321757543553701095626915 482636315330551643440373)
              ·
                refine ⟨45247154562239216572535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 482636315330551643440373 45247154562239216572535)
                ·
                  refine ⟨67870731843358824858803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45247154562239216572535 67870731843358824858803)
                  ·
                    refine ⟨101806097765038237288205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67870731843358824858803 101806097765038237288205)
                    ·
                      refine ⟨38177286661889338983077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 101806097765038237288205 38177286661889338983077)
                      ·
                        rfl

theorem cell23_74350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_74350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74350 prefixEnd_74350 := by exact prefixLift 74350
  have htrace : WordTrace (prefixWord ++ tailWord_74350) baseStart_74350 baseEnd_74350 := by
    simpa [prefixWord, tailWord_74350, baseEnd_74350] using wordTrace_append hprefix tailTrace_74350
  have hstable : (prefixWord ++ tailWord_74350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74350).length < 2 ^ (prefixWord ++ tailWord_74350).sum := by decide
  have hdescent : baseEnd_74350 < baseStart_74350 := by decide
  rcases family_descends (prefixWord ++ tailWord_74350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74369 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_74369 : Nat := 118140960795 + 74369 * 2 ^ 59
def prefixEnd_74369 : Nat := 4983230072969 + 3 ^ 40 * 74369 * 2
def baseEnd_74369 : Nat := 38187042794324764645489

theorem tailTrace_74369 : CollatzResearch.WordTrace tailWord_74369 prefixEnd_74369 38187042794324764645489 := by
  unfold tailWord_74369
  simp only [CollatzResearch.WordTrace]
  refine ⟨2712460267581289059114161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1808306845054192706076107 2712460267581289059114161)
  ·
    refine ⟨2034345200685966794335621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2712460267581289059114161 2034345200685966794335621)
    ·
      refine ⟨381439725128618773937929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2034345200685966794335621 381439725128618773937929)
      ·
        refine ⟨286079793846464080453447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381439725128618773937929 286079793846464080453447)
        ·
          refine ⟨429119690769696120680171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286079793846464080453447 429119690769696120680171)
          ·
            refine ⟨643679536154544181020257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429119690769696120680171 643679536154544181020257)
            ·
              refine ⟨482759652115908135765193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643679536154544181020257 482759652115908135765193)
              ·
                refine ⟨362069739086931101823895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482759652115908135765193 362069739086931101823895)
                ·
                  refine ⟨543104608630396652735843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362069739086931101823895 543104608630396652735843)
                  ·
                    refine ⟨814656912945594979103765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 543104608630396652735843 814656912945594979103765)
                    ·
                      refine ⟨38187042794324764645489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 814656912945594979103765 38187042794324764645489)
                      ·
                        rfl

theorem cell23_74369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_74369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74369 prefixEnd_74369 := by exact prefixLift 74369
  have htrace : WordTrace (prefixWord ++ tailWord_74369) baseStart_74369 baseEnd_74369 := by
    simpa [prefixWord, tailWord_74369, baseEnd_74369] using wordTrace_append hprefix tailTrace_74369
  have hstable : (prefixWord ++ tailWord_74369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74369).length < 2 ^ (prefixWord ++ tailWord_74369).sum := by decide
  have hdescent : baseEnd_74369 < baseStart_74369 := by decide
  rcases family_descends (prefixWord ++ tailWord_74369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74373 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 3, 2, 2]
def baseStart_74373 : Nat := 118140960795 + 74373 * 2 ^ 59
def prefixEnd_74373 : Nat := 4983230072969 + 3 ^ 40 * 74373 * 2
def baseEnd_74373 : Nat := 38189096716942748995471

theorem tailTrace_74373 : CollatzResearch.WordTrace tailWord_74373 prefixEnd_74373 38189096716942748995471 := by
  unfold tailWord_74373
  simp only [CollatzResearch.WordTrace]
  refine ⟨2712606159566797742259773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1808404106377865161506515 2712606159566797742259773)
  ·
    refine ⟨1017227309837549153347415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2712606159566797742259773 1017227309837549153347415)
    ·
      refine ⟨1525840964756323730021123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1017227309837549153347415 1525840964756323730021123)
      ·
        refine ⟨2288761447134485595031685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1525840964756323730021123 2288761447134485595031685)
        ·
          refine ⟨429142771337716049068441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2288761447134485595031685 429142771337716049068441)
          ·
            refine ⟨321857078503287036801331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429142771337716049068441 321857078503287036801331)
            ·
              refine ⟨482785617754930555201997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321857078503287036801331 482785617754930555201997)
              ·
                refine ⟨181044606658098958200749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 482785617754930555201997 181044606658098958200749)
                ·
                  refine ⟨67891727496787109325281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181044606658098958200749 67891727496787109325281)
                  ·
                    refine ⟨50918795622590331993961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67891727496787109325281 50918795622590331993961)
                    ·
                      refine ⟨38189096716942748995471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50918795622590331993961 38189096716942748995471)
                      ·
                        rfl

theorem cell23_74373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 2, 2].length) (baseStart_74373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74373 prefixEnd_74373 := by exact prefixLift 74373
  have htrace : WordTrace (prefixWord ++ tailWord_74373) baseStart_74373 baseEnd_74373 := by
    simpa [prefixWord, tailWord_74373, baseEnd_74373] using wordTrace_append hprefix tailTrace_74373
  have hstable : (prefixWord ++ tailWord_74373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74373).length < 2 ^ (prefixWord ++ tailWord_74373).sum := by decide
  have hdescent : baseEnd_74373 < baseStart_74373 := by decide
  rcases family_descends (prefixWord ++ tailWord_74373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74386 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_74386 : Nat := 118140960795 + 74386 * 2 ^ 59
def prefixEnd_74386 : Nat := 4983230072969 + 3 ^ 40 * 74386 * 2
def baseEnd_74386 : Nat := 38195771965451198132911

theorem tailTrace_74386 : CollatzResearch.WordTrace tailWord_74386 prefixEnd_74386 38195771965451198132911 := by
  unfold tailWord_74386
  simp only [CollatzResearch.WordTrace]
  refine ⟨678270077129925240620753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1808720205679800641655341 678270077129925240620753)
  ·
    refine ⟨508702557847443930465565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 678270077129925240620753 508702557847443930465565)
    ·
      refine ⟨190763459192791473924587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 508702557847443930465565 190763459192791473924587)
      ·
        refine ⟨286145188789187210886881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190763459192791473924587 286145188789187210886881)
        ·
          refine ⟨214608891591890408165161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286145188789187210886881 214608891591890408165161)
          ·
            refine ⟨160956668693917806123871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214608891591890408165161 160956668693917806123871)
            ·
              refine ⟨241435003040876709185807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160956668693917806123871 241435003040876709185807)
              ·
                refine ⟨362152504561315063778711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241435003040876709185807 362152504561315063778711)
                ·
                  refine ⟨543228756841972595668067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362152504561315063778711 543228756841972595668067)
                  ·
                    refine ⟨814843135262958893502101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 543228756841972595668067 814843135262958893502101)
                    ·
                      refine ⟨38195771965451198132911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 814843135262958893502101 38195771965451198132911)
                      ·
                        rfl

theorem cell23_74386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_74386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74386 prefixEnd_74386 := by exact prefixLift 74386
  have htrace : WordTrace (prefixWord ++ tailWord_74386) baseStart_74386 baseEnd_74386 := by
    simpa [prefixWord, tailWord_74386, baseEnd_74386] using wordTrace_append hprefix tailTrace_74386
  have hstable : (prefixWord ++ tailWord_74386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74386).length < 2 ^ (prefixWord ++ tailWord_74386).sum := by decide
  have hdescent : baseEnd_74386 < baseStart_74386 := by decide
  rcases family_descends (prefixWord ++ tailWord_74386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74396 : List Nat := [2, 2, 3, 2, 2, 1, 4, 7]
def baseStart_74396 : Nat := 118140960795 + 74396 * 2 ^ 59
def prefixEnd_74396 : Nat := 4983230072969 + 3 ^ 40 * 74396 * 2
def baseEnd_74396 : Nat := 1414848398962820703995

theorem tailTrace_74396 : CollatzResearch.WordTrace tailWord_74396 prefixEnd_74396 1414848398962820703995 := by
  unfold tailWord_74396
  simp only [CollatzResearch.WordTrace]
  refine ⟨1356722519241736335173521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1808963358988981780231361 1356722519241736335173521)
  ·
    refine ⟨1017541889431302251380141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1356722519241736335173521 1017541889431302251380141)
    ·
      refine ⟨381578208536738344267553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1017541889431302251380141 381578208536738344267553)
      ·
        refine ⟨286183656402553758200665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381578208536738344267553 286183656402553758200665)
        ·
          refine ⟨214637742301915318650499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286183656402553758200665 214637742301915318650499)
          ·
            refine ⟨321956613452872977975749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214637742301915318650499 321956613452872977975749)
            ·
              refine ⟨60366865022413683370453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 321956613452872977975749 60366865022413683370453)
              ·
                refine ⟨1414848398962820703995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 60366865022413683370453 1414848398962820703995)
                ·
                  rfl

theorem cell23_74396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 7].length) (baseStart_74396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74396 prefixEnd_74396 := by exact prefixLift 74396
  have htrace : WordTrace (prefixWord ++ tailWord_74396) baseStart_74396 baseEnd_74396 := by
    simpa [prefixWord, tailWord_74396, baseEnd_74396] using wordTrace_append hprefix tailTrace_74396
  have hstable : (prefixWord ++ tailWord_74396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74396).length < 2 ^ (prefixWord ++ tailWord_74396).sum := by decide
  have hdescent : baseEnd_74396 < baseStart_74396 := by decide
  rcases family_descends (prefixWord ++ tailWord_74396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74410 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_74410 : Nat := 118140960795 + 74410 * 2 ^ 59
def prefixEnd_74410 : Nat := 4983230072969 + 3 ^ 40 * 74410 * 2
def baseEnd_74410 : Nat := 38208095501159104232801

theorem tailTrace_74410 : CollatzResearch.WordTrace tailWord_74410 prefixEnd_74410 38208095501159104232801 := by
  unfold tailWord_74410
  simp only [CollatzResearch.WordTrace]
  refine ⟨678488915108188265339171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1809303773621835374237789 678488915108188265339171)
  ·
    refine ⟨1017733372662282398008757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 678488915108188265339171 1017733372662282398008757)
    ·
      refine ⟨95412503687088974813321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1017733372662282398008757 95412503687088974813321)
      ·
        refine ⟨71559377765316731109991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95412503687088974813321 71559377765316731109991)
        ·
          refine ⟨107339066647975096664987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71559377765316731109991 107339066647975096664987)
          ·
            refine ⟨161008599971962644997481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107339066647975096664987 161008599971962644997481)
            ·
              refine ⟨120756449978971983748111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161008599971962644997481 120756449978971983748111)
              ·
                refine ⟨181134674968457975622167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120756449978971983748111 181134674968457975622167)
                ·
                  refine ⟨271702012452686963433251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181134674968457975622167 271702012452686963433251)
                  ·
                    refine ⟨407553018679030445149877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 271702012452686963433251 407553018679030445149877)
                    ·
                      refine ⟨38208095501159104232801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 407553018679030445149877 38208095501159104232801)
                      ·
                        rfl

theorem cell23_74410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_74410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74410 prefixEnd_74410 := by exact prefixLift 74410
  have htrace : WordTrace (prefixWord ++ tailWord_74410) baseStart_74410 baseEnd_74410 := by
    simpa [prefixWord, tailWord_74410, baseEnd_74410] using wordTrace_append hprefix tailTrace_74410
  have hstable : (prefixWord ++ tailWord_74410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74410).length < 2 ^ (prefixWord ++ tailWord_74410).sum := by decide
  have hdescent : baseEnd_74410 < baseStart_74410 := by decide
  rcases family_descends (prefixWord ++ tailWord_74410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74416 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 5, 3, 2]
def baseStart_74416 : Nat := 118140960795 + 74416 * 2 ^ 59
def prefixEnd_74416 : Nat := 4983230072969 + 3 ^ 40 * 74416 * 2
def baseEnd_74416 : Nat := 38211176385086080757773

theorem tailTrace_74416 : CollatzResearch.WordTrace tailWord_74416 prefixEnd_74416 38211176385086080757773 := by
  unfold tailWord_74416
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357087249205508043037551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1809449665607344057383401 1357087249205508043037551)
  ·
    refine ⟨2035630873808262064556327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1357087249205508043037551 2035630873808262064556327)
    ·
      refine ⟨3053446310712393096834491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2035630873808262064556327 3053446310712393096834491)
      ·
        refine ⟨4580169466068589645251737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3053446310712393096834491 4580169466068589645251737)
        ·
          refine ⟨3435127099551442233938803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4580169466068589645251737 3435127099551442233938803)
          ·
            refine ⟨5152690649327163350908205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435127099551442233938803 5152690649327163350908205)
            ·
              refine ⟨1932258993497686256590577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5152690649327163350908205 1932258993497686256590577)
              ·
                refine ⟨1449194245123264692442933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932258993497686256590577 1449194245123264692442933)
                ·
                  refine ⟨135861960480306064916525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1449194245123264692442933 135861960480306064916525)
                  ·
                    refine ⟨50948235180114774343697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135861960480306064916525 50948235180114774343697)
                    ·
                      refine ⟨38211176385086080757773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50948235180114774343697 38211176385086080757773)
                      ·
                        rfl

theorem cell23_74416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 3, 2].length) (baseStart_74416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74416 prefixEnd_74416 := by exact prefixLift 74416
  have htrace : WordTrace (prefixWord ++ tailWord_74416) baseStart_74416 baseEnd_74416 := by
    simpa [prefixWord, tailWord_74416, baseEnd_74416] using wordTrace_append hprefix tailTrace_74416
  have hstable : (prefixWord ++ tailWord_74416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74416).length < 2 ^ (prefixWord ++ tailWord_74416).sum := by decide
  have hdescent : baseEnd_74416 < baseStart_74416 := by decide
  rcases family_descends (prefixWord ++ tailWord_74416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74440 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 2, 1, 3]
def baseStart_74440 : Nat := 118140960795 + 74440 * 2 ^ 59
def prefixEnd_74440 : Nat := 4983230072969 + 3 ^ 40 * 74440 * 2
def baseEnd_74440 : Nat := 38223499920793986857663

theorem tailTrace_74440 : CollatzResearch.WordTrace tailWord_74440 prefixEnd_74440 38223499920793986857663 := by
  unfold tailWord_74440
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357524925162034092474387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1810033233549378789965849 1357524925162034092474387)
  ·
    refine ⟨2036287387743051138711581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1357524925162034092474387 2036287387743051138711581)
    ·
      refine ⟨763607770403644177016843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2036287387743051138711581 763607770403644177016843)
      ·
        refine ⟨1145411655605466265525265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763607770403644177016843 1145411655605466265525265)
        ·
          refine ⟨859058741704099699143949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1145411655605466265525265 859058741704099699143949)
          ·
            refine ⟨322147028139037387178981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 859058741704099699143949 322147028139037387178981)
            ·
              refine ⟨60402567776069510096059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 322147028139037387178981 60402567776069510096059)
              ·
                refine ⟨90603851664104265144089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60402567776069510096059 90603851664104265144089)
                ·
                  refine ⟨67952888748078198858067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90603851664104265144089 67952888748078198858067)
                  ·
                    refine ⟨101929333122117298287101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67952888748078198858067 101929333122117298287101)
                    ·
                      refine ⟨38223499920793986857663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 101929333122117298287101 38223499920793986857663)
                      ·
                        rfl

theorem cell23_74440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_74440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74440 prefixEnd_74440 := by exact prefixLift 74440
  have htrace : WordTrace (prefixWord ++ tailWord_74440) baseStart_74440 baseEnd_74440 := by
    simpa [prefixWord, tailWord_74440, baseEnd_74440] using wordTrace_append hprefix tailTrace_74440
  have hstable : (prefixWord ++ tailWord_74440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74440).length < 2 ^ (prefixWord ++ tailWord_74440).sum := by decide
  have hdescent : baseEnd_74440 < baseStart_74440 := by decide
  rcases family_descends (prefixWord ++ tailWord_74440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74449 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_74449 : Nat := 118140960795 + 74449 * 2 ^ 59
def prefixEnd_74449 : Nat := 4983230072969 + 3 ^ 40 * 74449 * 2
def baseEnd_74449 : Nat := 38228121246684451645121

theorem tailTrace_74449 : CollatzResearch.WordTrace tailWord_74449 prefixEnd_74449 38228121246684451645121 := by
  unfold tailWord_74449
  simp only [CollatzResearch.WordTrace]
  refine ⟨2715378107291462722026401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1810252071527641814684267 2715378107291462722026401)
  ·
    refine ⟨2036533580468597041519801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2715378107291462722026401 2036533580468597041519801)
    ·
      refine ⟨1527400185351447781139851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2036533580468597041519801 1527400185351447781139851)
      ·
        refine ⟨2291100278027171671709777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527400185351447781139851 2291100278027171671709777)
        ·
          refine ⟨1718325208520378753782333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2291100278027171671709777 1718325208520378753782333)
          ·
            refine ⟨644371953195142032668375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1718325208520378753782333 644371953195142032668375)
            ·
              refine ⟨966557929792713049002563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644371953195142032668375 966557929792713049002563)
              ·
                refine ⟨1449836894689069573503845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966557929792713049002563 1449836894689069573503845)
                ·
                  refine ⟨271844417754200545031971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1449836894689069573503845 271844417754200545031971)
                  ·
                    refine ⟨407766626631300817547957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 271844417754200545031971 407766626631300817547957)
                    ·
                      refine ⟨38228121246684451645121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 407766626631300817547957 38228121246684451645121)
                      ·
                        rfl

theorem cell23_74449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_74449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74449 prefixEnd_74449 := by exact prefixLift 74449
  have htrace : WordTrace (prefixWord ++ tailWord_74449) baseStart_74449 baseEnd_74449 := by
    simpa [prefixWord, tailWord_74449, baseEnd_74449] using wordTrace_append hprefix tailTrace_74449
  have hstable : (prefixWord ++ tailWord_74449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74449).length < 2 ^ (prefixWord ++ tailWord_74449).sum := by decide
  have hdescent : baseEnd_74449 < baseStart_74449 := by decide
  rcases family_descends (prefixWord ++ tailWord_74449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74450 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_74450 : Nat := 118140960795 + 74450 * 2 ^ 59
def prefixEnd_74450 : Nat := 4983230072969 + 3 ^ 40 * 74450 * 2
def baseEnd_74450 : Nat := 38228634727338947732617

theorem tailTrace_74450 : CollatzResearch.WordTrace tailWord_74450 prefixEnd_74450 38228634727338947732617 := by
  unfold tailWord_74450
  simp only [CollatzResearch.WordTrace]
  refine ⟨678853645071959973203201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1810276386858559928541869 678853645071959973203201)
  ·
    refine ⟨509140233803969979902401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 678853645071959973203201 509140233803969979902401)
    ·
      refine ⟨381855175352977484926801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 509140233803969979902401 381855175352977484926801)
      ·
        refine ⟨286391381514733113695101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381855175352977484926801 286391381514733113695101)
        ·
          refine ⟨107396768068024917635663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286391381514733113695101 107396768068024917635663)
          ·
            refine ⟨161095152102037376453495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107396768068024917635663 161095152102037376453495)
            ·
              refine ⟨241642728153056064680243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161095152102037376453495 241642728153056064680243)
              ·
                refine ⟨362464092229584097020365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241642728153056064680243 362464092229584097020365)
                ·
                  refine ⟨135924034586094036382637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362464092229584097020365 135924034586094036382637)
                  ·
                    refine ⟨50971512969785263643489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135924034586094036382637 50971512969785263643489)
                    ·
                      refine ⟨38228634727338947732617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50971512969785263643489 38228634727338947732617)
                      ·
                        rfl

theorem cell23_74450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_74450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74450 prefixEnd_74450 := by exact prefixLift 74450
  have htrace : WordTrace (prefixWord ++ tailWord_74450) baseStart_74450 baseEnd_74450 := by
    simpa [prefixWord, tailWord_74450, baseEnd_74450] using wordTrace_append hprefix tailTrace_74450
  have hstable : (prefixWord ++ tailWord_74450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74450).length < 2 ^ (prefixWord ++ tailWord_74450).sum := by decide
  have hdescent : baseEnd_74450 < baseStart_74450 := by decide
  rcases family_descends (prefixWord ++ tailWord_74450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74463 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 1, 4, 2]
def baseStart_74463 : Nat := 118140960795 + 74463 * 2 ^ 59
def prefixEnd_74463 : Nat := 4983230072969 + 3 ^ 40 * 74463 * 2
def baseEnd_74463 : Nat := 38235309975847396870057

theorem tailTrace_74463 : CollatzResearch.WordTrace tailWord_74463 prefixEnd_74463 38235309975847396870057 := by
  unfold tailWord_74463
  simp only [CollatzResearch.WordTrace]
  refine ⟨2715888729240743113036043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1810592486160495408690695 2715888729240743113036043)
  ·
    refine ⟨4073833093861114669554065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2715888729240743113036043 4073833093861114669554065)
    ·
      refine ⟨3055374820395836002165549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4073833093861114669554065 3055374820395836002165549)
      ·
        refine ⟨1145765557648438500812081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3055374820395836002165549 1145765557648438500812081)
        ·
          refine ⟨859324168236328875609061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1145765557648438500812081 859324168236328875609061)
          ·
            refine ⟨161123281544311664176699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 859324168236328875609061 161123281544311664176699)
            ·
              refine ⟨241684922316467496265049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161123281544311664176699 241684922316467496265049)
              ·
                refine ⟨181263691737350622198787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241684922316467496265049 181263691737350622198787)
                ·
                  refine ⟨271895537606025933298181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181263691737350622198787 271895537606025933298181)
                  ·
                    refine ⟨50980413301129862493409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 271895537606025933298181 50980413301129862493409)
                    ·
                      refine ⟨38235309975847396870057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50980413301129862493409 38235309975847396870057)
                      ·
                        rfl

theorem cell23_74463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_74463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74463 prefixEnd_74463 := by exact prefixLift 74463
  have htrace : WordTrace (prefixWord ++ tailWord_74463) baseStart_74463 baseEnd_74463 := by
    simpa [prefixWord, tailWord_74463, baseEnd_74463] using wordTrace_append hprefix tailTrace_74463
  have hstable : (prefixWord ++ tailWord_74463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74463).length < 2 ^ (prefixWord ++ tailWord_74463).sum := by decide
  have hdescent : baseEnd_74463 < baseStart_74463 := by decide
  rcases family_descends (prefixWord ++ tailWord_74463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74467 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 1, 3, 2]
def baseStart_74467 : Nat := 118140960795 + 74467 * 2 ^ 59
def prefixEnd_74467 : Nat := 4983230072969 + 3 ^ 40 * 74467 * 2
def baseEnd_74467 : Nat := 38237363898465381220039

theorem tailTrace_74467 : CollatzResearch.WordTrace tailWord_74467 prefixEnd_74467 38237363898465381220039 := by
  unfold tailWord_74467
  simp only [CollatzResearch.WordTrace]
  refine ⟨2716034621226251796181655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1810689747484167864121103 2716034621226251796181655)
  ·
    refine ⟨4074051931839377694272483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2716034621226251796181655 4074051931839377694272483)
    ·
      refine ⟨6111077897759066541408725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4074051931839377694272483 6111077897759066541408725)
      ·
        refine ⟨143228388228728122064267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 6111077897759066541408725 143228388228728122064267)
        ·
          refine ⟨214842582343092183096401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143228388228728122064267 214842582343092183096401)
          ·
            refine ⟨161131936757319137322301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214842582343092183096401 161131936757319137322301)
            ·
              refine ⟨60424476283994676495863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161131936757319137322301 60424476283994676495863)
              ·
                refine ⟨90636714425992014743795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60424476283994676495863 90636714425992014743795)
                ·
                  refine ⟨135955071638988022115693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90636714425992014743795 135955071638988022115693)
                  ·
                    refine ⟨50983151864620508293385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135955071638988022115693 50983151864620508293385)
                    ·
                      refine ⟨38237363898465381220039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50983151864620508293385 38237363898465381220039)
                      ·
                        rfl

theorem cell23_74467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_74467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74467 prefixEnd_74467 := by exact prefixLift 74467
  have htrace : WordTrace (prefixWord ++ tailWord_74467) baseStart_74467 baseEnd_74467 := by
    simpa [prefixWord, tailWord_74467, baseEnd_74467] using wordTrace_append hprefix tailTrace_74467
  have hstable : (prefixWord ++ tailWord_74467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74467).length < 2 ^ (prefixWord ++ tailWord_74467).sum := by decide
  have hdescent : baseEnd_74467 < baseStart_74467 := by decide
  rcases family_descends (prefixWord ++ tailWord_74467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74480 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 2, 2, 2]
def baseStart_74480 : Nat := 118140960795 + 74480 * 2 ^ 59
def prefixEnd_74480 : Nat := 4983230072969 + 3 ^ 40 * 74480 * 2
def baseEnd_74480 : Nat := 38244039146973830357479

theorem tailTrace_74480 : CollatzResearch.WordTrace tailWord_74480 prefixEnd_74480 38244039146973830357479 := by
  unfold tailWord_74480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358254385089577508202447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1811005846786103344269929 1358254385089577508202447)
  ·
    refine ⟨2037381577634366262303671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1358254385089577508202447 2037381577634366262303671)
    ·
      refine ⟨3056072366451549393455507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2037381577634366262303671 3056072366451549393455507)
      ·
        refine ⟨4584108549677324090183261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056072366451549393455507 4584108549677324090183261)
        ·
          refine ⟨1719040706128996533818723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4584108549677324090183261 1719040706128996533818723)
          ·
            refine ⟨2578561059193494800728085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719040706128996533818723 2578561059193494800728085)
            ·
              refine ⟨120870049649695068784129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2578561059193494800728085 120870049649695068784129)
              ·
                refine ⟨90652537237271301588097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120870049649695068784129 90652537237271301588097)
                ·
                  refine ⟨67989402927953476191073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90652537237271301588097 67989402927953476191073)
                  ·
                    refine ⟨50992052195965107143305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67989402927953476191073 50992052195965107143305)
                    ·
                      refine ⟨38244039146973830357479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 50992052195965107143305 38244039146973830357479)
                      ·
                        rfl

theorem cell23_74480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2, 2, 2].length) (baseStart_74480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74480 prefixEnd_74480 := by exact prefixLift 74480
  have htrace : WordTrace (prefixWord ++ tailWord_74480) baseStart_74480 baseEnd_74480 := by
    simpa [prefixWord, tailWord_74480, baseEnd_74480] using wordTrace_append hprefix tailTrace_74480
  have hstable : (prefixWord ++ tailWord_74480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74480).length < 2 ^ (prefixWord ++ tailWord_74480).sum := by decide
  have hdescent : baseEnd_74480 < baseStart_74480 := by decide
  rcases family_descends (prefixWord ++ tailWord_74480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74486 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_74486 : Nat := 118140960795 + 74486 * 2 ^ 59
def prefixEnd_74486 : Nat := 4983230072969 + 3 ^ 40 * 74486 * 2
def baseEnd_74486 : Nat := 4249680003433422986939

theorem tailTrace_74486 : CollatzResearch.WordTrace tailWord_74486 prefixEnd_74486 4249680003433422986939 := by
  unfold tailWord_74486
  simp only [CollatzResearch.WordTrace]
  refine ⟨169795475509838627570207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1811151738771612027415541 169795475509838627570207)
  ·
    refine ⟨254693213264757941355311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169795475509838627570207 254693213264757941355311)
    ·
      refine ⟨382039819897136912032967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254693213264757941355311 382039819897136912032967)
      ·
        refine ⟨573059729845705368049451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382039819897136912032967 573059729845705368049451)
        ·
          refine ⟨859589594768558052074177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573059729845705368049451 859589594768558052074177)
          ·
            refine ⟨644692196076418539055633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859589594768558052074177 644692196076418539055633)
            ·
              refine ⟨483519147057313904291725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644692196076418539055633 483519147057313904291725)
              ·
                refine ⟨181319680146492714109397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483519147057313904291725 181319680146492714109397)
                ·
                  refine ⟨4249680003433422986939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 181319680146492714109397 4249680003433422986939)
                  ·
                    rfl

theorem cell23_74486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_74486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74486 prefixEnd_74486 := by exact prefixLift 74486
  have htrace : WordTrace (prefixWord ++ tailWord_74486) baseStart_74486 baseEnd_74486 := by
    simpa [prefixWord, tailWord_74486, baseEnd_74486] using wordTrace_append hprefix tailTrace_74486
  have hstable : (prefixWord ++ tailWord_74486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74486).length < 2 ^ (prefixWord ++ tailWord_74486).sum := by decide
  have hdescent : baseEnd_74486 < baseStart_74486 := by decide
  rcases family_descends (prefixWord ++ tailWord_74486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74499 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 1, 7]
def baseStart_74499 : Nat := 118140960795 + 74499 * 2 ^ 59
def prefixEnd_74499 : Nat := 4983230072969 + 3 ^ 40 * 74499 * 2
def baseEnd_74499 : Nat := 12751265093136418673297

theorem tailTrace_74499 : CollatzResearch.WordTrace tailWord_74499 prefixEnd_74499 12751265093136418673297 := by
  unfold tailWord_74499
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717201757110321261346551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1811467838073547507564367 2717201757110321261346551)
  ·
    refine ⟨4075802635665481892019827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2717201757110321261346551 4075802635665481892019827)
    ·
      refine ⟨6113703953498222838029741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4075802635665481892019827 6113703953498222838029741)
      ·
        refine ⟨2292638982561833564261153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6113703953498222838029741 2292638982561833564261153)
        ·
          refine ⟨1719479236921375173195865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2292638982561833564261153 1719479236921375173195865)
          ·
            refine ⟨1289609427691031379896899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1719479236921375173195865 1289609427691031379896899)
            ·
              refine ⟨1934414141536547069845349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289609427691031379896899 1934414141536547069845349)
              ·
                refine ⟨362702651538102575596003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1934414141536547069845349 362702651538102575596003)
                ·
                  refine ⟨544053977307153863394005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362702651538102575596003 544053977307153863394005)
                  ·
                    refine ⟨12751265093136418673297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 544053977307153863394005 12751265093136418673297)
                    ·
                      rfl

theorem cell23_74499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 7].length) (baseStart_74499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74499 prefixEnd_74499 := by exact prefixLift 74499
  have htrace : WordTrace (prefixWord ++ tailWord_74499) baseStart_74499 baseEnd_74499 := by
    simpa [prefixWord, tailWord_74499, baseEnd_74499] using wordTrace_append hprefix tailTrace_74499
  have hstable : (prefixWord ++ tailWord_74499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74499).length < 2 ^ (prefixWord ++ tailWord_74499).sum := by decide
  have hdescent : baseEnd_74499 < baseStart_74499 := by decide
  rcases family_descends (prefixWord ++ tailWord_74499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74539 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 5]
def baseStart_74539 : Nat := 118140960795 + 74539 * 2 ^ 59
def prefixEnd_74539 : Nat := 4983230072969 + 3 ^ 40 * 74539 * 2
def baseEnd_74539 : Nat := 38274334505589099519707

theorem tailTrace_74539 : CollatzResearch.WordTrace tailWord_74539 prefixEnd_74539 38274334505589099519707 := by
  unfold tailWord_74539
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718660676965408092802671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1812440451310272061868447 2718660676965408092802671)
  ·
    refine ⟨4077991015448112139204007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2718660676965408092802671 4077991015448112139204007)
    ·
      refine ⟨6116986523172168208806011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4077991015448112139204007 6116986523172168208806011)
      ·
        refine ⟨9175479784758252313209017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6116986523172168208806011 9175479784758252313209017)
        ·
          refine ⟨6881609838568689234906763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9175479784758252313209017 6881609838568689234906763)
          ·
            refine ⟨10322414757853033852360145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6881609838568689234906763 10322414757853033852360145)
            ·
              refine ⟨7741811068389775389270109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10322414757853033852360145 7741811068389775389270109)
              ·
                refine ⟨2903179150646165770976291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7741811068389775389270109 2903179150646165770976291)
                ·
                  refine ⟨4354768725969248656464437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2903179150646165770976291 4354768725969248656464437)
                  ·
                    refine ⟨408259568059617061543541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4354768725969248656464437 408259568059617061543541)
                    ·
                      refine ⟨38274334505589099519707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 408259568059617061543541 38274334505589099519707)
                      ·
                        rfl

theorem cell23_74539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_74539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74539 prefixEnd_74539 := by exact prefixLift 74539
  have htrace : WordTrace (prefixWord ++ tailWord_74539) baseStart_74539 baseEnd_74539 := by
    simpa [prefixWord, tailWord_74539, baseEnd_74539] using wordTrace_append hprefix tailTrace_74539
  have hstable : (prefixWord ++ tailWord_74539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74539).length < 2 ^ (prefixWord ++ tailWord_74539).sum := by decide
  have hdescent : baseEnd_74539 < baseStart_74539 := by decide
  rcases family_descends (prefixWord ++ tailWord_74539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74623 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 1, 5]
def baseStart_74623 : Nat := 118140960795 + 74623 * 2 ^ 59
def prefixEnd_74623 : Nat := 4983230072969 + 3 ^ 40 * 74623 * 2
def baseEnd_74623 : Nat := 12772488960188923623107

theorem tailTrace_74623 : CollatzResearch.WordTrace tailWord_74623 prefixEnd_74623 12772488960188923623107 := by
  unfold tailWord_74623
  simp only [CollatzResearch.WordTrace]
  refine ⟨2721724408661090438860523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1814482939107393625907015 2721724408661090438860523)
  ·
    refine ⟨4082586612991635658290785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2721724408661090438860523 4082586612991635658290785)
    ·
      refine ⟨3061939959743726743718089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4082586612991635658290785 3061939959743726743718089)
      ·
        refine ⟨2296454969807795057788567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3061939959743726743718089 2296454969807795057788567)
        ·
          refine ⟨3444682454711692586682851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296454969807795057788567 3444682454711692586682851)
          ·
            refine ⟨5167023682067538880024277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444682454711692586682851 5167023682067538880024277)
            ·
              refine ⟨121102117548457942500569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5167023682067538880024277 121102117548457942500569)
              ·
                refine ⟨90826588161343456875427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121102117548457942500569 90826588161343456875427)
                ·
                  refine ⟨136239882242015185313141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90826588161343456875427 136239882242015185313141)
                  ·
                    refine ⟨12772488960188923623107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 136239882242015185313141 12772488960188923623107)
                    ·
                      rfl

theorem cell23_74623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 5].length) (baseStart_74623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74623 prefixEnd_74623 := by exact prefixLift 74623
  have htrace : WordTrace (prefixWord ++ tailWord_74623) baseStart_74623 baseEnd_74623 := by
    simpa [prefixWord, tailWord_74623, baseEnd_74623] using wordTrace_append hprefix tailTrace_74623
  have hstable : (prefixWord ++ tailWord_74623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74623).length < 2 ^ (prefixWord ++ tailWord_74623).sum := by decide
  have hdescent : baseEnd_74623 < baseStart_74623 := by decide
  rcases family_descends (prefixWord ++ tailWord_74623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74636 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_74636 : Nat := 118140960795 + 74636 * 2 ^ 59
def prefixEnd_74636 : Nat := 4983230072969 + 3 ^ 40 * 74636 * 2
def baseEnd_74636 : Nat := 12774714043025073335587

theorem tailTrace_74636 : CollatzResearch.WordTrace tailWord_74636 prefixEnd_74636 12774714043025073335587 := by
  unfold tailWord_74636
  simp only [CollatzResearch.WordTrace]
  refine ⟨1361099278806996829541881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1814799038409329106055841 1361099278806996829541881)
  ·
    refine ⟨1020824459105247622156411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1361099278806996829541881 1020824459105247622156411)
    ·
      refine ⟨1531236688657871433234617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020824459105247622156411 1531236688657871433234617)
      ·
        refine ⟨1148427516493403574925963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1531236688657871433234617 1148427516493403574925963)
        ·
          refine ⟨1722641274740105362388945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148427516493403574925963 1722641274740105362388945)
          ·
            refine ⟨1291980956055079021791709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1722641274740105362388945 1291980956055079021791709)
            ·
              refine ⟨484492858520654633171891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1291980956055079021791709 484492858520654633171891)
              ·
                refine ⟨726739287780981949757837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484492858520654633171891 726739287780981949757837)
                ·
                  refine ⟨272527232917868231159189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726739287780981949757837 272527232917868231159189)
                  ·
                    refine ⟨12774714043025073335587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 272527232917868231159189 12774714043025073335587)
                    ·
                      rfl

theorem cell23_74636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_74636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74636 prefixEnd_74636 := by exact prefixLift 74636
  have htrace : WordTrace (prefixWord ++ tailWord_74636) baseStart_74636 baseEnd_74636 := by
    simpa [prefixWord, tailWord_74636, baseEnd_74636] using wordTrace_append hprefix tailTrace_74636
  have hstable : (prefixWord ++ tailWord_74636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74636).length < 2 ^ (prefixWord ++ tailWord_74636).sum := by decide
  have hdescent : baseEnd_74636 < baseStart_74636 := by decide
  rcases family_descends (prefixWord ++ tailWord_74636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74656 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_74656 : Nat := 118140960795 + 74656 * 2 ^ 59
def prefixEnd_74656 : Nat := 4983230072969 + 3 ^ 40 * 74656 * 2
def baseEnd_74656 : Nat := 38334411742165141756669

theorem tailTrace_74656 : CollatzResearch.WordTrace tailWord_74656 prefixEnd_74656 38334411742165141756669 := by
  unfold tailWord_74656
  simp only [CollatzResearch.WordTrace]
  refine ⟨1361464008770768537405911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1815285345027691383207881 1361464008770768537405911)
  ·
    refine ⟨2042196013156152806108867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1361464008770768537405911 2042196013156152806108867)
    ·
      refine ⟨3063294019734229209163301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2042196013156152806108867 3063294019734229209163301)
      ·
        refine ⟨574367628700167976718119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3063294019734229209163301 574367628700167976718119)
        ·
          refine ⟨861551443050251965077179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574367628700167976718119 861551443050251965077179)
          ·
            refine ⟨1292327164575377947615769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861551443050251965077179 1292327164575377947615769)
            ·
              refine ⟨969245373431533460711827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1292327164575377947615769 969245373431533460711827)
              ·
                refine ⟨1453868060147300191067741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969245373431533460711827 1453868060147300191067741)
                ·
                  refine ⟨545200522555237571650403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1453868060147300191067741 545200522555237571650403)
                  ·
                    refine ⟨817800783832856357475605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 545200522555237571650403 817800783832856357475605)
                    ·
                      refine ⟨38334411742165141756669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 817800783832856357475605 38334411742165141756669)
                      ·
                        rfl

theorem cell23_74656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_74656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74656 prefixEnd_74656 := by exact prefixLift 74656
  have htrace : WordTrace (prefixWord ++ tailWord_74656) baseStart_74656 baseEnd_74656 := by
    simpa [prefixWord, tailWord_74656, baseEnd_74656] using wordTrace_append hprefix tailTrace_74656
  have hstable : (prefixWord ++ tailWord_74656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74656).length < 2 ^ (prefixWord ++ tailWord_74656).sum := by decide
  have hdescent : baseEnd_74656 < baseStart_74656 := by decide
  rcases family_descends (prefixWord ++ tailWord_74656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74677 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_74677 : Nat := 118140960795 + 74677 * 2 ^ 59
def prefixEnd_74677 : Nat := 4983230072969 + 3 ^ 40 * 74677 * 2
def baseEnd_74677 : Nat := 38345194835909559594073

theorem tailTrace_74677 : CollatzResearch.WordTrace tailWord_74677 prefixEnd_74677 38345194835909559594073 := by
  unfold tailWord_74677
  simp only [CollatzResearch.WordTrace]
  refine ⟨2723693950465457661326285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1815795966976971774217523 2723693950465457661326285)
  ·
    refine ⟨1021385231424546622997357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2723693950465457661326285 1021385231424546622997357)
    ·
      refine ⟨383019461784204983624009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1021385231424546622997357 383019461784204983624009)
      ·
        refine ⟨287264596338153737718007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383019461784204983624009 287264596338153737718007)
        ·
          refine ⟨430896894507230606577011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287264596338153737718007 430896894507230606577011)
          ·
            refine ⟨646345341760845909865517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430896894507230606577011 646345341760845909865517)
            ·
              refine ⟨242379503160317216199569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 646345341760845909865517 242379503160317216199569)
              ·
                refine ⟨181784627370237912149677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242379503160317216199569 181784627370237912149677)
                ·
                  refine ⟨68169235263839217056129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181784627370237912149677 68169235263839217056129)
                  ·
                    refine ⟨51126926447879412792097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68169235263839217056129 51126926447879412792097)
                    ·
                      refine ⟨38345194835909559594073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51126926447879412792097 38345194835909559594073)
                      ·
                        rfl

theorem cell23_74677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_74677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74677 prefixEnd_74677 := by exact prefixLift 74677
  have htrace : WordTrace (prefixWord ++ tailWord_74677) baseStart_74677 baseEnd_74677 := by
    simpa [prefixWord, tailWord_74677, baseEnd_74677] using wordTrace_append hprefix tailTrace_74677
  have hstable : (prefixWord ++ tailWord_74677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74677).length < 2 ^ (prefixWord ++ tailWord_74677).sum := by decide
  have hdescent : baseEnd_74677 < baseStart_74677 := by decide
  rcases family_descends (prefixWord ++ tailWord_74677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74727 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_74727 : Nat := 118140960795 + 74727 * 2 ^ 59
def prefixEnd_74727 : Nat := 4983230072969 + 3 ^ 40 * 74727 * 2
def baseEnd_74727 : Nat := 38370868868634363968843

theorem tailTrace_74727 : CollatzResearch.WordTrace tailWord_74727 prefixEnd_74727 38370868868634363968843 := by
  unfold tailWord_74727
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725517600284316200646435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1817011733522877467097623 2725517600284316200646435)
  ·
    refine ⟨4088276400426474300969653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2725517600284316200646435 4088276400426474300969653)
    ·
      refine ⟨383275912539981965715905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4088276400426474300969653 383275912539981965715905)
      ·
        refine ⟨287456934404986474286929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383275912539981965715905 287456934404986474286929)
        ·
          refine ⟨215592700803739855715197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287456934404986474286929 215592700803739855715197)
          ·
            refine ⟨80847262801402445893199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215592700803739855715197 80847262801402445893199)
            ·
              refine ⟨121270894202103668839799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80847262801402445893199 121270894202103668839799)
              ·
                refine ⟨181906341303155503259699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121270894202103668839799 181906341303155503259699)
                ·
                  refine ⟨272859511954733254889549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181906341303155503259699 272859511954733254889549)
                  ·
                    refine ⟨102322316983024970583581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 272859511954733254889549 102322316983024970583581)
                    ·
                      refine ⟨38370868868634363968843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 102322316983024970583581 38370868868634363968843)
                      ·
                        rfl

theorem cell23_74727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_74727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74727 prefixEnd_74727 := by exact prefixLift 74727
  have htrace : WordTrace (prefixWord ++ tailWord_74727) baseStart_74727 baseEnd_74727 := by
    simpa [prefixWord, tailWord_74727, baseEnd_74727] using wordTrace_append hprefix tailTrace_74727
  have hstable : (prefixWord ++ tailWord_74727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74727).length < 2 ^ (prefixWord ++ tailWord_74727).sum := by decide
  have hdescent : baseEnd_74727 < baseStart_74727 := by decide
  rcases family_descends (prefixWord ++ tailWord_74727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74737 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 1, 3, 2]
def baseStart_74737 : Nat := 118140960795 + 74737 * 2 ^ 59
def prefixEnd_74737 : Nat := 4983230072969 + 3 ^ 40 * 74737 * 2
def baseEnd_74737 : Nat := 38376003675179324843797

theorem tailTrace_74737 : CollatzResearch.WordTrace tailWord_74737 prefixEnd_74737 38376003675179324843797 := by
  unfold tailWord_74737
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725882330248087908510465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1817254886832058605673643 2725882330248087908510465)
  ·
    refine ⟨2044411747686065931382849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2725882330248087908510465 2044411747686065931382849)
    ·
      refine ⟨1533308810764549448537137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2044411747686065931382849 1533308810764549448537137)
      ·
        refine ⟨1149981608073412086402853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1533308810764549448537137 1149981608073412086402853)
        ·
          refine ⟨215621551513764766200535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1149981608073412086402853 215621551513764766200535)
          ·
            refine ⟨323432327270647149300803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215621551513764766200535 323432327270647149300803)
            ·
              refine ⟨485148490905970723951205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323432327270647149300803 485148490905970723951205)
              ·
                refine ⟨90965342044869510740851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 485148490905970723951205 90965342044869510740851)
                ·
                  refine ⟨136448013067304266111277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90965342044869510740851 136448013067304266111277)
                  ·
                    refine ⟨51168004900239099791729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 136448013067304266111277 51168004900239099791729)
                    ·
                      refine ⟨38376003675179324843797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51168004900239099791729 38376003675179324843797)
                      ·
                        rfl

theorem cell23_74737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_74737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74737 prefixEnd_74737 := by exact prefixLift 74737
  have htrace : WordTrace (prefixWord ++ tailWord_74737) baseStart_74737 baseEnd_74737 := by
    simpa [prefixWord, tailWord_74737, baseEnd_74737] using wordTrace_append hprefix tailTrace_74737
  have hstable : (prefixWord ++ tailWord_74737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74737).length < 2 ^ (prefixWord ++ tailWord_74737).sum := by decide
  have hdescent : baseEnd_74737 < baseStart_74737 := by decide
  rcases family_descends (prefixWord ++ tailWord_74737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74753 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_74753 : Nat := 118140960795 + 74753 * 2 ^ 59
def prefixEnd_74753 : Nat := 4983230072969 + 3 ^ 40 * 74753 * 2
def baseEnd_74753 : Nat := 38384219365651262243723

theorem tailTrace_74753 : CollatzResearch.WordTrace tailWord_74753 prefixEnd_74753 38384219365651262243723 := by
  unfold tailWord_74753
  simp only [CollatzResearch.WordTrace]
  refine ⟨2726465898190122641092913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1817643932126748427395275 2726465898190122641092913)
  ·
    refine ⟨2044849423642591980819685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2726465898190122641092913 2044849423642591980819685)
    ·
      refine ⟨383409266932985996403691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2044849423642591980819685 383409266932985996403691)
      ·
        refine ⟨575113900399478994605537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383409266932985996403691 575113900399478994605537)
        ·
          refine ⟨431335425299609245954153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575113900399478994605537 431335425299609245954153)
          ·
            refine ⟨323501568974706934465615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431335425299609245954153 323501568974706934465615)
            ·
              refine ⟨485252353462060401698423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323501568974706934465615 485252353462060401698423)
              ·
                refine ⟨727878530193090602547635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485252353462060401698423 727878530193090602547635)
                ·
                  refine ⟨1091817795289635903821453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727878530193090602547635 1091817795289635903821453)
                  ·
                    refine ⟨409431673233613463933045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1091817795289635903821453 409431673233613463933045)
                    ·
                      refine ⟨38384219365651262243723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 409431673233613463933045 38384219365651262243723)
                      ·
                        rfl

theorem cell23_74753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_74753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74753 prefixEnd_74753 := by exact prefixLift 74753
  have htrace : WordTrace (prefixWord ++ tailWord_74753) baseStart_74753 baseEnd_74753 := by
    simpa [prefixWord, tailWord_74753, baseEnd_74753] using wordTrace_append hprefix tailTrace_74753
  have hstable : (prefixWord ++ tailWord_74753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74753).length < 2 ^ (prefixWord ++ tailWord_74753).sum := by decide
  have hdescent : baseEnd_74753 < baseStart_74753 := by decide
  rcases family_descends (prefixWord ++ tailWord_74753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74857 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 4]
def baseStart_74857 : Nat := 118140960795 + 74857 * 2 ^ 59
def prefixEnd_74857 : Nat := 4983230072969 + 3 ^ 40 * 74857 * 2
def baseEnd_74857 : Nat := 38437621353718855343245

theorem tailTrace_74857 : CollatzResearch.WordTrace tailWord_74857 prefixEnd_74857 38437621353718855343245 := by
  unfold tailWord_74857
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730259089813348402878825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1820172726542232268585883 2730259089813348402878825)
  ·
    refine ⟨2047694317360011302159119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2730259089813348402878825 2047694317360011302159119)
    ·
      refine ⟨3071541476040016953238679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2047694317360011302159119 3071541476040016953238679)
      ·
        refine ⟨4607312214060025429858019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071541476040016953238679 4607312214060025429858019)
        ·
          refine ⟨6910968321090038144787029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4607312214060025429858019 6910968321090038144787029)
          ·
            refine ⟨80987910012773884509223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 6910968321090038144787029 80987910012773884509223)
            ·
              refine ⟨121481865019160826763835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80987910012773884509223 121481865019160826763835)
              ·
                refine ⟨182222797528741240145753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121481865019160826763835 182222797528741240145753)
                ·
                  refine ⟨136667098146555930109315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182222797528741240145753 136667098146555930109315)
                  ·
                    refine ⟨205000647219833895163973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136667098146555930109315 205000647219833895163973)
                    ·
                      refine ⟨38437621353718855343245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 205000647219833895163973 38437621353718855343245)
                      ·
                        rfl

theorem cell23_74857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 4].length) (baseStart_74857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74857 prefixEnd_74857 := by exact prefixLift 74857
  have htrace : WordTrace (prefixWord ++ tailWord_74857) baseStart_74857 baseEnd_74857 := by
    simpa [prefixWord, tailWord_74857, baseEnd_74857] using wordTrace_append hprefix tailTrace_74857
  have hstable : (prefixWord ++ tailWord_74857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74857).length < 2 ^ (prefixWord ++ tailWord_74857).sum := by decide
  have hdescent : baseEnd_74857 < baseStart_74857 := by decide
  rcases family_descends (prefixWord ++ tailWord_74857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74860 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 3]
def baseStart_74860 : Nat := 118140960795 + 74860 * 2 ^ 59
def prefixEnd_74860 : Nat := 4983230072969 + 3 ^ 40 * 74860 * 2
def baseEnd_74860 : Nat := 38439161795682343605731

theorem tailTrace_74860 : CollatzResearch.WordTrace tailWord_74860 prefixEnd_74860 38439161795682343605731 := by
  unfold tailWord_74860
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365184254401239957619017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1820245672534986610158689 1365184254401239957619017)
  ·
    refine ⟨1023888190800929968214263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1365184254401239957619017 1023888190800929968214263)
    ·
      refine ⟨1535832286201394952321395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023888190800929968214263 1535832286201394952321395)
      ·
        refine ⟨2303748429302092428482093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535832286201394952321395 2303748429302092428482093)
        ·
          refine ⟨863905660988284660680785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2303748429302092428482093 863905660988284660680785)
          ·
            refine ⟨647929245741213495510589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 863905660988284660680785 647929245741213495510589)
            ·
              refine ⟨242973467152955060816471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 647929245741213495510589 242973467152955060816471)
              ·
                refine ⟨364460200729432591224707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242973467152955060816471 364460200729432591224707)
                ·
                  refine ⟨546690301094148886837061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364460200729432591224707 546690301094148886837061)
                  ·
                    refine ⟨102504431455152916281949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546690301094148886837061 102504431455152916281949)
                    ·
                      refine ⟨38439161795682343605731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 102504431455152916281949 38439161795682343605731)
                      ·
                        rfl

theorem cell23_74860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_74860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74860 prefixEnd_74860 := by exact prefixLift 74860
  have htrace : WordTrace (prefixWord ++ tailWord_74860) baseStart_74860 baseEnd_74860 := by
    simpa [prefixWord, tailWord_74860, baseEnd_74860] using wordTrace_append hprefix tailTrace_74860
  have hstable : (prefixWord ++ tailWord_74860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74860).length < 2 ^ (prefixWord ++ tailWord_74860).sum := by decide
  have hdescent : baseEnd_74860 < baseStart_74860 := by decide
  rcases family_descends (prefixWord ++ tailWord_74860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74863 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 8]
def baseStart_74863 : Nat := 118140960795 + 74863 * 2 ^ 59
def prefixEnd_74863 : Nat := 4983230072969 + 3 ^ 40 * 74863 * 2
def baseEnd_74863 : Nat := 4271189137516203540913

theorem tailTrace_74863 : CollatzResearch.WordTrace tailWord_74863 prefixEnd_74863 4271189137516203540913 := by
  unfold tailWord_74863
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730477927791611427597243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1820318618527740951731495 2730477927791611427597243)
  ·
    refine ⟨4095716891687417141395865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2730477927791611427597243 4095716891687417141395865)
    ·
      refine ⟨3071787668765562856046899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4095716891687417141395865 3071787668765562856046899)
      ·
        refine ⟨4607681503148344284070349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071787668765562856046899 4607681503148344284070349)
        ·
          refine ⟨1727880563680629106526381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4607681503148344284070349 1727880563680629106526381)
          ·
            refine ⟨647955211380235914947393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1727880563680629106526381 647955211380235914947393)
            ·
              refine ⟨485966408535176936210545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647955211380235914947393 485966408535176936210545)
              ·
                refine ⟨364474806401382702157909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485966408535176936210545 364474806401382702157909)
                ·
                  refine ⟨4271189137516203540913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 364474806401382702157909 4271189137516203540913)
                  ·
                    rfl

theorem cell23_74863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 8].length) (baseStart_74863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74863 prefixEnd_74863 := by exact prefixLift 74863
  have htrace : WordTrace (prefixWord ++ tailWord_74863) baseStart_74863 baseEnd_74863 := by
    simpa [prefixWord, tailWord_74863, baseEnd_74863] using wordTrace_append hprefix tailTrace_74863
  have hstable : (prefixWord ++ tailWord_74863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74863).length < 2 ^ (prefixWord ++ tailWord_74863).sum := by decide
  have hdescent : baseEnd_74863 < baseStart_74863 := by decide
  rcases family_descends (prefixWord ++ tailWord_74863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74870 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_74870 : Nat := 118140960795 + 74870 * 2 ^ 59
def prefixEnd_74870 : Nat := 4983230072969 + 3 ^ 40 * 74870 * 2
def baseEnd_74870 : Nat := 38444296602227304480685

theorem tailTrace_74870 : CollatzResearch.WordTrace tailWord_74870 prefixEnd_74870 38444296602227304480685 := by
  unfold tailWord_74870
  simp only [CollatzResearch.WordTrace]
  refine ⟨170670827422890726443879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1820488825844167748734709 170670827422890726443879)
  ·
    refine ⟨256006241134336089665819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170670827422890726443879 256006241134336089665819)
    ·
      refine ⟨384009361701504134498729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256006241134336089665819 384009361701504134498729)
      ·
        refine ⟨288007021276128100874047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384009361701504134498729 288007021276128100874047)
        ·
          refine ⟨432010531914192151311071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288007021276128100874047 432010531914192151311071)
          ·
            refine ⟨648015797871288226966607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432010531914192151311071 648015797871288226966607)
            ·
              refine ⟨972023696806932340449911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648015797871288226966607 972023696806932340449911)
              ·
                refine ⟨1458035545210398510674867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972023696806932340449911 1458035545210398510674867)
                ·
                  refine ⟨2187053317815597766012301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458035545210398510674867 2187053317815597766012301)
                  ·
                    refine ⟨820144994180849162254613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2187053317815597766012301 820144994180849162254613)
                    ·
                      refine ⟨38444296602227304480685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 820144994180849162254613 38444296602227304480685)
                      ·
                        rfl

theorem cell23_74870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_74870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74870 prefixEnd_74870 := by exact prefixLift 74870
  have htrace : WordTrace (prefixWord ++ tailWord_74870) baseStart_74870 baseEnd_74870 := by
    simpa [prefixWord, tailWord_74870, baseEnd_74870] using wordTrace_append hprefix tailTrace_74870
  have hstable : (prefixWord ++ tailWord_74870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74870).length < 2 ^ (prefixWord ++ tailWord_74870).sum := by decide
  have hdescent : baseEnd_74870 < baseStart_74870 := by decide
  rcases family_descends (prefixWord ++ tailWord_74870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74880 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 6]
def baseStart_74880 : Nat := 118140960795 + 74880 * 2 ^ 59
def prefixEnd_74880 : Nat := 4983230072969 + 3 ^ 40 * 74880 * 2
def baseEnd_74880 : Nat := 4272159045419140595071

theorem tailTrace_74880 : CollatzResearch.WordTrace tailWord_74880 prefixEnd_74880 4272159045419140595071 := by
  unfold tailWord_74880
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365548984365011665483047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1820731979153348887310729 1365548984365011665483047)
  ·
    refine ⟨2048323476547517498224571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1365548984365011665483047 2048323476547517498224571)
    ·
      refine ⟨3072485214821276247336857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2048323476547517498224571 3072485214821276247336857)
      ·
        refine ⟨2304363911115957185502643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3072485214821276247336857 2304363911115957185502643)
        ·
          refine ⟨3456545866673935778253965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304363911115957185502643 3456545866673935778253965)
          ·
            refine ⟨1296204700002725916845237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3456545866673935778253965 1296204700002725916845237)
            ·
              refine ⟨121519190625255554704241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1296204700002725916845237 121519190625255554704241)
              ·
                refine ⟨91139392968941666028181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121519190625255554704241 91139392968941666028181)
                ·
                  refine ⟨4272159045419140595071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91139392968941666028181 4272159045419140595071)
                  ·
                    rfl

theorem cell23_74880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 6].length) (baseStart_74880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74880 prefixEnd_74880 := by exact prefixLift 74880
  have htrace : WordTrace (prefixWord ++ tailWord_74880) baseStart_74880 baseEnd_74880 := by
    simpa [prefixWord, tailWord_74880, baseEnd_74880] using wordTrace_append hprefix tailTrace_74880
  have hstable : (prefixWord ++ tailWord_74880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74880).length < 2 ^ (prefixWord ++ tailWord_74880).sum := by decide
  have hdescent : baseEnd_74880 < baseStart_74880 := by decide
  rcases family_descends (prefixWord ++ tailWord_74880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74883 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 8]
def baseStart_74883 : Nat := 118140960795 + 74883 * 2 ^ 59
def prefixEnd_74883 : Nat := 4983230072969 + 3 ^ 40 * 74883 * 2
def baseEnd_74883 : Nat := 38450971850735753618125

theorem tailTrace_74883 : CollatzResearch.WordTrace tailWord_74883 prefixEnd_74883 38450971850735753618125 := by
  unfold tailWord_74883
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731207387719154843325303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1820804925146103228883535 2731207387719154843325303)
  ·
    refine ⟨4096811081578732264987955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2731207387719154843325303 4096811081578732264987955)
    ·
      refine ⟨6145216622368098397481933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4096811081578732264987955 6145216622368098397481933)
      ·
        refine ⟨2304456233388036899055725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6145216622368098397481933 2304456233388036899055725)
        ·
          refine ⟨864171087520513837145897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2304456233388036899055725 864171087520513837145897)
          ·
            refine ⟨648128315640385377859423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 864171087520513837145897 648128315640385377859423)
            ·
              refine ⟨972192473460578066789135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648128315640385377859423 972192473460578066789135)
              ·
                refine ⟨1458288710190867100183703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972192473460578066789135 1458288710190867100183703)
                ·
                  refine ⟨2187433065286300650275555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458288710190867100183703 2187433065286300650275555)
                  ·
                    refine ⟨3281149597929450975413333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2187433065286300650275555 3281149597929450975413333)
                    ·
                      refine ⟨38450971850735753618125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 3281149597929450975413333 38450971850735753618125)
                      ·
                        rfl

theorem cell23_74883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_74883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74883 prefixEnd_74883 := by exact prefixLift 74883
  have htrace : WordTrace (prefixWord ++ tailWord_74883) baseStart_74883 baseEnd_74883 := by
    simpa [prefixWord, tailWord_74883, baseEnd_74883] using wordTrace_append hprefix tailTrace_74883
  have hstable : (prefixWord ++ tailWord_74883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74883).length < 2 ^ (prefixWord ++ tailWord_74883).sum := by decide
  have hdescent : baseEnd_74883 < baseStart_74883 := by decide
  rcases family_descends (prefixWord ++ tailWord_74883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74884 : List Nat := [2, 3, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_74884 : Nat := 118140960795 + 74884 * 2 ^ 59
def prefixEnd_74884 : Nat := 4983230072969 + 3 ^ 40 * 74884 * 2
def baseEnd_74884 : Nat := 12817161777130083235207

theorem tailTrace_74884 : CollatzResearch.WordTrace tailWord_74884 prefixEnd_74884 12817161777130083235207 := by
  unfold tailWord_74884
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365621930357766007055853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1820829240477021342741137 1365621930357766007055853)
  ·
    refine ⟨512108223884162252645945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1365621930357766007055853 512108223884162252645945)
    ·
      refine ⟨384081167913121689484459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 512108223884162252645945 384081167913121689484459)
      ·
        refine ⟨576121751869682534226689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384081167913121689484459 576121751869682534226689)
        ·
          refine ⟨432091313902261900670017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 576121751869682534226689 432091313902261900670017)
          ·
            refine ⟨324068485426696425502513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432091313902261900670017 324068485426696425502513)
            ·
              refine ⟨243051364070022319126885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324068485426696425502513 243051364070022319126885)
              ·
                refine ⟨45572130763129184836291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243051364070022319126885 45572130763129184836291)
                ·
                  refine ⟨68358196144693777254437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45572130763129184836291 68358196144693777254437)
                  ·
                    refine ⟨12817161777130083235207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68358196144693777254437 12817161777130083235207)
                    ·
                      rfl

theorem cell23_74884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_74884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74884 prefixEnd_74884 := by exact prefixLift 74884
  have htrace : WordTrace (prefixWord ++ tailWord_74884) baseStart_74884 baseEnd_74884 := by
    simpa [prefixWord, tailWord_74884, baseEnd_74884] using wordTrace_append hprefix tailTrace_74884
  have hstable : (prefixWord ++ tailWord_74884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74884).length < 2 ^ (prefixWord ++ tailWord_74884).sum := by decide
  have hdescent : baseEnd_74884 < baseStart_74884 := by decide
  rcases family_descends (prefixWord ++ tailWord_74884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74917 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 1, 5, 2]
def baseStart_74917 : Nat := 118140960795 + 74917 * 2 ^ 59
def prefixEnd_74917 : Nat := 4983230072969 + 3 ^ 40 * 74917 * 2
def baseEnd_74917 : Nat := 38468430192988620592969

theorem tailTrace_74917 : CollatzResearch.WordTrace tailWord_74917 prefixEnd_74917 38468430192988620592969 := by
  unfold tailWord_74917
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732447469595978650063005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1821631646397319100042003 2732447469595978650063005)
  ·
    refine ⟨1024667801098491993773627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2732447469595978650063005 1024667801098491993773627)
    ·
      refine ⟨1537001701647737990660441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024667801098491993773627 1537001701647737990660441)
      ·
        refine ⟨1152751276235803492995331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1537001701647737990660441 1152751276235803492995331)
        ·
          refine ⟨1729126914353705239492997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152751276235803492995331 1729126914353705239492997)
          ·
            refine ⟨324211296441319732404937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1729126914353705239492997 324211296441319732404937)
            ·
              refine ⟨243158472330989799303703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324211296441319732404937 243158472330989799303703)
              ·
                refine ⟨364737708496484698955555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243158472330989799303703 364737708496484698955555)
                ·
                  refine ⟨547106562744727048433333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364737708496484698955555 547106562744727048433333)
                  ·
                    refine ⟨51291240257318160790625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 547106562744727048433333 51291240257318160790625)
                    ·
                      refine ⟨38468430192988620592969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51291240257318160790625 38468430192988620592969)
                      ·
                        rfl

theorem cell23_74917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_74917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74917 prefixEnd_74917 := by exact prefixLift 74917
  have htrace : WordTrace (prefixWord ++ tailWord_74917) baseStart_74917 baseEnd_74917 := by
    simpa [prefixWord, tailWord_74917, baseEnd_74917] using wordTrace_append hprefix tailTrace_74917
  have hstable : (prefixWord ++ tailWord_74917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74917).length < 2 ^ (prefixWord ++ tailWord_74917).sum := by decide
  have hdescent : baseEnd_74917 < baseStart_74917 := by decide
  rcases family_descends (prefixWord ++ tailWord_74917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74924 : List Nat := [2, 2, 1, 1, 1, 1, 1, 9, 1, 1, 3]
def baseStart_74924 : Nat := 118140960795 + 74924 * 2 ^ 59
def prefixEnd_74924 : Nat := 4983230072969 + 3 ^ 40 * 74924 * 2
def baseEnd_74924 : Nat := 38472024557570093205437

theorem tailTrace_74924 : CollatzResearch.WordTrace tailWord_74924 prefixEnd_74924 38472024557570093205437 := by
  unfold tailWord_74924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1366351390285309422783913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1821801853713745897045217 1366351390285309422783913)
  ·
    refine ⟨1024763542713982067087935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1366351390285309422783913 1024763542713982067087935)
    ·
      refine ⟨1537145314070973100631903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024763542713982067087935 1537145314070973100631903)
      ·
        refine ⟨2305717971106459650947855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1537145314070973100631903 2305717971106459650947855)
        ·
          refine ⟨3458576956659689476421783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2305717971106459650947855 3458576956659689476421783)
          ·
            refine ⟨5187865434989534214632675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3458576956659689476421783 5187865434989534214632675)
            ·
              refine ⟨7781798152484301321949013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5187865434989534214632675 7781798152484301321949013)
              ·
                refine ⟨45596473549712703058295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7781798152484301321949013 45596473549712703058295)
                ·
                  refine ⟨68394710324569054587443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45596473549712703058295 68394710324569054587443)
                  ·
                    refine ⟨102592065486853581881165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68394710324569054587443 102592065486853581881165)
                    ·
                      refine ⟨38472024557570093205437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 102592065486853581881165 38472024557570093205437)
                      ·
                        rfl

theorem cell23_74924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 1, 1, 3].length) (baseStart_74924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74924 prefixEnd_74924 := by exact prefixLift 74924
  have htrace : WordTrace (prefixWord ++ tailWord_74924) baseStart_74924 baseEnd_74924 := by
    simpa [prefixWord, tailWord_74924, baseEnd_74924] using wordTrace_append hprefix tailTrace_74924
  have hstable : (prefixWord ++ tailWord_74924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74924).length < 2 ^ (prefixWord ++ tailWord_74924).sum := by decide
  have hdescent : baseEnd_74924 < baseStart_74924 := by decide
  rcases family_descends (prefixWord ++ tailWord_74924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74977 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_74977 : Nat := 118140960795 + 74977 * 2 ^ 59
def prefixEnd_74977 : Nat := 4983230072969 + 3 ^ 40 * 74977 * 2
def baseEnd_74977 : Nat := 38499239032258385842693

theorem tailTrace_74977 : CollatzResearch.WordTrace tailWord_74977 prefixEnd_74977 38499239032258385842693 := by
  unfold tailWord_74977
  simp only [CollatzResearch.WordTrace]
  refine ⟨2734635849378608897247185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1823090566252405931498123 2734635849378608897247185)
  ·
    refine ⟨2050976887033956672935389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2734635849378608897247185 2050976887033956672935389)
    ·
      refine ⟨769116332637733752350771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2050976887033956672935389 769116332637733752350771)
      ·
        refine ⟨1153674498956600628526157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769116332637733752350771 1153674498956600628526157)
        ·
          refine ⟨432627937108725235697309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1153674498956600628526157 432627937108725235697309)
          ·
            refine ⟨162235476415771963386491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 432627937108725235697309 162235476415771963386491)
            ·
              refine ⟨243353214623657945079737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162235476415771963386491 243353214623657945079737)
              ·
                refine ⟨182514910967743458809803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243353214623657945079737 182514910967743458809803)
                ·
                  refine ⟨273772366451615188214705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182514910967743458809803 273772366451615188214705)
                  ·
                    refine ⟨205329274838711391161029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 273772366451615188214705 205329274838711391161029)
                    ·
                      refine ⟨38499239032258385842693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 205329274838711391161029 38499239032258385842693)
                      ·
                        rfl

theorem cell23_74977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_74977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74977 prefixEnd_74977 := by exact prefixLift 74977
  have htrace : WordTrace (prefixWord ++ tailWord_74977) baseStart_74977 baseEnd_74977 := by
    simpa [prefixWord, tailWord_74977, baseEnd_74977] using wordTrace_append hprefix tailTrace_74977
  have hstable : (prefixWord ++ tailWord_74977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74977).length < 2 ^ (prefixWord ++ tailWord_74977).sum := by decide
  have hdescent : baseEnd_74977 < baseStart_74977 := by decide
  rcases family_descends (prefixWord ++ tailWord_74977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74981 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 1, 1, 4]
def baseStart_74981 : Nat := 118140960795 + 74981 * 2 ^ 59
def prefixEnd_74981 : Nat := 4983230072969 + 3 ^ 40 * 74981 * 2
def baseEnd_74981 : Nat := 38501292954876370192675

theorem tailTrace_74981 : CollatzResearch.WordTrace tailWord_74981 prefixEnd_74981 38501292954876370192675 := by
  unfold tailWord_74981
  simp only [CollatzResearch.WordTrace]
  refine ⟨2734781741364117580392797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1823187827576078386928531 2734781741364117580392797)
  ·
    refine ⟨1025543153011544092647299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2734781741364117580392797 1025543153011544092647299)
    ·
      refine ⟨1538314729517316138970949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1025543153011544092647299 1538314729517316138970949)
      ·
        refine ⟨288434011784496776057053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1538314729517316138970949 288434011784496776057053)
        ·
          refine ⟨108162754419186291021395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288434011784496776057053 108162754419186291021395)
          ·
            refine ⟨162244131628779436532093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108162754419186291021395 162244131628779436532093)
            ·
              refine ⟨60841549360792288699535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162244131628779436532093 60841549360792288699535)
              ·
                refine ⟨91262324041188433049303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60841549360792288699535 91262324041188433049303)
                ·
                  refine ⟨136893486061782649573955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91262324041188433049303 136893486061782649573955)
                  ·
                    refine ⟨205340229092673974360933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136893486061782649573955 205340229092673974360933)
                    ·
                      refine ⟨38501292954876370192675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 205340229092673974360933 38501292954876370192675)
                      ·
                        rfl

theorem cell23_74981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_74981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_74981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_74981 prefixEnd_74981 := by exact prefixLift 74981
  have htrace : WordTrace (prefixWord ++ tailWord_74981) baseStart_74981 baseEnd_74981 := by
    simpa [prefixWord, tailWord_74981, baseEnd_74981] using wordTrace_append hprefix tailTrace_74981
  have hstable : (prefixWord ++ tailWord_74981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74981).length < 2 ^ (prefixWord ++ tailWord_74981).sum := by decide
  have hdescent : baseEnd_74981 < baseStart_74981 := by decide
  rcases family_descends (prefixWord ++ tailWord_74981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75004 : List Nat := [2, 2, 2, 1, 6, 1, 1, 8]
def baseStart_75004 : Nat := 118140960795 + 75004 * 2 ^ 59
def prefixEnd_75004 : Nat := 4983230072969 + 3 ^ 40 * 75004 * 2
def baseEnd_75004 : Nat := 1426411222589991859447

theorem tailTrace_75004 : CollatzResearch.WordTrace tailWord_75004 prefixEnd_75004 1426411222589991859447 := by
  unfold tailWord_75004
  simp only [CollatzResearch.WordTrace]
  refine ⟨1367810310140396254240033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1823747080187195005653377 1367810310140396254240033)
  ·
    refine ⟨1025857732605297190680025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1367810310140396254240033 1025857732605297190680025)
    ·
      refine ⟨769393299453972893010019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1025857732605297190680025 769393299453972893010019)
      ·
        refine ⟨1154089949180959339515029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769393299453972893010019 1154089949180959339515029)
        ·
          refine ⟨54097966367857469039767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1154089949180959339515029 54097966367857469039767)
          ·
            refine ⟨81146949551786203559651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54097966367857469039767 81146949551786203559651)
            ·
              refine ⟨121720424327679305339477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81146949551786203559651 121720424327679305339477)
              ·
                refine ⟨1426411222589991859447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 121720424327679305339477 1426411222589991859447)
                ·
                  rfl

theorem cell23_75004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 8].length) (baseStart_75004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75004 prefixEnd_75004 := by exact prefixLift 75004
  have htrace : WordTrace (prefixWord ++ tailWord_75004) baseStart_75004 baseEnd_75004 := by
    simpa [prefixWord, tailWord_75004, baseEnd_75004] using wordTrace_append hprefix tailTrace_75004
  have hstable : (prefixWord ++ tailWord_75004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75004).length < 2 ^ (prefixWord ++ tailWord_75004).sum := by decide
  have hdescent : baseEnd_75004 < baseStart_75004 := by decide
  rcases family_descends (prefixWord ++ tailWord_75004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75048 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_75048 : Nat := 118140960795 + 75048 * 2 ^ 59
def prefixEnd_75048 : Nat := 4983230072969 + 3 ^ 40 * 75048 * 2
def baseEnd_75048 : Nat := 38535696158727608054867

theorem tailTrace_75048 : CollatzResearch.WordTrace tailWord_75048 prefixEnd_75048 38535696158727608054867 := by
  unfold tailWord_75048
  simp only [CollatzResearch.WordTrace]
  refine ⟨1368612716060694011540899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1824816954747592015387865 1368612716060694011540899)
  ·
    refine ⟨2052919074091041017311349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1368612716060694011540899 2052919074091041017311349)
    ·
      refine ⟨192461163196035095372939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2052919074091041017311349 192461163196035095372939)
      ·
        refine ⟨288691744794052643059409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192461163196035095372939 288691744794052643059409)
        ·
          refine ⟨216518808595539482294557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288691744794052643059409 216518808595539482294557)
          ·
            refine ⟨81194553223327305860459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216518808595539482294557 81194553223327305860459)
            ·
              refine ⟨121791829834990958790689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81194553223327305860459 121791829834990958790689)
              ·
                refine ⟨91343872376243219093017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121791829834990958790689 91343872376243219093017)
                ·
                  refine ⟨68507904282182414319763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91343872376243219093017 68507904282182414319763)
                  ·
                    refine ⟨102761856423273621479645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68507904282182414319763 102761856423273621479645)
                    ·
                      refine ⟨38535696158727608054867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 102761856423273621479645 38535696158727608054867)
                      ·
                        rfl

theorem cell23_75048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_75048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75048 prefixEnd_75048 := by exact prefixLift 75048
  have htrace : WordTrace (prefixWord ++ tailWord_75048) baseStart_75048 baseEnd_75048 := by
    simpa [prefixWord, tailWord_75048, baseEnd_75048] using wordTrace_append hprefix tailTrace_75048
  have hstable : (prefixWord ++ tailWord_75048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75048).length < 2 ^ (prefixWord ++ tailWord_75048).sum := by decide
  have hdescent : baseEnd_75048 < baseStart_75048 := by decide
  rcases family_descends (prefixWord ++ tailWord_75048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75071 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 1, 4, 2]
def baseStart_75071 : Nat := 118140960795 + 75071 * 2 ^ 59
def prefixEnd_75071 : Nat := 4983230072969 + 3 ^ 40 * 75071 * 2
def baseEnd_75071 : Nat := 38547506213781018067261

theorem tailTrace_75071 : CollatzResearch.WordTrace tailWord_75071 prefixEnd_75071 38547506213781018067261 := by
  unfold tailWord_75071
  simp only [CollatzResearch.WordTrace]
  refine ⟨2738064311038062951169067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1825376207358708634112711 2738064311038062951169067)
  ·
    refine ⟨4107096466557094426753601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2738064311038062951169067 4107096466557094426753601)
    ·
      refine ⟨3080322349917820820065201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4107096466557094426753601 3080322349917820820065201)
      ·
        refine ⟨2310241762438365615048901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3080322349917820820065201 2310241762438365615048901)
        ·
          refine ⟨433170330457193552821669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2310241762438365615048901 433170330457193552821669)
          ·
            refine ⟨81219436960723791154063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 433170330457193552821669 81219436960723791154063)
            ·
              refine ⟨121829155441085686731095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81219436960723791154063 121829155441085686731095)
              ·
                refine ⟨182743733161628530096643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121829155441085686731095 182743733161628530096643)
                ·
                  refine ⟨274115599742442795144965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182743733161628530096643 274115599742442795144965)
                  ·
                    refine ⟨51396674951708024089681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 274115599742442795144965 51396674951708024089681)
                    ·
                      refine ⟨38547506213781018067261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51396674951708024089681 38547506213781018067261)
                      ·
                        rfl

theorem cell23_75071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 4, 2].length) (baseStart_75071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75071 prefixEnd_75071 := by exact prefixLift 75071
  have htrace : WordTrace (prefixWord ++ tailWord_75071) baseStart_75071 baseEnd_75071 := by
    simpa [prefixWord, tailWord_75071, baseEnd_75071] using wordTrace_append hprefix tailTrace_75071
  have hstable : (prefixWord ++ tailWord_75071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75071).length < 2 ^ (prefixWord ++ tailWord_75071).sum := by decide
  have hdescent : baseEnd_75071 < baseStart_75071 := by decide
  rcases family_descends (prefixWord ++ tailWord_75071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75107 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 4, 5]
def baseStart_75107 : Nat := 118140960795 + 75107 * 2 ^ 59
def prefixEnd_75107 : Nat := 4983230072969 + 3 ^ 40 * 75107 * 2
def baseEnd_75107 : Nat := 12855330505780959072365

theorem tailTrace_75107 : CollatzResearch.WordTrace tailWord_75107 prefixEnd_75107 12855330505780959072365 := by
  unfold tailWord_75107
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739377338907641099479575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1826251559271760732986383 2739377338907641099479575)
  ·
    refine ⟨4109066008361461649219363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2739377338907641099479575 4109066008361461649219363)
    ·
      refine ⟨6163599012542192473829045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4109066008361461649219363 6163599012542192473829045)
      ·
        refine ⟨577837407425830544421473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6163599012542192473829045 577837407425830544421473)
        ·
          refine ⟨433378055569372908316105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577837407425830544421473 433378055569372908316105)
          ·
            refine ⟨325033541677029681237079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433378055569372908316105 325033541677029681237079)
            ·
              refine ⟨487550312515544521855619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325033541677029681237079 487550312515544521855619)
              ·
                refine ⟨731325468773316782783429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487550312515544521855619 731325468773316782783429)
                ·
                  refine ⟨137123525394996896771893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731325468773316782783429 137123525394996896771893)
                  ·
                    refine ⟨12855330505780959072365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 137123525394996896771893 12855330505780959072365)
                    ·
                      rfl

theorem cell23_75107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 5].length) (baseStart_75107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75107 prefixEnd_75107 := by exact prefixLift 75107
  have htrace : WordTrace (prefixWord ++ tailWord_75107) baseStart_75107 baseEnd_75107 := by
    simpa [prefixWord, tailWord_75107, baseEnd_75107] using wordTrace_append hprefix tailTrace_75107
  have hstable : (prefixWord ++ tailWord_75107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75107).length < 2 ^ (prefixWord ++ tailWord_75107).sum := by decide
  have hdescent : baseEnd_75107 < baseStart_75107 := by decide
  rcases family_descends (prefixWord ++ tailWord_75107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75111 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 7]
def baseStart_75111 : Nat := 118140960795 + 75111 * 2 ^ 59
def prefixEnd_75111 : Nat := 4983230072969 + 3 ^ 40 * 75111 * 2
def baseEnd_75111 : Nat := 4285338382217873507453

theorem tailTrace_75111 : CollatzResearch.WordTrace tailWord_75111 prefixEnd_75111 4285338382217873507453 := by
  unfold tailWord_75111
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739523230893149782625187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1826348820595433188416791 2739523230893149782625187)
  ·
    refine ⟨4109284846339724673937781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2739523230893149782625187 4109284846339724673937781)
    ·
      refine ⟨385245454344349188181667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4109284846339724673937781 385245454344349188181667)
      ·
        refine ⟨577868181516523782272501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385245454344349188181667 577868181516523782272501)
        ·
          refine ⟨54175142017174104588047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 577868181516523782272501 54175142017174104588047)
          ·
            refine ⟨81262713025761156882071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54175142017174104588047 81262713025761156882071)
            ·
              refine ⟨121894069538641735323107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81262713025761156882071 121894069538641735323107)
              ·
                refine ⟨182841104307962602984661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121894069538641735323107 182841104307962602984661)
                ·
                  refine ⟨4285338382217873507453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 182841104307962602984661 4285338382217873507453)
                  ·
                    rfl

theorem cell23_75111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 7].length) (baseStart_75111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75111 prefixEnd_75111 := by exact prefixLift 75111
  have htrace : WordTrace (prefixWord ++ tailWord_75111) baseStart_75111 baseEnd_75111 := by
    simpa [prefixWord, tailWord_75111, baseEnd_75111] using wordTrace_append hprefix tailTrace_75111
  have hstable : (prefixWord ++ tailWord_75111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75111).length < 2 ^ (prefixWord ++ tailWord_75111).sum := by decide
  have hdescent : baseEnd_75111 < baseStart_75111 := by decide
  rcases family_descends (prefixWord ++ tailWord_75111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75117 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_75117 : Nat := 118140960795 + 75117 * 2 ^ 59
def prefixEnd_75117 : Nat := 4983230072969 + 3 ^ 40 * 75117 * 2
def baseEnd_75117 : Nat := 38571126323887838092049

theorem tailTrace_75117 : CollatzResearch.WordTrace tailWord_75117 prefixEnd_75117 38571126323887838092049 := by
  unfold tailWord_75117
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739742068871412807343605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1826494712580941871562403 2739742068871412807343605)
  ·
    refine ⟨256850818956694950688463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2739742068871412807343605 256850818956694950688463)
    ·
      refine ⟨385276228435042426032695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256850818956694950688463 385276228435042426032695)
      ·
        refine ⟨577914342652563639049043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385276228435042426032695 577914342652563639049043)
        ·
          refine ⟨866871513978845458573565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577914342652563639049043 866871513978845458573565)
          ·
            refine ⟨325076817742067046965087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 866871513978845458573565 325076817742067046965087)
            ·
              refine ⟨487615226613100570447631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325076817742067046965087 487615226613100570447631)
              ·
                refine ⟨731422839919650855671447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487615226613100570447631 731422839919650855671447)
                ·
                  refine ⟨1097134259879476283507171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731422839919650855671447 1097134259879476283507171)
                  ·
                    refine ⟨1645701389819214425260757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1097134259879476283507171 1645701389819214425260757)
                    ·
                      refine ⟨38571126323887838092049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1645701389819214425260757 38571126323887838092049)
                      ·
                        rfl

theorem cell23_75117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_75117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75117 prefixEnd_75117 := by exact prefixLift 75117
  have htrace : WordTrace (prefixWord ++ tailWord_75117) baseStart_75117 baseEnd_75117 := by
    simpa [prefixWord, tailWord_75117, baseEnd_75117] using wordTrace_append hprefix tailTrace_75117
  have hstable : (prefixWord ++ tailWord_75117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75117).length < 2 ^ (prefixWord ++ tailWord_75117).sum := by decide
  have hdescent : baseEnd_75117 < baseStart_75117 := by decide
  rcases family_descends (prefixWord ++ tailWord_75117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75127 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_75127 : Nat := 118140960795 + 75127 * 2 ^ 59
def prefixEnd_75127 : Nat := 4983230072969 + 3 ^ 40 * 75127 * 2
def baseEnd_75127 : Nat := 38576261130432798967003

theorem tailTrace_75127 : CollatzResearch.WordTrace tailWord_75127 prefixEnd_75127 38576261130432798967003 := by
  unfold tailWord_75127
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740106798835184515207635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1826737865890123010138423 2740106798835184515207635)
  ·
    refine ⟨4110160198252776772811453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2740106798835184515207635 4110160198252776772811453)
    ·
      refine ⟨1541310074344791289804295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4110160198252776772811453 1541310074344791289804295)
      ·
        refine ⟨2311965111517186934706443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541310074344791289804295 2311965111517186934706443)
        ·
          refine ⟨3467947667275780402059665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311965111517186934706443 3467947667275780402059665)
          ·
            refine ⟨2600960750456835301544749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3467947667275780402059665 2600960750456835301544749)
            ·
              refine ⟨975360281421313238079281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2600960750456835301544749 975360281421313238079281)
              ·
                refine ⟨731520211065984928559461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975360281421313238079281 731520211065984928559461)
                ·
                  refine ⟨137160039574872174104899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731520211065984928559461 137160039574872174104899)
                  ·
                    refine ⟨205740059362308261157349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137160039574872174104899 205740059362308261157349)
                    ·
                      refine ⟨38576261130432798967003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 205740059362308261157349 38576261130432798967003)
                      ·
                        rfl

theorem cell23_75127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_75127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75127 prefixEnd_75127 := by exact prefixLift 75127
  have htrace : WordTrace (prefixWord ++ tailWord_75127) baseStart_75127 baseEnd_75127 := by
    simpa [prefixWord, tailWord_75127, baseEnd_75127] using wordTrace_append hprefix tailTrace_75127
  have hstable : (prefixWord ++ tailWord_75127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75127).length < 2 ^ (prefixWord ++ tailWord_75127).sum := by decide
  have hdescent : baseEnd_75127 < baseStart_75127 := by decide
  rcases family_descends (prefixWord ++ tailWord_75127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75144 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_75144 : Nat := 118140960795 + 75144 * 2 ^ 59
def prefixEnd_75144 : Nat := 4983230072969 + 3 ^ 40 * 75144 * 2
def baseEnd_75144 : Nat := 38584990301559232454425

theorem tailTrace_75144 : CollatzResearch.WordTrace tailWord_75144 prefixEnd_75144 38584990301559232454425 := by
  unfold tailWord_75144
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370363419886798209288243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1827151226515730945717657 1370363419886798209288243)
  ·
    refine ⟨2055545129830197313932365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1370363419886798209288243 2055545129830197313932365)
    ·
      refine ⟨770829423686323992724637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2055545129830197313932365 770829423686323992724637)
      ·
        refine ⟨289061033882371497271739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 770829423686323992724637 289061033882371497271739)
        ·
          refine ⟨433591550823557245907609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289061033882371497271739 433591550823557245907609)
          ·
            refine ⟨325193663117667934430707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433591550823557245907609 325193663117667934430707)
            ·
              refine ⟨487790494676501901646061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325193663117667934430707 487790494676501901646061)
              ·
                refine ⟨182921435503688213117273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 487790494676501901646061 182921435503688213117273)
                ·
                  refine ⟨137191076627766159837955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182921435503688213117273 137191076627766159837955)
                  ·
                    refine ⟨205786614941649239756933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137191076627766159837955 205786614941649239756933)
                    ·
                      refine ⟨38584990301559232454425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 205786614941649239756933 38584990301559232454425)
                      ·
                        rfl

theorem cell23_75144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_75144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75144 prefixEnd_75144 := by exact prefixLift 75144
  have htrace : WordTrace (prefixWord ++ tailWord_75144) baseStart_75144 baseEnd_75144 := by
    simpa [prefixWord, tailWord_75144, baseEnd_75144] using wordTrace_append hprefix tailTrace_75144
  have hstable : (prefixWord ++ tailWord_75144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75144).length < 2 ^ (prefixWord ++ tailWord_75144).sum := by decide
  have hdescent : baseEnd_75144 < baseStart_75144 := by decide
  rcases family_descends (prefixWord ++ tailWord_75144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75171 : List Nat := [1, 1, 1, 4, 1, 3, 3, 4, 1, 4]
def baseStart_75171 : Nat := 118140960795 + 75171 * 2 ^ 59
def prefixEnd_75171 : Nat := 4983230072969 + 3 ^ 40 * 75171 * 2
def baseEnd_75171 : Nat := 12866284759743542272267

theorem tailTrace_75171 : CollatzResearch.WordTrace tailWord_75171 prefixEnd_75171 12866284759743542272267 := by
  unfold tailWord_75171
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741711610675780029809367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1827807740450520019872911 2741711610675780029809367)
  ·
    refine ⟨4112567416013670044714051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2741711610675780029809367 4112567416013670044714051)
    ·
      refine ⟨6168851124020505067071077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4112567416013670044714051 6168851124020505067071077)
      ·
        refine ⟨1156659585753844700075827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6168851124020505067071077 1156659585753844700075827)
        ·
          refine ⟨1734989378630767050113741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156659585753844700075827 1734989378630767050113741)
          ·
            refine ⟨650621016986537643792653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1734989378630767050113741 650621016986537643792653)
            ·
              refine ⟨243982881369951616422245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 650621016986537643792653 243982881369951616422245)
              ·
                refine ⟨45746790256865928079171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243982881369951616422245 45746790256865928079171)
                ·
                  refine ⟨68620185385298892118757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45746790256865928079171 68620185385298892118757)
                  ·
                    refine ⟨12866284759743542272267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68620185385298892118757 12866284759743542272267)
                    ·
                      rfl

theorem cell23_75171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 1, 4].length) (baseStart_75171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75171 prefixEnd_75171 := by exact prefixLift 75171
  have htrace : WordTrace (prefixWord ++ tailWord_75171) baseStart_75171 baseEnd_75171 := by
    simpa [prefixWord, tailWord_75171, baseEnd_75171] using wordTrace_append hprefix tailTrace_75171
  have hstable : (prefixWord ++ tailWord_75171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75171).length < 2 ^ (prefixWord ++ tailWord_75171).sum := by decide
  have hdescent : baseEnd_75171 < baseStart_75171 := by decide
  rcases family_descends (prefixWord ++ tailWord_75171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75177 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 4, 5, 3]
def baseStart_75177 : Nat := 118140960795 + 75177 * 2 ^ 59
def prefixEnd_75177 : Nat := 4983230072969 + 3 ^ 40 * 75177 * 2
def baseEnd_75177 : Nat := 38601935163157603341773

theorem tailTrace_75177 : CollatzResearch.WordTrace tailWord_75177 prefixEnd_75177 38601935163157603341773 := by
  unfold tailWord_75177
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741930448654043054527785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1827953632436028703018523 2741930448654043054527785)
  ·
    refine ⟨2056447836490532290895839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2741930448654043054527785 2056447836490532290895839)
    ·
      refine ⟨3084671754735798436343759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2056447836490532290895839 3084671754735798436343759)
      ·
        refine ⟨4627007632103697654515639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3084671754735798436343759 4627007632103697654515639)
        ·
          refine ⟨6940511448155546481773459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4627007632103697654515639 6940511448155546481773459)
          ·
            refine ⟨10410767172233319722660189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6940511448155546481773459 10410767172233319722660189)
            ·
              refine ⟨3904037689587494895997571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10410767172233319722660189 3904037689587494895997571)
              ·
                refine ⟨5856056534381242343996357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904037689587494895997571 5856056534381242343996357)
                ·
                  refine ⟨1098010600196482939499317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5856056534381242343996357 1098010600196482939499317)
                  ·
                    refine ⟨102938493768420275578061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1098010600196482939499317 102938493768420275578061)
                    ·
                      refine ⟨38601935163157603341773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 102938493768420275578061 38601935163157603341773)
                      ·
                        rfl

theorem cell23_75177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5, 3].length) (baseStart_75177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75177 prefixEnd_75177 := by exact prefixLift 75177
  have htrace : WordTrace (prefixWord ++ tailWord_75177) baseStart_75177 baseEnd_75177 := by
    simpa [prefixWord, tailWord_75177, baseEnd_75177] using wordTrace_append hprefix tailTrace_75177
  have hstable : (prefixWord ++ tailWord_75177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75177).length < 2 ^ (prefixWord ++ tailWord_75177).sum := by decide
  have hdescent : baseEnd_75177 < baseStart_75177 := by decide
  rcases family_descends (prefixWord ++ tailWord_75177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75221 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 4, 3, 2]
def baseStart_75221 : Nat := 118140960795 + 75221 * 2 ^ 59
def prefixEnd_75221 : Nat := 4983230072969 + 3 ^ 40 * 75221 * 2
def baseEnd_75221 : Nat := 38624528311955431191571

theorem tailTrace_75221 : CollatzResearch.WordTrace tailWord_75221 prefixEnd_75221 38624528311955431191571 := by
  unfold tailWord_75221
  simp only [CollatzResearch.WordTrace]
  refine ⟨2743535260494638569129517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1829023506996425712753011 2743535260494638569129517)
  ·
    refine ⟨1028825722685489463423569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2743535260494638569129517 1028825722685489463423569)
    ·
      refine ⟨771619292014117097567677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1028825722685489463423569 771619292014117097567677)
      ·
        refine ⟨289357234505293911587879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 771619292014117097567677 289357234505293911587879)
        ·
          refine ⟨434035851757940867381819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289357234505293911587879 434035851757940867381819)
          ·
            refine ⟨651053777636911301072729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434035851757940867381819 651053777636911301072729)
            ·
              refine ⟨488290333227683475804547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651053777636911301072729 488290333227683475804547)
              ·
                refine ⟨732435499841525213706821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488290333227683475804547 732435499841525213706821)
                ·
                  refine ⟨137331656220285977570029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 732435499841525213706821 137331656220285977570029)
                  ·
                    refine ⟨51499371082607241588761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 137331656220285977570029 51499371082607241588761)
                    ·
                      refine ⟨38624528311955431191571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51499371082607241588761 38624528311955431191571)
                      ·
                        rfl

theorem cell23_75221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_75221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75221 prefixEnd_75221 := by exact prefixLift 75221
  have htrace : WordTrace (prefixWord ++ tailWord_75221) baseStart_75221 baseEnd_75221 := by
    simpa [prefixWord, tailWord_75221, baseEnd_75221] using wordTrace_append hprefix tailTrace_75221
  have hstable : (prefixWord ++ tailWord_75221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75221).length < 2 ^ (prefixWord ++ tailWord_75221).sum := by decide
  have hdescent : baseEnd_75221 < baseStart_75221 := by decide
  rcases family_descends (prefixWord ++ tailWord_75221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75251 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 5, 2, 2]
def baseStart_75251 : Nat := 118140960795 + 75251 * 2 ^ 59
def prefixEnd_75251 : Nat := 4983230072969 + 3 ^ 40 * 75251 * 2
def baseEnd_75251 : Nat := 38639932731590313816433

theorem tailTrace_75251 : CollatzResearch.WordTrace tailWord_75251 prefixEnd_75251 38639932731590313816433 := by
  unfold tailWord_75251
  simp only [CollatzResearch.WordTrace]
  refine ⟨2744629450385953692721607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1829752966923969128481071 2744629450385953692721607)
  ·
    refine ⟨4116944175578930539082411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2744629450385953692721607 4116944175578930539082411)
    ·
      refine ⟨6175416263368395808623617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4116944175578930539082411 6175416263368395808623617)
      ·
        refine ⟨4631562197526296856467713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6175416263368395808623617 4631562197526296856467713)
        ·
          refine ⟨3473671648144722642350785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4631562197526296856467713 3473671648144722642350785)
          ·
            refine ⟨2605253736108541981763089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3473671648144722642350785 2605253736108541981763089)
            ·
              refine ⟨1953940302081406486322317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2605253736108541981763089 1953940302081406486322317)
              ·
                refine ⟨732727613280527432370869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1953940302081406486322317 732727613280527432370869)
                ·
                  refine ⟨68693213745049446784769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 732727613280527432370869 68693213745049446784769)
                  ·
                    refine ⟨51519910308787085088577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68693213745049446784769 51519910308787085088577)
                    ·
                      refine ⟨38639932731590313816433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51519910308787085088577 38639932731590313816433)
                      ·
                        rfl

theorem cell23_75251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 2, 2].length) (baseStart_75251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75251 prefixEnd_75251 := by exact prefixLift 75251
  have htrace : WordTrace (prefixWord ++ tailWord_75251) baseStart_75251 baseEnd_75251 := by
    simpa [prefixWord, tailWord_75251, baseEnd_75251] using wordTrace_append hprefix tailTrace_75251
  have hstable : (prefixWord ++ tailWord_75251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75251).length < 2 ^ (prefixWord ++ tailWord_75251).sum := by decide
  have hdescent : baseEnd_75251 < baseStart_75251 := by decide
  rcases family_descends (prefixWord ++ tailWord_75251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75271 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_75271 : Nat := 118140960795 + 75271 * 2 ^ 59
def prefixEnd_75271 : Nat := 4983230072969 + 3 ^ 40 * 75271 * 2
def baseEnd_75271 : Nat := 38650202344680235566341

theorem tailTrace_75271 : CollatzResearch.WordTrace tailWord_75271 prefixEnd_75271 38650202344680235566341 := by
  unfold tailWord_75271
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745358910313497108449667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1830239273542331405633111 2745358910313497108449667)
  ·
    refine ⟨4118038365470245662674501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2745358910313497108449667 4118038365470245662674501)
    ·
      refine ⟨772132193525671061751469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4118038365470245662674501 772132193525671061751469)
      ·
        refine ⟨289549572572126648156801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 772132193525671061751469 289549572572126648156801)
        ·
          refine ⟨217162179429094986117601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289549572572126648156801 217162179429094986117601)
          ·
            refine ⟨162871634571821239588201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217162179429094986117601 162871634571821239588201)
            ·
              refine ⟨122153725928865929691151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162871634571821239588201 122153725928865929691151)
              ·
                refine ⟨183230588893298894536727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122153725928865929691151 183230588893298894536727)
                ·
                  refine ⟨274845883339948341805091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183230588893298894536727 274845883339948341805091)
                  ·
                    refine ⟨412268825009922512707637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274845883339948341805091 412268825009922512707637)
                    ·
                      refine ⟨38650202344680235566341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 412268825009922512707637 38650202344680235566341)
                      ·
                        rfl

theorem cell23_75271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_75271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75271 prefixEnd_75271 := by exact prefixLift 75271
  have htrace : WordTrace (prefixWord ++ tailWord_75271) baseStart_75271 baseEnd_75271 := by
    simpa [prefixWord, tailWord_75271, baseEnd_75271] using wordTrace_append hprefix tailTrace_75271
  have hstable : (prefixWord ++ tailWord_75271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75271).length < 2 ^ (prefixWord ++ tailWord_75271).sum := by decide
  have hdescent : baseEnd_75271 < baseStart_75271 := by decide
  rcases family_descends (prefixWord ++ tailWord_75271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75274 : List Nat := [3, 1, 2, 2, 2, 4, 9]
def baseStart_75274 : Nat := 118140960795 + 75274 * 2 ^ 59
def prefixEnd_75274 : Nat := 4983230072969 + 3 ^ 40 * 75274 * 2
def baseEnd_75274 : Nat := 477182009711650911467

theorem tailTrace_75274 : CollatzResearch.WordTrace tailWord_75274 prefixEnd_75274 477182009711650911467 := by
  unfold tailWord_75274
  simp only [CollatzResearch.WordTrace]
  refine ⟨686367082325657155202219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1830312219535085747205917 686367082325657155202219)
  ·
    refine ⟨1029550623488485732803329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 686367082325657155202219 1029550623488485732803329)
    ·
      refine ⟨772162967616364299602497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1029550623488485732803329 772162967616364299602497)
      ·
        refine ⟨579122225712273224701873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 772162967616364299602497 579122225712273224701873)
        ·
          refine ⟨434341669284204918526405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 579122225712273224701873 434341669284204918526405)
          ·
            refine ⟨81439062990788422223701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 434341669284204918526405 81439062990788422223701)
            ·
              refine ⟨477182009711650911467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 81439062990788422223701 477182009711650911467)
              ·
                rfl

theorem cell23_75274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 9].length) (baseStart_75274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75274 prefixEnd_75274 := by exact prefixLift 75274
  have htrace : WordTrace (prefixWord ++ tailWord_75274) baseStart_75274 baseEnd_75274 := by
    simpa [prefixWord, tailWord_75274, baseEnd_75274] using wordTrace_append hprefix tailTrace_75274
  have hstable : (prefixWord ++ tailWord_75274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75274).length < 2 ^ (prefixWord ++ tailWord_75274).sum := by decide
  have hdescent : baseEnd_75274 < baseStart_75274 := by decide
  rcases family_descends (prefixWord ++ tailWord_75274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75285 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 3, 2, 2]
def baseStart_75285 : Nat := 118140960795 + 75285 * 2 ^ 59
def prefixEnd_75285 : Nat := 4983230072969 + 3 ^ 40 * 75285 * 2
def baseEnd_75285 : Nat := 38657391073843180791277

theorem tailTrace_75285 : CollatzResearch.WordTrace tailWord_75285 prefixEnd_75285 38657391073843180791277 := by
  unfold tailWord_75285
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745869532262777499459309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1830579688175184999639539 2745869532262777499459309)
  ·
    refine ⟨1029701074598541562297241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2745869532262777499459309 1029701074598541562297241)
    ·
      refine ⟨772275805948906171722931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1029701074598541562297241 772275805948906171722931)
      ·
        refine ⟨1158413708923359257584397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 772275805948906171722931 1158413708923359257584397)
        ·
          refine ⟨434405140846259721594149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1158413708923359257584397 434405140846259721594149)
          ·
            refine ⟨81450963908673697798903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 434405140846259721594149 81450963908673697798903)
            ·
              refine ⟨122176445863010546698355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81450963908673697798903 122176445863010546698355)
              ·
                refine ⟨183264668794515820047533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122176445863010546698355 183264668794515820047533)
                ·
                  refine ⟨68724250797943432517825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183264668794515820047533 68724250797943432517825)
                  ·
                    refine ⟨51543188098457574388369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68724250797943432517825 51543188098457574388369)
                    ·
                      refine ⟨38657391073843180791277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51543188098457574388369 38657391073843180791277)
                      ·
                        rfl

theorem cell23_75285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_75285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75285 prefixEnd_75285 := by exact prefixLift 75285
  have htrace : WordTrace (prefixWord ++ tailWord_75285) baseStart_75285 baseEnd_75285 := by
    simpa [prefixWord, tailWord_75285, baseEnd_75285] using wordTrace_append hprefix tailTrace_75285
  have hstable : (prefixWord ++ tailWord_75285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75285).length < 2 ^ (prefixWord ++ tailWord_75285).sum := by decide
  have hdescent : baseEnd_75285 < baseStart_75285 := by decide
  rcases family_descends (prefixWord ++ tailWord_75285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75307 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 10]
def baseStart_75307 : Nat := 118140960795 + 75307 * 2 ^ 59
def prefixEnd_75307 : Nat := 4983230072969 + 3 ^ 40 * 75307 * 2
def baseEnd_75307 : Nat := 38668687648242094716175

theorem tailTrace_75307 : CollatzResearch.WordTrace tailWord_75307 prefixEnd_75307 38668687648242094716175 := by
  unfold tailWord_75307
  simp only [CollatzResearch.WordTrace]
  refine ⟨2746671938183075256760175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1831114625455383504506783 2746671938183075256760175)
  ·
    refine ⟨4120007907274612885140263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2746671938183075256760175 4120007907274612885140263)
    ·
      refine ⟨6180011860911919327710395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4120007907274612885140263 6180011860911919327710395)
      ·
        refine ⟨9270017791367878991565593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6180011860911919327710395 9270017791367878991565593)
        ·
          refine ⟨6952513343525909243674195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9270017791367878991565593 6952513343525909243674195)
          ·
            refine ⟨10428770015288863865511293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6952513343525909243674195 10428770015288863865511293)
            ·
              refine ⟨3910788755733323949566735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10428770015288863865511293 3910788755733323949566735)
              ·
                refine ⟨5866183133599985924350103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3910788755733323949566735 5866183133599985924350103)
                ·
                  refine ⟨8799274700399978886525155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5866183133599985924350103 8799274700399978886525155)
                  ·
                    refine ⟨13198912050599968329787733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8799274700399978886525155 13198912050599968329787733)
                    ·
                      refine ⟨38668687648242094716175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 13198912050599968329787733 38668687648242094716175)
                      ·
                        rfl

theorem cell23_75307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_75307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75307 prefixEnd_75307 := by exact prefixLift 75307
  have htrace : WordTrace (prefixWord ++ tailWord_75307) baseStart_75307 baseEnd_75307 := by
    simpa [prefixWord, tailWord_75307, baseEnd_75307] using wordTrace_append hprefix tailTrace_75307
  have hstable : (prefixWord ++ tailWord_75307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75307).length < 2 ^ (prefixWord ++ tailWord_75307).sum := by decide
  have hdescent : baseEnd_75307 < baseStart_75307 := by decide
  rcases family_descends (prefixWord ++ tailWord_75307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75335 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_75335 : Nat := 118140960795 + 75335 * 2 ^ 59
def prefixEnd_75335 : Nat := 4983230072969 + 3 ^ 40 * 75335 * 2
def baseEnd_75335 : Nat := 38683065106567985166047

theorem tailTrace_75335 : CollatzResearch.WordTrace tailWord_75335 prefixEnd_75335 38683065106567985166047 := by
  unfold tailWord_75335
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747693182081636038779459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1831795454721090692519639 2747693182081636038779459)
  ·
    refine ⟨4121539773122454058169189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2747693182081636038779459 4121539773122454058169189)
    ·
      refine ⟨772788707460460135906723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4121539773122454058169189 772788707460460135906723)
      ·
        refine ⟨1159183061190690203860085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 772788707460460135906723 1159183061190690203860085)
        ·
          refine ⟨108673411986627206611883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1159183061190690203860085 108673411986627206611883)
          ·
            refine ⟨163010117979940809917825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108673411986627206611883 163010117979940809917825)
            ·
              refine ⟨122257588484955607438369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163010117979940809917825 122257588484955607438369)
              ·
                refine ⟨91693191363716705578777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122257588484955607438369 91693191363716705578777)
                ·
                  refine ⟨68769893522787529184083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91693191363716705578777 68769893522787529184083)
                  ·
                    refine ⟨103154840284181293776125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68769893522787529184083 103154840284181293776125)
                    ·
                      refine ⟨38683065106567985166047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 103154840284181293776125 38683065106567985166047)
                      ·
                        rfl

theorem cell23_75335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_75335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75335 prefixEnd_75335 := by exact prefixLift 75335
  have htrace : WordTrace (prefixWord ++ tailWord_75335) baseStart_75335 baseEnd_75335 := by
    simpa [prefixWord, tailWord_75335, baseEnd_75335] using wordTrace_append hprefix tailTrace_75335
  have hstable : (prefixWord ++ tailWord_75335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75335).length < 2 ^ (prefixWord ++ tailWord_75335).sum := by decide
  have hdescent : baseEnd_75335 < baseStart_75335 := by decide
  rcases family_descends (prefixWord ++ tailWord_75335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75344 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 3]
def baseStart_75344 : Nat := 118140960795 + 75344 * 2 ^ 59
def prefixEnd_75344 : Nat := 4983230072969 + 3 ^ 40 * 75344 * 2
def baseEnd_75344 : Nat := 38687686432458449953505

theorem tailTrace_75344 : CollatzResearch.WordTrace tailWord_75344 prefixEnd_75344 38687686432458449953505 := by
  unfold tailWord_75344
  simp only [CollatzResearch.WordTrace]
  refine ⟨1374010719524515287928543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1832014292699353717238057 1374010719524515287928543)
  ·
    refine ⟨2061016079286772931892815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1374010719524515287928543 2061016079286772931892815)
    ·
      refine ⟨3091524118930159397839223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2061016079286772931892815 3091524118930159397839223)
      ·
        refine ⟨4637286178395239096758835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3091524118930159397839223 4637286178395239096758835)
        ·
          refine ⟨6955929267592858645138253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4637286178395239096758835 6955929267592858645138253)
          ·
            refine ⟨2608473475347321991926845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6955929267592858645138253 2608473475347321991926845)
            ·
              refine ⟨978177553255245746972567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2608473475347321991926845 978177553255245746972567)
              ·
                refine ⟨1467266329882868620458851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978177553255245746972567 1467266329882868620458851)
                ·
                  refine ⟨2200899494824302930688277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467266329882868620458851 2200899494824302930688277)
                  ·
                    refine ⟨103167163819889199876013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2200899494824302930688277 103167163819889199876013)
                    ·
                      refine ⟨38687686432458449953505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 103167163819889199876013 38687686432458449953505)
                      ·
                        rfl

theorem cell23_75344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 3].length) (baseStart_75344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75344 prefixEnd_75344 := by exact prefixLift 75344
  have htrace : WordTrace (prefixWord ++ tailWord_75344) baseStart_75344 baseEnd_75344 := by
    simpa [prefixWord, tailWord_75344, baseEnd_75344] using wordTrace_append hprefix tailTrace_75344
  have hstable : (prefixWord ++ tailWord_75344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75344).length < 2 ^ (prefixWord ++ tailWord_75344).sum := by decide
  have hdescent : baseEnd_75344 < baseStart_75344 := by decide
  rcases family_descends (prefixWord ++ tailWord_75344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75364 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 9]
def baseStart_75364 : Nat := 118140960795 + 75364 * 2 ^ 59
def prefixEnd_75364 : Nat := 4983230072969 + 3 ^ 40 * 75364 * 2
def baseEnd_75364 : Nat := 4299772893949819078157

theorem tailTrace_75364 : CollatzResearch.WordTrace tailWord_75364 prefixEnd_75364 4299772893949819078157 := by
  unfold tailWord_75364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1374375449488286995792573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1832500599317715994390097 1374375449488286995792573)
  ·
    refine ⟨515390793558107623422215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1374375449488286995792573 515390793558107623422215)
    ·
      refine ⟨773086190337161435133323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 515390793558107623422215 773086190337161435133323)
      ·
        refine ⟨1159629285505742152699985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773086190337161435133323 1159629285505742152699985)
        ·
          refine ⟨869721964129306614524989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1159629285505742152699985 869721964129306614524989)
          ·
            refine ⟨326145736548489980446871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 869721964129306614524989 326145736548489980446871)
            ·
              refine ⟨489218604822734970670307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326145736548489980446871 489218604822734970670307)
              ·
                refine ⟨733827907234102456005461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489218604822734970670307 733827907234102456005461)
                ·
                  refine ⟨4299772893949819078157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 733827907234102456005461 4299772893949819078157)
                  ·
                    rfl

theorem cell23_75364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_75364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75364 prefixEnd_75364 := by exact prefixLift 75364
  have htrace : WordTrace (prefixWord ++ tailWord_75364) baseStart_75364 baseEnd_75364 := by
    simpa [prefixWord, tailWord_75364, baseEnd_75364] using wordTrace_append hprefix tailTrace_75364
  have hstable : (prefixWord ++ tailWord_75364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75364).length < 2 ^ (prefixWord ++ tailWord_75364).sum := by decide
  have hdescent : baseEnd_75364 < baseStart_75364 := by decide
  rcases family_descends (prefixWord ++ tailWord_75364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75401 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 1, 7, 2]
def baseStart_75401 : Nat := 118140960795 + 75401 * 2 ^ 59
def prefixEnd_75401 : Nat := 4983230072969 + 3 ^ 40 * 75401 * 2
def baseEnd_75401 : Nat := 38716954829764726940743

theorem tailTrace_75401 : CollatzResearch.WordTrace tailWord_75401 prefixEnd_75401 38716954829764726940743 := by
  unfold tailWord_75401
  simp only [CollatzResearch.WordTrace]
  refine ⟨2750100399842529310682057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1833400266561686207121371 2750100399842529310682057)
  ·
    refine ⟨2062575299881896983011543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2750100399842529310682057 2062575299881896983011543)
    ·
      refine ⟨3093862949822845474517315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2062575299881896983011543 3093862949822845474517315)
      ·
        refine ⟨4640794424734268211775973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3093862949822845474517315 4640794424734268211775973)
        ·
          refine ⟨870148954637675289707995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4640794424734268211775973 870148954637675289707995)
          ·
            refine ⟨1305223431956512934561993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870148954637675289707995 1305223431956512934561993)
            ·
              refine ⟨978917573967384700921495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1305223431956512934561993 978917573967384700921495)
              ·
                refine ⟨1468376360951077051382243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978917573967384700921495 1468376360951077051382243)
                ·
                  refine ⟨2202564541426615577073365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468376360951077051382243 2202564541426615577073365)
                  ·
                    refine ⟨51622606439686302587657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2202564541426615577073365 51622606439686302587657)
                    ·
                      refine ⟨38716954829764726940743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51622606439686302587657 38716954829764726940743)
                      ·
                        rfl

theorem cell23_75401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 7, 2].length) (baseStart_75401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75401 prefixEnd_75401 := by exact prefixLift 75401
  have htrace : WordTrace (prefixWord ++ tailWord_75401) baseStart_75401 baseEnd_75401 := by
    simpa [prefixWord, tailWord_75401, baseEnd_75401] using wordTrace_append hprefix tailTrace_75401
  have hstable : (prefixWord ++ tailWord_75401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75401).length < 2 ^ (prefixWord ++ tailWord_75401).sum := by decide
  have hdescent : baseEnd_75401 < baseStart_75401 := by decide
  rcases family_descends (prefixWord ++ tailWord_75401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75404 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_75404 : Nat := 118140960795 + 75404 * 2 ^ 59
def prefixEnd_75404 : Nat := 4983230072969 + 3 ^ 40 * 75404 * 2
def baseEnd_75404 : Nat := 38718495271728215203229

theorem tailTrace_75404 : CollatzResearch.WordTrace tailWord_75404 prefixEnd_75404 38718495271728215203229 := by
  unfold tailWord_75404
  simp only [CollatzResearch.WordTrace]
  refine ⟨1375104909415830411520633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1833473212554440548694177 1375104909415830411520633)
  ·
    refine ⟨1031328682061872808640475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1375104909415830411520633 1031328682061872808640475)
    ·
      refine ⟨1546993023092809212960713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1031328682061872808640475 1546993023092809212960713)
      ·
        refine ⟨1160244767319606909720535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1546993023092809212960713 1160244767319606909720535)
        ·
          refine ⟨1740367150979410364580803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160244767319606909720535 1740367150979410364580803)
          ·
            refine ⟨2610550726469115546871205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740367150979410364580803 2610550726469115546871205)
            ·
              refine ⟨489478261212959165038351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2610550726469115546871205 489478261212959165038351)
              ·
                refine ⟨734217391819438747557527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489478261212959165038351 734217391819438747557527)
                ·
                  refine ⟨1101326087729158121336291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734217391819438747557527 1101326087729158121336291)
                  ·
                    refine ⟨1651989131593737182004437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1101326087729158121336291 1651989131593737182004437)
                    ·
                      refine ⟨38718495271728215203229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1651989131593737182004437 38718495271728215203229)
                      ·
                        rfl

theorem cell23_75404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_75404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75404 prefixEnd_75404 := by exact prefixLift 75404
  have htrace : WordTrace (prefixWord ++ tailWord_75404) baseStart_75404 baseEnd_75404 := by
    simpa [prefixWord, tailWord_75404, baseEnd_75404] using wordTrace_append hprefix tailTrace_75404
  have hstable : (prefixWord ++ tailWord_75404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75404).length < 2 ^ (prefixWord ++ tailWord_75404).sum := by decide
  have hdescent : baseEnd_75404 < baseStart_75404 := by decide
  rcases family_descends (prefixWord ++ tailWord_75404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75531 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 1, 6]
def baseStart_75531 : Nat := 118140960795 + 75531 * 2 ^ 59
def prefixEnd_75531 : Nat := 4983230072969 + 3 ^ 40 * 75531 * 2
def baseEnd_75531 : Nat := 12927902438283072771715

theorem tailTrace_75531 : CollatzResearch.WordTrace tailWord_75531 prefixEnd_75531 12927902438283072771715 := by
  unfold tailWord_75531
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754841889371561512914447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1836561259581041008609631 2754841889371561512914447)
  ·
    refine ⟨4132262834057342269371671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2754841889371561512914447 4132262834057342269371671)
    ·
      refine ⟨6198394251086013404057507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4132262834057342269371671 6198394251086013404057507)
      ·
        refine ⟨9297591376629020106086261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6198394251086013404057507 9297591376629020106086261)
        ·
          refine ⟨871649191558970634945587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9297591376629020106086261 871649191558970634945587)
          ·
            refine ⟨1307473787338455952418381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871649191558970634945587 1307473787338455952418381)
            ·
              refine ⟨490302670251920982156893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1307473787338455952418381 490302670251920982156893)
              ·
                refine ⟨183863501344470368308835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 490302670251920982156893 183863501344470368308835)
                ·
                  refine ⟨275795252016705552463253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183863501344470368308835 275795252016705552463253)
                  ·
                    refine ⟨12927902438283072771715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 275795252016705552463253 12927902438283072771715)
                    ·
                      rfl

theorem cell23_75531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 6].length) (baseStart_75531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75531 prefixEnd_75531 := by exact prefixLift 75531
  have htrace : WordTrace (prefixWord ++ tailWord_75531) baseStart_75531 baseEnd_75531 := by
    simpa [prefixWord, tailWord_75531, baseEnd_75531] using wordTrace_append hprefix tailTrace_75531
  have hstable : (prefixWord ++ tailWord_75531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75531).length < 2 ^ (prefixWord ++ tailWord_75531).sum := by decide
  have hdescent : baseEnd_75531 < baseStart_75531 := by decide
  rcases family_descends (prefixWord ++ tailWord_75531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75533 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_75533 : Nat := 118140960795 + 75533 * 2 ^ 59
def prefixEnd_75533 : Nat := 4983230072969 + 3 ^ 40 * 75533 * 2
def baseEnd_75533 : Nat := 38784734276158210490137

theorem tailTrace_75533 : CollatzResearch.WordTrace tailWord_75533 prefixEnd_75533 38784734276158210490137 := by
  unfold tailWord_75533
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754914835364315854487253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1836609890242877236324835 2754914835364315854487253)
  ·
    refine ⟨64568316453851152839545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 2754914835364315854487253 64568316453851152839545)
    ·
      refine ⟨48426237340388364629659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64568316453851152839545 48426237340388364629659)
      ·
        refine ⟨72639356010582546944489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48426237340388364629659 72639356010582546944489)
        ·
          refine ⟨54479517007936910208367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72639356010582546944489 54479517007936910208367)
          ·
            refine ⟨81719275511905365312551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54479517007936910208367 81719275511905365312551)
            ·
              refine ⟨122578913267858047968827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81719275511905365312551 122578913267858047968827)
              ·
                refine ⟨183868369901787071953241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122578913267858047968827 183868369901787071953241)
                ·
                  refine ⟨137901277426340303964931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183868369901787071953241 137901277426340303964931)
                  ·
                    refine ⟨206851916139510455947397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137901277426340303964931 206851916139510455947397)
                    ·
                      refine ⟨38784734276158210490137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 206851916139510455947397 38784734276158210490137)
                      ·
                        rfl

theorem cell23_75533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_75533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75533 prefixEnd_75533 := by exact prefixLift 75533
  have htrace : WordTrace (prefixWord ++ tailWord_75533) baseStart_75533 baseEnd_75533 := by
    simpa [prefixWord, tailWord_75533, baseEnd_75533] using wordTrace_append hprefix tailTrace_75533
  have hstable : (prefixWord ++ tailWord_75533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75533).length < 2 ^ (prefixWord ++ tailWord_75533).sum := by decide
  have hdescent : baseEnd_75533 < baseStart_75533 := by decide
  rcases family_descends (prefixWord ++ tailWord_75533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75548 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 4, 4]
def baseStart_75548 : Nat := 118140960795 + 75548 * 2 ^ 59
def prefixEnd_75548 : Nat := 4983230072969 + 3 ^ 40 * 75548 * 2
def baseEnd_75548 : Nat := 12930812161991883934189

theorem tailTrace_75548 : CollatzResearch.WordTrace tailWord_75548 prefixEnd_75548 12930812161991883934189 := by
  unfold tailWord_75548
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377730965154986708141649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1836974620206648944188865 1377730965154986708141649)
  ·
    refine ⟨1033298223866240031106237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1377730965154986708141649 1033298223866240031106237)
    ·
      refine ⟨387486833949840011664839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1033298223866240031106237 387486833949840011664839)
      ·
        refine ⟨581230250924760017497259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387486833949840011664839 581230250924760017497259)
        ·
          refine ⟨871845376387140026245889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581230250924760017497259 871845376387140026245889)
          ·
            refine ⟨653884032290355019684417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 871845376387140026245889 653884032290355019684417)
            ·
              refine ⟨490413024217766264763313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653884032290355019684417 490413024217766264763313)
              ·
                refine ⟨367809768163324698572485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490413024217766264763313 367809768163324698572485)
                ·
                  refine ⟨68964331530623380982341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367809768163324698572485 68964331530623380982341)
                  ·
                    refine ⟨12930812161991883934189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68964331530623380982341 12930812161991883934189)
                    ·
                      rfl

theorem cell23_75548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_75548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75548 prefixEnd_75548 := by exact prefixLift 75548
  have htrace : WordTrace (prefixWord ++ tailWord_75548) baseStart_75548 baseEnd_75548 := by
    simpa [prefixWord, tailWord_75548, baseEnd_75548] using wordTrace_append hprefix tailTrace_75548
  have hstable : (prefixWord ++ tailWord_75548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75548).length < 2 ^ (prefixWord ++ tailWord_75548).sum := by decide
  have hdescent : baseEnd_75548 < baseStart_75548 := by decide
  rcases family_descends (prefixWord ++ tailWord_75548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75555 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 1, 1, 4]
def baseStart_75555 : Nat := 118140960795 + 75555 * 2 ^ 59
def prefixEnd_75555 : Nat := 4983230072969 + 3 ^ 40 * 75555 * 2
def baseEnd_75555 : Nat := 38796030850557124415035

theorem tailTrace_75555 : CollatzResearch.WordTrace tailWord_75555 prefixEnd_75555 38796030850557124415035 := by
  unfold tailWord_75555
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755717241284613611788119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1837144827523075741192079 2755717241284613611788119)
  ·
    refine ⟨4133575861926920417682179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2755717241284613611788119 4133575861926920417682179)
    ·
      refine ⟨6200363792890380626523269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4133575861926920417682179 6200363792890380626523269)
      ·
        refine ⟨1162568211166946367473113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6200363792890380626523269 1162568211166946367473113)
        ·
          refine ⟨871926158375209775604835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1162568211166946367473113 871926158375209775604835)
          ·
            refine ⟨1307889237562814663407253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871926158375209775604835 1307889237562814663407253)
            ·
              refine ⟨61307308010756937347215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1307889237562814663407253 61307308010756937347215)
              ·
                refine ⟨91960962016135406020823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61307308010756937347215 91960962016135406020823)
                ·
                  refine ⟨137941443024203109031235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91960962016135406020823 137941443024203109031235)
                  ·
                    refine ⟨206912164536304663546853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137941443024203109031235 206912164536304663546853)
                    ·
                      refine ⟨38796030850557124415035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 206912164536304663546853 38796030850557124415035)
                      ·
                        rfl

theorem cell23_75555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_75555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75555 prefixEnd_75555 := by exact prefixLift 75555
  have htrace : WordTrace (prefixWord ++ tailWord_75555) baseStart_75555 baseEnd_75555 := by
    simpa [prefixWord, tailWord_75555, baseEnd_75555] using wordTrace_append hprefix tailTrace_75555
  have hstable : (prefixWord ++ tailWord_75555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75555).length < 2 ^ (prefixWord ++ tailWord_75555).sum := by decide
  have hdescent : baseEnd_75555 < baseStart_75555 := by decide
  rcases family_descends (prefixWord ++ tailWord_75555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75591 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 2, 7]
def baseStart_75591 : Nat := 118140960795 + 75591 * 2 ^ 59
def prefixEnd_75591 : Nat := 4983230072969 + 3 ^ 40 * 75591 * 2
def baseEnd_75591 : Nat := 12938172051372994521623

theorem tailTrace_75591 : CollatzResearch.WordTrace tailWord_75591 prefixEnd_75591 12938172051372994521623 := by
  unfold tailWord_75591
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757030269154191760098627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1838020179436127840065751 2757030269154191760098627)
  ·
    refine ⟨4135545403731287640147941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2757030269154191760098627 4135545403731287640147941)
    ·
      refine ⟨775414763199616432527739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4135545403731287640147941 775414763199616432527739)
      ·
        refine ⟨1163122144799424648791609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775414763199616432527739 1163122144799424648791609)
        ·
          refine ⟨872341608599568486593707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1163122144799424648791609 872341608599568486593707)
          ·
            refine ⟨1308512412899352729890561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872341608599568486593707 1308512412899352729890561)
            ·
              refine ⟨981384309674514547417921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1308512412899352729890561 981384309674514547417921)
              ·
                refine ⟨736038232255885910563441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 981384309674514547417921 736038232255885910563441)
                ·
                  refine ⟨552028674191914432922581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 736038232255885910563441 552028674191914432922581)
                  ·
                    refine ⟨12938172051372994521623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 552028674191914432922581 12938172051372994521623)
                    ·
                      rfl

theorem cell23_75591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_75591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75591 prefixEnd_75591 := by exact prefixLift 75591
  have htrace : WordTrace (prefixWord ++ tailWord_75591) baseStart_75591 baseEnd_75591 := by
    simpa [prefixWord, tailWord_75591, baseEnd_75591] using wordTrace_append hprefix tailTrace_75591
  have hstable : (prefixWord ++ tailWord_75591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75591).length < 2 ^ (prefixWord ++ tailWord_75591).sum := by decide
  have hdescent : baseEnd_75591 < baseStart_75591 := by decide
  rcases family_descends (prefixWord ++ tailWord_75591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75605 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_75605 : Nat := 118140960795 + 75605 * 2 ^ 59
def prefixEnd_75605 : Nat := 4983230072969 + 3 ^ 40 * 75605 * 2
def baseEnd_75605 : Nat := 38821704883281928789805

theorem tailTrace_75605 : CollatzResearch.WordTrace tailWord_75605 prefixEnd_75605 38821704883281928789805 := by
  unfold tailWord_75605
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757540891103472151108269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1838360594068981434072179 2757540891103472151108269)
  ·
    refine ⟨1034077834163802056665601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2757540891103472151108269 1034077834163802056665601)
    ·
      refine ⟨775558375622851542499201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1034077834163802056665601 775558375622851542499201)
      ·
        refine ⟨581668781717138656874401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 775558375622851542499201 581668781717138656874401)
        ·
          refine ⟨436251586287853992655801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581668781717138656874401 436251586287853992655801)
          ·
            refine ⟨327188689715890494491851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436251586287853992655801 327188689715890494491851)
            ·
              refine ⟨490783034573835741737777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327188689715890494491851 490783034573835741737777)
              ·
                refine ⟨368087275930376806303333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490783034573835741737777 368087275930376806303333)
                ·
                  refine ⟨69016364236945651181875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368087275930376806303333 69016364236945651181875)
                  ·
                    refine ⟨103524546355418476772813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69016364236945651181875 103524546355418476772813)
                    ·
                      refine ⟨38821704883281928789805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 103524546355418476772813 38821704883281928789805)
                      ·
                        rfl

theorem cell23_75605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_75605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75605 prefixEnd_75605 := by exact prefixLift 75605
  have htrace : WordTrace (prefixWord ++ tailWord_75605) baseStart_75605 baseEnd_75605 := by
    simpa [prefixWord, tailWord_75605, baseEnd_75605] using wordTrace_append hprefix tailTrace_75605
  have hstable : (prefixWord ++ tailWord_75605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75605).length < 2 ^ (prefixWord ++ tailWord_75605).sum := by decide
  have hdescent : baseEnd_75605 < baseStart_75605 := by decide
  rcases family_descends (prefixWord ++ tailWord_75605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75645 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 1, 4, 2]
def baseStart_75645 : Nat := 118140960795 + 75645 * 2 ^ 59
def prefixEnd_75645 : Nat := 4983230072969 + 3 ^ 40 * 75645 * 2
def baseEnd_75645 : Nat := 38842244109461772289621

theorem tailTrace_75645 : CollatzResearch.WordTrace tailWord_75645 prefixEnd_75645 38842244109461772289621 := by
  unfold tailWord_75645
  simp only [CollatzResearch.WordTrace]
  refine ⟨2758999810958558982564389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1839333207305705988376259 2758999810958558982564389)
  ·
    refine ⟨517312464554729809230823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2758999810958558982564389 517312464554729809230823)
    ·
      refine ⟨775968696832094713846235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 517312464554729809230823 775968696832094713846235)
      ·
        refine ⟨1163953045248142070769353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775968696832094713846235 1163953045248142070769353)
        ·
          refine ⟨872964783936106553077015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1163953045248142070769353 872964783936106553077015)
          ·
            refine ⟨1309447175904159829615523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872964783936106553077015 1309447175904159829615523)
            ·
              refine ⟨1964170763856239744423285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1309447175904159829615523 1964170763856239744423285)
              ·
                refine ⟨184141009111522476039683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1964170763856239744423285 184141009111522476039683)
                ·
                  refine ⟨276211513667283714059525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184141009111522476039683 276211513667283714059525)
                  ·
                    refine ⟨51789658812615696386161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 276211513667283714059525 51789658812615696386161)
                    ·
                      refine ⟨38842244109461772289621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51789658812615696386161 38842244109461772289621)
                      ·
                        rfl

theorem cell23_75645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_75645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75645 prefixEnd_75645 := by exact prefixLift 75645
  have htrace : WordTrace (prefixWord ++ tailWord_75645) baseStart_75645 baseEnd_75645 := by
    simpa [prefixWord, tailWord_75645, baseEnd_75645] using wordTrace_append hprefix tailTrace_75645
  have hstable : (prefixWord ++ tailWord_75645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75645).length < 2 ^ (prefixWord ++ tailWord_75645).sum := by decide
  have hdescent : baseEnd_75645 < baseStart_75645 := by decide
  rcases family_descends (prefixWord ++ tailWord_75645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75649 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_75649 : Nat := 118140960795 + 75649 * 2 ^ 59
def prefixEnd_75649 : Nat := 4983230072969 + 3 ^ 40 * 75649 * 2
def baseEnd_75649 : Nat := 38844298032079756639603

theorem tailTrace_75649 : CollatzResearch.WordTrace tailWord_75649 prefixEnd_75649 38844298032079756639603 := by
  unfold tailWord_75649
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759145702944067665710001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1839430468629378443806667 2759145702944067665710001)
  ·
    refine ⟨2069359277208050749282501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2759145702944067665710001 2069359277208050749282501)
    ·
      refine ⟨388004864476509515490469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2069359277208050749282501 388004864476509515490469)
      ·
        refine ⟨72750912089345534154463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 388004864476509515490469 72750912089345534154463)
        ·
          refine ⟨109126368134018301231695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72750912089345534154463 109126368134018301231695)
          ·
            refine ⟨163689552201027451847543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109126368134018301231695 163689552201027451847543)
            ·
              refine ⟨245534328301541177771315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163689552201027451847543 245534328301541177771315)
              ·
                refine ⟨368301492452311766656973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245534328301541177771315 368301492452311766656973)
                ·
                  refine ⟨138113059669616912496365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368301492452311766656973 138113059669616912496365)
                  ·
                    refine ⟨51792397376106342186137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138113059669616912496365 51792397376106342186137)
                    ·
                      refine ⟨38844298032079756639603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51792397376106342186137 38844298032079756639603)
                      ·
                        rfl

theorem cell23_75649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_75649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75649 prefixEnd_75649 := by exact prefixLift 75649
  have htrace : WordTrace (prefixWord ++ tailWord_75649) baseStart_75649 baseEnd_75649 := by
    simpa [prefixWord, tailWord_75649, baseEnd_75649] using wordTrace_append hprefix tailTrace_75649
  have hstable : (prefixWord ++ tailWord_75649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75649).length < 2 ^ (prefixWord ++ tailWord_75649).sum := by decide
  have hdescent : baseEnd_75649 < baseStart_75649 := by decide
  rcases family_descends (prefixWord ++ tailWord_75649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75666 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_75666 : Nat := 118140960795 + 75666 * 2 ^ 59
def prefixEnd_75666 : Nat := 4983230072969 + 3 ^ 40 * 75666 * 2
def baseEnd_75666 : Nat := 38853027203206190127025

theorem tailTrace_75666 : CollatzResearch.WordTrace tailWord_75666 prefixEnd_75666 38853027203206190127025 := by
  unfold tailWord_75666
  simp only [CollatzResearch.WordTrace]
  refine ⟨689941435970619892269713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1839843829254986379385901 689941435970619892269713)
  ·
    refine ⟨517456076977964919202285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 689941435970619892269713 517456076977964919202285)
    ·
      refine ⟨194046028866736844700857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 517456076977964919202285 194046028866736844700857)
      ·
        refine ⟨145534521650052633525643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194046028866736844700857 145534521650052633525643)
        ·
          refine ⟨218301782475078950288465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145534521650052633525643 218301782475078950288465)
          ·
            refine ⟨163726336856309212716349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218301782475078950288465 163726336856309212716349)
            ·
              refine ⟨61397376321115954768631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163726336856309212716349 61397376321115954768631)
              ·
                refine ⟨92096064481673932152947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61397376321115954768631 92096064481673932152947)
                ·
                  refine ⟨138144096722510898229421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92096064481673932152947 138144096722510898229421)
                  ·
                    refine ⟨51804036270941586836033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138144096722510898229421 51804036270941586836033)
                    ·
                      refine ⟨38853027203206190127025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51804036270941586836033 38853027203206190127025)
                      ·
                        rfl

theorem cell23_75666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_75666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75666 prefixEnd_75666 := by exact prefixLift 75666
  have htrace : WordTrace (prefixWord ++ tailWord_75666) baseStart_75666 baseEnd_75666 := by
    simpa [prefixWord, tailWord_75666, baseEnd_75666] using wordTrace_append hprefix tailTrace_75666
  have hstable : (prefixWord ++ tailWord_75666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75666).length < 2 ^ (prefixWord ++ tailWord_75666).sum := by decide
  have hdescent : baseEnd_75666 < baseStart_75666 := by decide
  rcases family_descends (prefixWord ++ tailWord_75666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75698 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_75698 : Nat := 118140960795 + 75698 * 2 ^ 59
def prefixEnd_75698 : Nat := 4983230072969 + 3 ^ 40 * 75698 * 2
def baseEnd_75698 : Nat := 12956486194716688308959

theorem tailTrace_75698 : CollatzResearch.WordTrace tailWord_75698 prefixEnd_75698 12956486194716688308959 := by
  unfold tailWord_75698
  simp only [CollatzResearch.WordTrace]
  refine ⟨690233219941637258560937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1840621919844366022829165 690233219941637258560937)
  ·
    refine ⟨517674914956227943920703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 690233219941637258560937 517674914956227943920703)
    ·
      refine ⟨776512372434341915881055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 517674914956227943920703 776512372434341915881055)
      ·
        refine ⟨1164768558651512873821583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776512372434341915881055 1164768558651512873821583)
        ·
          refine ⟨1747152837977269310732375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164768558651512873821583 1747152837977269310732375)
          ·
            refine ⟨2620729256965903966098563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747152837977269310732375 2620729256965903966098563)
            ·
              refine ⟨3931093885448855949147845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620729256965903966098563 3931093885448855949147845)
              ·
                refine ⟨737080103521660490465221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3931093885448855949147845 737080103521660490465221)
                ·
                  refine ⟨138202519410311341962229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 737080103521660490465221 138202519410311341962229)
                  ·
                    refine ⟨12956486194716688308959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 138202519410311341962229 12956486194716688308959)
                    ·
                      rfl

theorem cell23_75698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_75698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75698 prefixEnd_75698 := by exact prefixLift 75698
  have htrace : WordTrace (prefixWord ++ tailWord_75698) baseStart_75698 baseEnd_75698 := by
    simpa [prefixWord, tailWord_75698, baseEnd_75698] using wordTrace_append hprefix tailTrace_75698
  have hstable : (prefixWord ++ tailWord_75698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75698).length < 2 ^ (prefixWord ++ tailWord_75698).sum := by decide
  have hdescent : baseEnd_75698 < baseStart_75698 := by decide
  rcases family_descends (prefixWord ++ tailWord_75698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75705 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 2, 5, 2]
def baseStart_75705 : Nat := 118140960795 + 75705 * 2 ^ 59
def prefixEnd_75705 : Nat := 4983230072969 + 3 ^ 40 * 75705 * 2
def baseEnd_75705 : Nat := 38873052948731537539345

theorem tailTrace_75705 : CollatzResearch.WordTrace tailWord_75705 prefixEnd_75705 38873052948731537539345 := by
  unfold tailWord_75705
  simp only [CollatzResearch.WordTrace]
  refine ⟨2761188190741189229748569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1840792127160792819832379 2761188190741189229748569)
  ·
    refine ⟨2070891143055891922311427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2761188190741189229748569 2070891143055891922311427)
    ·
      refine ⟨3106336714583837883467141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2070891143055891922311427 3106336714583837883467141)
      ·
        refine ⟨582438133984469603150089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3106336714583837883467141 582438133984469603150089)
        ·
          refine ⟨436828600488352202362567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582438133984469603150089 436828600488352202362567)
          ·
            refine ⟨655242900732528303543851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436828600488352202362567 655242900732528303543851)
            ·
              refine ⟨982864351098792455315777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655242900732528303543851 982864351098792455315777)
              ·
                refine ⟨737148263324094341486833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982864351098792455315777 737148263324094341486833)
                ·
                  refine ⟨552861197493070756115125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 737148263324094341486833 552861197493070756115125)
                  ·
                    refine ⟨51830737264975383385793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 552861197493070756115125 51830737264975383385793)
                    ·
                      refine ⟨38873052948731537539345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51830737264975383385793 38873052948731537539345)
                      ·
                        rfl

theorem cell23_75705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_75705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75705 prefixEnd_75705 := by exact prefixLift 75705
  have htrace : WordTrace (prefixWord ++ tailWord_75705) baseStart_75705 baseEnd_75705 := by
    simpa [prefixWord, tailWord_75705, baseEnd_75705] using wordTrace_append hprefix tailTrace_75705
  have hstable : (prefixWord ++ tailWord_75705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75705).length < 2 ^ (prefixWord ++ tailWord_75705).sum := by decide
  have hdescent : baseEnd_75705 < baseStart_75705 := by decide
  rcases family_descends (prefixWord ++ tailWord_75705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75735 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 4, 4, 2]
def baseStart_75735 : Nat := 118140960795 + 75735 * 2 ^ 59
def prefixEnd_75735 : Nat := 4983230072969 + 3 ^ 40 * 75735 * 2
def baseEnd_75735 : Nat := 38888457368366420164207

theorem tailTrace_75735 : CollatzResearch.WordTrace tailWord_75735 prefixEnd_75735 38888457368366420164207 := by
  unfold tailWord_75735
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762282380632504353340659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1841521587088336235560439 2762282380632504353340659)
  ·
    refine ⟨4143423570948756530010989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2762282380632504353340659 4143423570948756530010989)
    ·
      refine ⟨1553783839105783698754121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4143423570948756530010989 1553783839105783698754121)
      ·
        refine ⟨1165337879329337774065591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1553783839105783698754121 1165337879329337774065591)
        ·
          refine ⟨1748006818994006661098387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165337879329337774065591 1748006818994006661098387)
          ·
            refine ⟨2622010228491009991647581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748006818994006661098387 2622010228491009991647581)
            ·
              refine ⟨983253835684128746867843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2622010228491009991647581 983253835684128746867843)
              ·
                refine ⟨1474880753526193120301765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983253835684128746867843 1474880753526193120301765)
                ·
                  refine ⟨276540141286161210056581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1474880753526193120301765 276540141286161210056581)
                  ·
                    refine ⟨51851276491155226885609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 276540141286161210056581 51851276491155226885609)
                    ·
                      refine ⟨38888457368366420164207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51851276491155226885609 38888457368366420164207)
                      ·
                        rfl

theorem cell23_75735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_75735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75735 prefixEnd_75735 := by exact prefixLift 75735
  have htrace : WordTrace (prefixWord ++ tailWord_75735) baseStart_75735 baseEnd_75735 := by
    simpa [prefixWord, tailWord_75735, baseEnd_75735] using wordTrace_append hprefix tailTrace_75735
  have hstable : (prefixWord ++ tailWord_75735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75735).length < 2 ^ (prefixWord ++ tailWord_75735).sum := by decide
  have hdescent : baseEnd_75735 < baseStart_75735 := by decide
  rcases family_descends (prefixWord ++ tailWord_75735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75745 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 3, 4]
def baseStart_75745 : Nat := 118140960795 + 75745 * 2 ^ 59
def prefixEnd_75745 : Nat := 4983230072969 + 3 ^ 40 * 75745 * 2
def baseEnd_75745 : Nat := 12964530724970460346387

theorem tailTrace_75745 : CollatzResearch.WordTrace tailWord_75745 prefixEnd_75745 12964530724970460346387 := by
  unfold tailWord_75745
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762647110596276061204689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1841764740397517374136459 2762647110596276061204689)
  ·
    refine ⟨2071985332947207045903517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2762647110596276061204689 2071985332947207045903517)
    ·
      refine ⟨776994499855202642213819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2071985332947207045903517 776994499855202642213819)
      ·
        refine ⟨1165491749782803963320729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776994499855202642213819 1165491749782803963320729)
        ·
          refine ⟨874118812337102972490547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1165491749782803963320729 874118812337102972490547)
          ·
            refine ⟨1311178218505654458735821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874118812337102972490547 1311178218505654458735821)
            ·
              refine ⟨491691831939620422025933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1311178218505654458735821 491691831939620422025933)
              ·
                refine ⟨184384436977357658259725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 491691831939620422025933 184384436977357658259725)
                ·
                  refine ⟨69144163866509121847397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184384436977357658259725 69144163866509121847397)
                  ·
                    refine ⟨12964530724970460346387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69144163866509121847397 12964530724970460346387)
                    ·
                      rfl

theorem cell23_75745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_75745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75745 prefixEnd_75745 := by exact prefixLift 75745
  have htrace : WordTrace (prefixWord ++ tailWord_75745) baseStart_75745 baseEnd_75745 := by
    simpa [prefixWord, tailWord_75745, baseEnd_75745] using wordTrace_append hprefix tailTrace_75745
  have hstable : (prefixWord ++ tailWord_75745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75745).length < 2 ^ (prefixWord ++ tailWord_75745).sum := by decide
  have hdescent : baseEnd_75745 < baseStart_75745 := by decide
  rcases family_descends (prefixWord ++ tailWord_75745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75748 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_75748 : Nat := 118140960795 + 75748 * 2 ^ 59
def prefixEnd_75748 : Nat := 4983230072969 + 3 ^ 40 * 75748 * 2
def baseEnd_75748 : Nat := 38895132616874869301647

theorem tailTrace_75748 : CollatzResearch.WordTrace tailWord_75748 prefixEnd_75748 38895132616874869301647 := by
  unfold tailWord_75748
  simp only [CollatzResearch.WordTrace]
  refine ⟨1381378264792703786781949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1841837686390271715709265 1381378264792703786781949)
  ·
    refine ⟨518016849297263920043231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1381378264792703786781949 518016849297263920043231)
    ·
      refine ⟨777025273945895880064847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 518016849297263920043231 777025273945895880064847)
      ·
        refine ⟨1165537910918843820097271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777025273945895880064847 1165537910918843820097271)
        ·
          refine ⟨1748306866378265730145907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165537910918843820097271 1748306866378265730145907)
          ·
            refine ⟨2622460299567398595218861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748306866378265730145907 2622460299567398595218861)
            ·
              refine ⟨983422612337774473207073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2622460299567398595218861 983422612337774473207073)
              ·
                refine ⟨737566959253330854905305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983422612337774473207073 737566959253330854905305)
                ·
                  refine ⟨553175219439998141178979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 737566959253330854905305 553175219439998141178979)
                  ·
                    refine ⟨829762829159997211768469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 553175219439998141178979 829762829159997211768469)
                    ·
                      refine ⟨38895132616874869301647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 829762829159997211768469 38895132616874869301647)
                      ·
                        rfl

theorem cell23_75748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_75748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75748 prefixEnd_75748 := by exact prefixLift 75748
  have htrace : WordTrace (prefixWord ++ tailWord_75748) baseStart_75748 baseEnd_75748 := by
    simpa [prefixWord, tailWord_75748, baseEnd_75748] using wordTrace_append hprefix tailTrace_75748
  have hstable : (prefixWord ++ tailWord_75748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75748).length < 2 ^ (prefixWord ++ tailWord_75748).sum := by decide
  have hdescent : baseEnd_75748 < baseStart_75748 := by decide
  rcases family_descends (prefixWord ++ tailWord_75748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75809 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 6]
def baseStart_75809 : Nat := 118140960795 + 75809 * 2 ^ 59
def prefixEnd_75809 : Nat := 4983230072969 + 3 ^ 40 * 75809 * 2
def baseEnd_75809 : Nat := 4325161659644347848763

theorem tailTrace_75809 : CollatzResearch.WordTrace tailWord_75809 prefixEnd_75809 4325161659644347848763 := by
  unfold tailWord_75809
  simp only [CollatzResearch.WordTrace]
  refine ⟨2764981382364414991534481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1843320921576276661022987 2764981382364414991534481)
  ·
    refine ⟨2073736036773311243650861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2764981382364414991534481 2073736036773311243650861)
    ·
      refine ⟨777651013789991716369073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2073736036773311243650861 777651013789991716369073)
      ·
        refine ⟨583238260342493787276805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 777651013789991716369073 583238260342493787276805)
        ·
          refine ⟨109357173814217585114401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 583238260342493787276805 109357173814217585114401)
          ·
            refine ⟨82017880360663188835801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109357173814217585114401 82017880360663188835801)
            ·
              refine ⟨61513410270497391626851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82017880360663188835801 61513410270497391626851)
              ·
                refine ⟨92270115405746087440277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61513410270497391626851 92270115405746087440277)
                ·
                  refine ⟨4325161659644347848763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92270115405746087440277 4325161659644347848763)
                  ·
                    rfl

theorem cell23_75809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 6].length) (baseStart_75809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75809 prefixEnd_75809 := by exact prefixLift 75809
  have htrace : WordTrace (prefixWord ++ tailWord_75809) baseStart_75809 baseEnd_75809 := by
    simpa [prefixWord, tailWord_75809, baseEnd_75809] using wordTrace_append hprefix tailTrace_75809
  have hstable : (prefixWord ++ tailWord_75809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75809).length < 2 ^ (prefixWord ++ tailWord_75809).sum := by decide
  have hdescent : baseEnd_75809 < baseStart_75809 := by decide
  rcases family_descends (prefixWord ++ tailWord_75809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75822 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_75822 : Nat := 118140960795 + 75822 * 2 ^ 59
def prefixEnd_75822 : Nat := 4983230072969 + 3 ^ 40 * 75822 * 2
def baseEnd_75822 : Nat := 12977710061769193258769

theorem tailTrace_75822 : CollatzResearch.WordTrace tailWord_75822 prefixEnd_75822 12977710061769193258769 := by
  unfold tailWord_75822
  simp only [CollatzResearch.WordTrace]
  refine ⟨345681941414664776469715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1843637020878212141171813 345681941414664776469715)
  ·
    refine ⟨518522912121997164704573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 345681941414664776469715 518522912121997164704573)
    ·
      refine ⟨194446092045748936764215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 518522912121997164704573 194446092045748936764215)
      ·
        refine ⟨291669138068623405146323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194446092045748936764215 291669138068623405146323)
        ·
          refine ⟨437503707102935107719485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291669138068623405146323 437503707102935107719485)
          ·
            refine ⟨164063890163600665394807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 437503707102935107719485 164063890163600665394807)
            ·
              refine ⟨246095835245400998092211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164063890163600665394807 246095835245400998092211)
              ·
                refine ⟨369143752868101497138317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246095835245400998092211 369143752868101497138317)
                ·
                  refine ⟨138428907325538061426869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369143752868101497138317 138428907325538061426869)
                  ·
                    refine ⟨12977710061769193258769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 138428907325538061426869 12977710061769193258769)
                    ·
                      rfl

theorem cell23_75822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_75822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75822 prefixEnd_75822 := by exact prefixLift 75822
  have htrace : WordTrace (prefixWord ++ tailWord_75822) baseStart_75822 baseEnd_75822 := by
    simpa [prefixWord, tailWord_75822, baseEnd_75822] using wordTrace_append hprefix tailTrace_75822
  have hstable : (prefixWord ++ tailWord_75822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75822).length < 2 ^ (prefixWord ++ tailWord_75822).sum := by decide
  have hdescent : baseEnd_75822 < baseStart_75822 := by decide
  rcases family_descends (prefixWord ++ tailWord_75822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75846 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_75846 : Nat := 118140960795 + 75846 * 2 ^ 59
def prefixEnd_75846 : Nat := 4983230072969 + 3 ^ 40 * 75846 * 2
def baseEnd_75846 : Nat := 38945453721015485876197

theorem tailTrace_75846 : CollatzResearch.WordTrace tailWord_75846 prefixEnd_75846 38945453721015485876197 := by
  unfold tailWord_75846
  simp only [CollatzResearch.WordTrace]
  refine ⟨86447840100949072207231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1844220588820246873754261 86447840100949072207231)
  ·
    refine ⟨129671760151423608310847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86447840100949072207231 129671760151423608310847)
    ·
      refine ⟨194507640227135412466271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129671760151423608310847 194507640227135412466271)
      ·
        refine ⟨291761460340703118699407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194507640227135412466271 291761460340703118699407)
        ·
          refine ⟨437642190511054678049111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291761460340703118699407 437642190511054678049111)
          ·
            refine ⟨656463285766582017073667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437642190511054678049111 656463285766582017073667)
            ·
              refine ⟨984694928649873025610501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656463285766582017073667 984694928649873025610501)
              ·
                refine ⟨184630299121851192301969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 984694928649873025610501 184630299121851192301969)
                ·
                  refine ⟨138472724341388394226477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184630299121851192301969 138472724341388394226477)
                  ·
                    refine ⟨51927271628020647834929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138472724341388394226477 51927271628020647834929)
                    ·
                      refine ⟨38945453721015485876197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51927271628020647834929 38945453721015485876197)
                      ·
                        rfl

theorem cell23_75846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_75846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75846 prefixEnd_75846 := by exact prefixLift 75846
  have htrace : WordTrace (prefixWord ++ tailWord_75846) baseStart_75846 baseEnd_75846 := by
    simpa [prefixWord, tailWord_75846, baseEnd_75846] using wordTrace_append hprefix tailTrace_75846
  have hstable : (prefixWord ++ tailWord_75846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75846).length < 2 ^ (prefixWord ++ tailWord_75846).sum := by decide
  have hdescent : baseEnd_75846 < baseStart_75846 := by decide
  rcases family_descends (prefixWord ++ tailWord_75846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75852 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 2, 4]
def baseStart_75852 : Nat := 118140960795 + 75852 * 2 ^ 59
def prefixEnd_75852 : Nat := 4983230072969 + 3 ^ 40 * 75852 * 2
def baseEnd_75852 : Nat := 12982844868314154133723

theorem tailTrace_75852 : CollatzResearch.WordTrace tailWord_75852 prefixEnd_75852 12982844868314154133723 := by
  unfold tailWord_75852
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383274860604316667674905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1844366480805755556899873 1383274860604316667674905)
  ·
    refine ⟨1037456145453237500756179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1383274860604316667674905 1037456145453237500756179)
    ·
      refine ⟨1556184218179856251134269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037456145453237500756179 1556184218179856251134269)
      ·
        refine ⟨583569081817446094175351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1556184218179856251134269 583569081817446094175351)
        ·
          refine ⟨875353622726169141263027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583569081817446094175351 875353622726169141263027)
          ·
            refine ⟨1313030434089253711894541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875353622726169141263027 1313030434089253711894541)
            ·
              refine ⟨492386412783470141960453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1313030434089253711894541 492386412783470141960453)
              ·
                refine ⟨92322452396900651617585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492386412783470141960453 92322452396900651617585)
                ·
                  refine ⟨69241839297675488713189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92322452396900651617585 69241839297675488713189)
                  ·
                    refine ⟨12982844868314154133723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69241839297675488713189 12982844868314154133723)
                    ·
                      rfl

theorem cell23_75852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_75852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75852 prefixEnd_75852 := by exact prefixLift 75852
  have htrace : WordTrace (prefixWord ++ tailWord_75852) baseStart_75852 baseEnd_75852 := by
    simpa [prefixWord, tailWord_75852, baseEnd_75852] using wordTrace_append hprefix tailTrace_75852
  have hstable : (prefixWord ++ tailWord_75852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75852).length < 2 ^ (prefixWord ++ tailWord_75852).sum := by decide
  have hdescent : baseEnd_75852 < baseStart_75852 := by decide
  rcases family_descends (prefixWord ++ tailWord_75852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75869 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_75869 : Nat := 118140960795 + 75869 * 2 ^ 59
def prefixEnd_75869 : Nat := 4983230072969 + 3 ^ 40 * 75869 * 2
def baseEnd_75869 : Nat := 12985754592022965296197

theorem tailTrace_75869 : CollatzResearch.WordTrace tailWord_75869 prefixEnd_75869 12985754592022965296197 := by
  unfold tailWord_75869
  simp only [CollatzResearch.WordTrace]
  refine ⟨2767169762147045238718661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1844779841431363492479107 2767169762147045238718661)
  ·
    refine ⟨518844330402570982259749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2767169762147045238718661 518844330402570982259749)
    ·
      refine ⟨97283311950482059173703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 518844330402570982259749 97283311950482059173703)
      ·
        refine ⟨145924967925723088760555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97283311950482059173703 145924967925723088760555)
        ·
          refine ⟨218887451888584633140833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145924967925723088760555 218887451888584633140833)
          ·
            refine ⟨164165588916438474855625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218887451888584633140833 164165588916438474855625)
            ·
              refine ⟨123124191687328856141719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164165588916438474855625 123124191687328856141719)
              ·
                refine ⟨184686287530993284212579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123124191687328856141719 184686287530993284212579)
                ·
                  refine ⟨277029431296489926318869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184686287530993284212579 277029431296489926318869)
                  ·
                    refine ⟨12985754592022965296197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 277029431296489926318869 12985754592022965296197)
                    ·
                      rfl

theorem cell23_75869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_75869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75869 prefixEnd_75869 := by exact prefixLift 75869
  have htrace : WordTrace (prefixWord ++ tailWord_75869) baseStart_75869 baseEnd_75869 := by
    simpa [prefixWord, tailWord_75869, baseEnd_75869] using wordTrace_append hprefix tailTrace_75869
  have hstable : (prefixWord ++ tailWord_75869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75869).length < 2 ^ (prefixWord ++ tailWord_75869).sum := by decide
  have hdescent : baseEnd_75869 < baseStart_75869 := by decide
  rcases family_descends (prefixWord ++ tailWord_75869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75872 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 4]
def baseStart_75872 : Nat := 118140960795 + 75872 * 2 ^ 59
def prefixEnd_75872 : Nat := 4983230072969 + 3 ^ 40 * 75872 * 2
def baseEnd_75872 : Nat := 38958804218032384151077

theorem tailTrace_75872 : CollatzResearch.WordTrace tailWord_75872 prefixEnd_75872 38958804218032384151077 := by
  unfold tailWord_75872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383639590568088375538935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1844852787424117834051913 1383639590568088375538935)
  ·
    refine ⟨2075459385852132563308403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1383639590568088375538935 2075459385852132563308403)
    ·
      refine ⟨3113189078778198844962605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2075459385852132563308403 3113189078778198844962605)
      ·
        refine ⟨1167445904541824566860977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3113189078778198844962605 1167445904541824566860977)
        ·
          refine ⟨875584428406368425145733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1167445904541824566860977 875584428406368425145733)
          ·
            refine ⟨164172080326194079714825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 875584428406368425145733 164172080326194079714825)
            ·
              refine ⟨123129060244645559786119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164172080326194079714825 123129060244645559786119)
              ·
                refine ⟨184693590366968339679179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123129060244645559786119 184693590366968339679179)
                ·
                  refine ⟨277040385550452509518769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184693590366968339679179 277040385550452509518769)
                  ·
                    refine ⟨207780289162839382139077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 277040385550452509518769 207780289162839382139077)
                    ·
                      refine ⟨38958804218032384151077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 207780289162839382139077 38958804218032384151077)
                      ·
                        rfl

theorem cell23_75872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_75872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75872 prefixEnd_75872 := by exact prefixLift 75872
  have htrace : WordTrace (prefixWord ++ tailWord_75872) baseStart_75872 baseEnd_75872 := by
    simpa [prefixWord, tailWord_75872, baseEnd_75872] using wordTrace_append hprefix tailTrace_75872
  have hstable : (prefixWord ++ tailWord_75872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75872).length < 2 ^ (prefixWord ++ tailWord_75872).sum := by decide
  have hdescent : baseEnd_75872 < baseStart_75872 := by decide
  rcases family_descends (prefixWord ++ tailWord_75872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75909 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 4, 1, 3]
def baseStart_75909 : Nat := 118140960795 + 75909 * 2 ^ 59
def prefixEnd_75909 : Nat := 4983230072969 + 3 ^ 40 * 75909 * 2
def baseEnd_75909 : Nat := 38977803002248739388407

theorem tailTrace_75909 : CollatzResearch.WordTrace tailWord_75909 prefixEnd_75909 38977803002248739388407 := by
  unfold tailWord_75909
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768628682002132070174781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1845752454668088046783187 2768628682002132070174781)
  ·
    refine ⟨1038235755750799526315543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2768628682002132070174781 1038235755750799526315543)
    ·
      refine ⟨1557353633626199289473315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1038235755750799526315543 1557353633626199289473315)
      ·
        refine ⟨2336030450439298934209973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557353633626199289473315 2336030450439298934209973)
        ·
          refine ⟨219002854728684275082185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2336030450439298934209973 219002854728684275082185)
          ·
            refine ⟨164252141046513206311639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219002854728684275082185 164252141046513206311639)
            ·
              refine ⟨246378211569769809467459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164252141046513206311639 246378211569769809467459)
              ·
                refine ⟨369567317354654714201189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246378211569769809467459 369567317354654714201189)
                ·
                  refine ⟨69293872003997758912723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369567317354654714201189 69293872003997758912723)
                  ·
                    refine ⟨103940808005996638369085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69293872003997758912723 103940808005996638369085)
                    ·
                      refine ⟨38977803002248739388407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 103940808005996638369085 38977803002248739388407)
                      ·
                        rfl

theorem cell23_75909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_75909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75909 prefixEnd_75909 := by exact prefixLift 75909
  have htrace : WordTrace (prefixWord ++ tailWord_75909) baseStart_75909 baseEnd_75909 := by
    simpa [prefixWord, tailWord_75909, baseEnd_75909] using wordTrace_append hprefix tailTrace_75909
  have hstable : (prefixWord ++ tailWord_75909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75909).length < 2 ^ (prefixWord ++ tailWord_75909).sum := by decide
  have hdescent : baseEnd_75909 < baseStart_75909 := by decide
  rcases family_descends (prefixWord ++ tailWord_75909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75925 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_75925 : Nat := 118140960795 + 75925 * 2 ^ 59
def prefixEnd_75925 : Nat := 4983230072969 + 3 ^ 40 * 75925 * 2
def baseEnd_75925 : Nat := 12995339564240225596111

theorem tailTrace_75925 : CollatzResearch.WordTrace tailWord_75925 prefixEnd_75925 12995339564240225596111 := by
  unfold tailWord_75925
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769212249944166802757229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1846141499962777868504819 2769212249944166802757229)
  ·
    refine ⟨1038454593729062551033961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2769212249944166802757229 1038454593729062551033961)
    ·
      refine ⟨778840945296796913275471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1038454593729062551033961 778840945296796913275471)
      ·
        refine ⟨1168261417945195369913207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778840945296796913275471 1168261417945195369913207)
        ·
          refine ⟨1752392126917793054869811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168261417945195369913207 1752392126917793054869811)
          ·
            refine ⟨2628588190376689582304717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752392126917793054869811 2628588190376689582304717)
            ·
              refine ⟨985720571391258593364269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2628588190376689582304717 985720571391258593364269)
              ·
                refine ⟨369645214271721972511601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 985720571391258593364269 369645214271721972511601)
                ·
                  refine ⟨277233910703791479383701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369645214271721972511601 277233910703791479383701)
                  ·
                    refine ⟨12995339564240225596111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 277233910703791479383701 12995339564240225596111)
                    ·
                      rfl

theorem cell23_75925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_75925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75925 prefixEnd_75925 := by exact prefixLift 75925
  have htrace : WordTrace (prefixWord ++ tailWord_75925) baseStart_75925 baseEnd_75925 := by
    simpa [prefixWord, tailWord_75925, baseEnd_75925] using wordTrace_append hprefix tailTrace_75925
  have hstable : (prefixWord ++ tailWord_75925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75925).length < 2 ^ (prefixWord ++ tailWord_75925).sum := by decide
  have hdescent : baseEnd_75925 < baseStart_75925 := by decide
  rcases family_descends (prefixWord ++ tailWord_75925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75936 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 1, 3, 2]
def baseStart_75936 : Nat := 118140960795 + 75936 * 2 ^ 59
def prefixEnd_75936 : Nat := 4983230072969 + 3 ^ 40 * 75936 * 2
def baseEnd_75936 : Nat := 38991666979920133750783

theorem tailTrace_75936 : CollatzResearch.WordTrace tailWord_75936 prefixEnd_75936 38991666979920133750783 := by
  unfold tailWord_75936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1384806726452157840703831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1846408968602877120938441 1384806726452157840703831)
  ·
    refine ⟨2077210089678236761055747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1384806726452157840703831 2077210089678236761055747)
    ·
      refine ⟨3115815134517355141583621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077210089678236761055747 3115815134517355141583621)
      ·
        refine ⟨584215337722004089046929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3115815134517355141583621 584215337722004089046929)
        ·
          refine ⟨438161503291503066785197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 584215337722004089046929 438161503291503066785197)
          ·
            refine ⟨164310563734313650044449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 438161503291503066785197 164310563734313650044449)
            ·
              refine ⟨123232922800735237533337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164310563734313650044449 123232922800735237533337)
              ·
                refine ⟨92424692100551428150003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123232922800735237533337 92424692100551428150003)
                ·
                  refine ⟨138637038150827142225005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92424692100551428150003 138637038150827142225005)
                  ·
                    refine ⟨51988889306560178334377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138637038150827142225005 51988889306560178334377)
                    ·
                      refine ⟨38991666979920133750783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 51988889306560178334377 38991666979920133750783)
                      ·
                        rfl

theorem cell23_75936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_75936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75936 prefixEnd_75936 := by exact prefixLift 75936
  have htrace : WordTrace (prefixWord ++ tailWord_75936) baseStart_75936 baseEnd_75936 := by
    simpa [prefixWord, tailWord_75936, baseEnd_75936] using wordTrace_append hprefix tailTrace_75936
  have hstable : (prefixWord ++ tailWord_75936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75936).length < 2 ^ (prefixWord ++ tailWord_75936).sum := by decide
  have hdescent : baseEnd_75936 < baseStart_75936 := by decide
  rcases family_descends (prefixWord ++ tailWord_75936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75965 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_75965 : Nat := 118140960795 + 75965 * 2 ^ 59
def prefixEnd_75965 : Nat := 4983230072969 + 3 ^ 40 * 75965 * 2
def baseEnd_75965 : Nat := 39006557918900520288149

theorem tailTrace_75965 : CollatzResearch.WordTrace tailWord_75965 prefixEnd_75965 39006557918900520288149 := by
  unfold tailWord_75965
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770671169799253634213349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1847114113199502422808899 2770671169799253634213349)
  ·
    refine ⟨519500844337360056415003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2770671169799253634213349 519500844337360056415003)
    ·
      refine ⟨779251266506040084622505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519500844337360056415003 779251266506040084622505)
      ·
        refine ⟨584438449879530063466879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 779251266506040084622505 584438449879530063466879)
        ·
          refine ⟨876657674819295095200319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584438449879530063466879 876657674819295095200319)
          ·
            refine ⟨1314986512228942642800479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876657674819295095200319 1314986512228942642800479)
            ·
              refine ⟨1972479768343413964200719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314986512228942642800479 1972479768343413964200719)
              ·
                refine ⟨2958719652515120946301079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972479768343413964200719 2958719652515120946301079)
                ·
                  refine ⟨4438079478772681419451619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2958719652515120946301079 4438079478772681419451619)
                  ·
                    refine ⟨6657119218159022129177429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4438079478772681419451619 6657119218159022129177429)
                    ·
                      refine ⟨39006557918900520288149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 6657119218159022129177429 39006557918900520288149)
                      ·
                        rfl

theorem cell23_75965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_75965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75965 prefixEnd_75965 := by exact prefixLift 75965
  have htrace : WordTrace (prefixWord ++ tailWord_75965) baseStart_75965 baseEnd_75965 := by
    simpa [prefixWord, tailWord_75965, baseEnd_75965] using wordTrace_append hprefix tailTrace_75965
  have hstable : (prefixWord ++ tailWord_75965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75965).length < 2 ^ (prefixWord ++ tailWord_75965).sum := by decide
  have hdescent : baseEnd_75965 < baseStart_75965 := by decide
  rcases family_descends (prefixWord ++ tailWord_75965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75985 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 3, 7]
def baseStart_75985 : Nat := 118140960795 + 75985 * 2 ^ 59
def prefixEnd_75985 : Nat := 4983230072969 + 3 ^ 40 * 75985 * 2
def baseEnd_75985 : Nat := 13005609177330147346019

theorem tailTrace_75985 : CollatzResearch.WordTrace tailWord_75985 prefixEnd_75985 13005609177330147346019 := by
  unfold tailWord_75985
  simp only [CollatzResearch.WordTrace]
  refine ⟨2771400629726797049941409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1847600419817864699960939 2771400629726797049941409)
  ·
    refine ⟨2078550472295097787456057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2771400629726797049941409 2078550472295097787456057)
    ·
      refine ⟨1558912854221323340592043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2078550472295097787456057 1558912854221323340592043)
      ·
        refine ⟨2338369281331985010888065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558912854221323340592043 2338369281331985010888065)
        ·
          refine ⟨1753776960998988758166049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2338369281331985010888065 1753776960998988758166049)
          ·
            refine ⟨1315332720749241568624537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1753776960998988758166049 1315332720749241568624537)
            ·
              refine ⟨986499540561931176468403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1315332720749241568624537 986499540561931176468403)
              ·
                refine ⟨1479749310842896764702605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986499540561931176468403 1479749310842896764702605)
                ·
                  refine ⟨554905991566086286763477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1479749310842896764702605 554905991566086286763477)
                  ·
                    refine ⟨13005609177330147346019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 554905991566086286763477 13005609177330147346019)
                    ·
                      rfl

theorem cell23_75985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_75985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75985 prefixEnd_75985 := by exact prefixLift 75985
  have htrace : WordTrace (prefixWord ++ tailWord_75985) baseStart_75985 baseEnd_75985 := by
    simpa [prefixWord, tailWord_75985, baseEnd_75985] using wordTrace_append hprefix tailTrace_75985
  have hstable : (prefixWord ++ tailWord_75985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75985).length < 2 ^ (prefixWord ++ tailWord_75985).sum := by decide
  have hdescent : baseEnd_75985 < baseStart_75985 := by decide
  rcases family_descends (prefixWord ++ tailWord_75985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75995 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 5]
def baseStart_75995 : Nat := 118140960795 + 75995 * 2 ^ 59
def prefixEnd_75995 : Nat := 4983230072969 + 3 ^ 40 * 75995 * 2
def baseEnd_75995 : Nat := 39021962338535402913011

theorem tailTrace_75995 : CollatzResearch.WordTrace tailWord_75995 prefixEnd_75995 39021962338535402913011 := by
  unfold tailWord_75995
  simp only [CollatzResearch.WordTrace]
  refine ⟨2771765359690568757805439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1847843573127045838536959 2771765359690568757805439)
  ·
    refine ⟨4157648039535853136708159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2771765359690568757805439 4157648039535853136708159)
    ·
      refine ⟨6236472059303779705062239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4157648039535853136708159 6236472059303779705062239)
      ·
        refine ⟨9354708088955669557593359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6236472059303779705062239 9354708088955669557593359)
        ·
          refine ⟨14032062133433504336390039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9354708088955669557593359 14032062133433504336390039)
          ·
            refine ⟨21048093200150256504585059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14032062133433504336390039 21048093200150256504585059)
            ·
              refine ⟨31572139800225384756877589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21048093200150256504585059 31572139800225384756877589)
              ·
                refine ⟨1479944053135564910478637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31572139800225384756877589 1479944053135564910478637)
                ·
                  refine ⟨554979019925836841429489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1479944053135564910478637 554979019925836841429489)
                  ·
                    refine ⟨416234264944377631072117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 554979019925836841429489 416234264944377631072117)
                    ·
                      refine ⟨39021962338535402913011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 416234264944377631072117 39021962338535402913011)
                      ·
                        rfl

theorem cell23_75995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_75995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_75995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_75995 prefixEnd_75995 := by exact prefixLift 75995
  have htrace : WordTrace (prefixWord ++ tailWord_75995) baseStart_75995 baseEnd_75995 := by
    simpa [prefixWord, tailWord_75995, baseEnd_75995] using wordTrace_append hprefix tailTrace_75995
  have hstable : (prefixWord ++ tailWord_75995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75995).length < 2 ^ (prefixWord ++ tailWord_75995).sum := by decide
  have hdescent : baseEnd_75995 < baseStart_75995 := by decide
  rcases family_descends (prefixWord ++ tailWord_75995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76049 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 3, 4]
def baseStart_76049 : Nat := 118140960795 + 76049 * 2 ^ 59
def prefixEnd_76049 : Nat := 4983230072969 + 3 ^ 40 * 76049 * 2
def baseEnd_76049 : Nat := 13016563431292730545921

theorem tailTrace_76049 : CollatzResearch.WordTrace tailWord_76049 prefixEnd_76049 13016563431292730545921 := by
  unfold tailWord_76049
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773734901494935980271201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1849156600996623986847467 2773734901494935980271201)
  ·
    refine ⟨2080301176121201985203401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2773734901494935980271201 2080301176121201985203401)
    ·
      refine ⟨1560225882090901488902551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2080301176121201985203401 1560225882090901488902551)
      ·
        refine ⟨2340338823136352233353827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1560225882090901488902551 2340338823136352233353827)
        ·
          refine ⟨3510508234704528350030741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340338823136352233353827 3510508234704528350030741)
          ·
            refine ⟨164555073501774766407691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3510508234704528350030741 164555073501774766407691)
            ·
              refine ⟨246832610252662149611537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164555073501774766407691 246832610252662149611537)
              ·
                refine ⟨185124457689496612208653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246832610252662149611537 185124457689496612208653)
                ·
                  refine ⟨69421671633561229578245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185124457689496612208653 69421671633561229578245)
                  ·
                    refine ⟨13016563431292730545921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69421671633561229578245 13016563431292730545921)
                    ·
                      rfl

theorem cell23_76049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_76049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76049 prefixEnd_76049 := by exact prefixLift 76049
  have htrace : WordTrace (prefixWord ++ tailWord_76049) baseStart_76049 baseEnd_76049 := by
    simpa [prefixWord, tailWord_76049, baseEnd_76049] using wordTrace_append hprefix tailTrace_76049
  have hstable : (prefixWord ++ tailWord_76049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76049).length < 2 ^ (prefixWord ++ tailWord_76049).sum := by decide
  have hdescent : baseEnd_76049 < baseStart_76049 := by decide
  rcases family_descends (prefixWord ++ tailWord_76049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76059 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 3]
def baseStart_76059 : Nat := 118140960795 + 76059 * 2 ^ 59
def prefixEnd_76059 : Nat := 4983230072969 + 3 ^ 40 * 76059 * 2
def baseEnd_76059 : Nat := 39054825100423152512717

theorem tailTrace_76059 : CollatzResearch.WordTrace tailWord_76059 prefixEnd_76059 39054825100423152512717 := by
  unfold tailWord_76059
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774099631458707688135231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1849399754305805125423487 2774099631458707688135231)
  ·
    refine ⟨4161149447188061532202847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2774099631458707688135231 4161149447188061532202847)
    ·
      refine ⟨6241724170782092298304271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4161149447188061532202847 6241724170782092298304271)
      ·
        refine ⟨9362586256173138447456407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6241724170782092298304271 9362586256173138447456407)
        ·
          refine ⟨14043879384259707671184611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9362586256173138447456407 14043879384259707671184611)
          ·
            refine ⟨21065819076389561506776917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14043879384259707671184611 21065819076389561506776917)
            ·
              refine ⟨123432533650720086953771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 21065819076389561506776917 123432533650720086953771)
              ·
                refine ⟨185148800476080130430657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123432533650720086953771 185148800476080130430657)
                ·
                  refine ⟨138861600357060097822993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185148800476080130430657 138861600357060097822993)
                  ·
                    refine ⟨104146200267795073367245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 138861600357060097822993 104146200267795073367245)
                    ·
                      refine ⟨39054825100423152512717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 104146200267795073367245 39054825100423152512717)
                      ·
                        rfl

theorem cell23_76059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 3].length) (baseStart_76059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_76059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_76059 prefixEnd_76059 := by exact prefixLift 76059
  have htrace : WordTrace (prefixWord ++ tailWord_76059) baseStart_76059 baseEnd_76059 := by
    simpa [prefixWord, tailWord_76059, baseEnd_76059] using wordTrace_append hprefix tailTrace_76059
  have hstable : (prefixWord ++ tailWord_76059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76059).length < 2 ^ (prefixWord ++ tailWord_76059).sum := by decide
  have hdescent : baseEnd_76059 < baseStart_76059 := by decide
  rcases family_descends (prefixWord ++ tailWord_76059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
