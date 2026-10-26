import V185TrunkScan22Chunk424

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3789188 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_3789188 : Nat := 118140960795 + 3789188 * 2 ^ 59
def prefixEnd_3789188 : Nat := 4983230072969 + 3 ^ 40 * 3789188 * 2
def baseEnd_3789188 : Nat := 1297116489499217345482565

theorem tailTrace_3789188 : CollatzResearch.WordTrace tailWord_3789188 prefixEnd_3789188 1297116489499217345482565 := by
  unfold tailWord_3789188
  simp only [CollatzResearch.WordTrace]
  refine ⟨69101520098213246316960109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92135360130950995089280145 69101520098213246316960109)
  ·
    refine ⟨25913070036829967368860041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69101520098213246316960109 25913070036829967368860041)
    ·
      refine ⟨19434802527622475526645031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25913070036829967368860041 19434802527622475526645031)
      ·
        refine ⟨29152203791433713289967547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19434802527622475526645031 29152203791433713289967547)
        ·
          refine ⟨43728305687150569934951321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29152203791433713289967547 43728305687150569934951321)
          ·
            refine ⟨32796229265362927451213491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43728305687150569934951321 32796229265362927451213491)
            ·
              refine ⟨49194343898044391176820237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32796229265362927451213491 49194343898044391176820237)
              ·
                refine ⟨18447878961766646691307589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49194343898044391176820237 18447878961766646691307589)
                ·
                  refine ⟨3458977305331246254620173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18447878961766646691307589 3458977305331246254620173)
                  ·
                    refine ⟨1297116489499217345482565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458977305331246254620173 1297116489499217345482565)
                    ·
                      rfl

theorem cell22_3789188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_3789188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789188 prefixEnd_3789188 := by exact prefixLift 3789188
  have htrace : WordTrace (prefixWord ++ tailWord_3789188) baseStart_3789188 baseEnd_3789188 := by
    simpa [prefixWord, tailWord_3789188, baseEnd_3789188] using wordTrace_append hprefix tailTrace_3789188
  have hstable : (prefixWord ++ tailWord_3789188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789188).length < 2 ^ (prefixWord ++ tailWord_3789188).sum := by decide
  have hdescent : baseEnd_3789188 < baseStart_3789188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789226 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3789226 : Nat := 118140960795 + 3789226 * 2 ^ 59
def prefixEnd_3789226 : Nat := 4983230072969 + 3 ^ 40 * 3789226 * 2
def baseEnd_3789226 : Nat := 1297129497675797913032449

theorem tailTrace_3789226 : CollatzResearch.WordTrace tailWord_3789226 prefixEnd_3789226 1297129497675797913032449 := by
  unfold tailWord_3789226
  simp only [CollatzResearch.WordTrace]
  refine ⟨34551106542572206280950883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92136284113525883415869021 34551106542572206280950883)
  ·
    refine ⟨51826659813858309421426325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34551106542572206280950883 51826659813858309421426325)
    ·
      refine ⟨2429374678774608254129359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51826659813858309421426325 2429374678774608254129359)
      ·
        refine ⟨3644062018161912381194039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429374678774608254129359 3644062018161912381194039)
        ·
          refine ⟨5466093027242868571791059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3644062018161912381194039 5466093027242868571791059)
          ·
            refine ⟨8199139540864302857686589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466093027242868571791059 8199139540864302857686589)
            ·
              refine ⟨3074677327824113571632471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8199139540864302857686589 3074677327824113571632471)
              ·
                refine ⟨4612015991736170357448707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3074677327824113571632471 4612015991736170357448707)
                ·
                  refine ⟨6918023987604255536173061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612015991736170357448707 6918023987604255536173061)
                  ·
                    refine ⟨1297129497675797913032449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6918023987604255536173061 1297129497675797913032449)
                    ·
                      rfl

theorem cell22_3789226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3789226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789226 prefixEnd_3789226 := by exact prefixLift 3789226
  have htrace : WordTrace (prefixWord ++ tailWord_3789226) baseStart_3789226 baseEnd_3789226 := by
    simpa [prefixWord, tailWord_3789226, baseEnd_3789226] using wordTrace_append hprefix tailTrace_3789226
  have hstable : (prefixWord ++ tailWord_3789226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789226).length < 2 ^ (prefixWord ++ tailWord_3789226).sum := by decide
  have hdescent : baseEnd_3789226 < baseStart_3789226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789252 : List Nat := [2, 3, 3, 2, 3, 1, 1, 7]
def baseStart_3789252 : Nat := 118140960795 + 3789252 * 2 ^ 59
def prefixEnd_3789252 : Nat := 4983230072969 + 3 ^ 40 * 3789252 * 2
def baseEnd_3789252 : Nat := 144126488667460279098041

theorem tailTrace_3789252 : CollatzResearch.WordTrace tailWord_3789252 prefixEnd_3789252 144126488667460279098041 := by
  unfold tailWord_3789252
  simp only [CollatzResearch.WordTrace]
  refine ⟨69102687234097315782125005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92136916312129754376166673 69102687234097315782125005)
  ·
    refine ⟨25913507712786493418296877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69102687234097315782125005 25913507712786493418296877)
    ·
      refine ⟨9717565392294935031861329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25913507712786493418296877 9717565392294935031861329)
      ·
        refine ⟨7288174044221201273895997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9717565392294935031861329 7288174044221201273895997)
        ·
          refine ⟨2733065266582950477710999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7288174044221201273895997 2733065266582950477710999)
          ·
            refine ⟨4099597899874425716566499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733065266582950477710999 4099597899874425716566499)
            ·
              refine ⟨6149396849811638574849749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099597899874425716566499 6149396849811638574849749)
              ·
                refine ⟨144126488667460279098041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6149396849811638574849749 144126488667460279098041)
                ·
                  rfl

theorem cell22_3789252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 7].length) (baseStart_3789252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789252 prefixEnd_3789252 := by exact prefixLift 3789252
  have htrace : WordTrace (prefixWord ++ tailWord_3789252) baseStart_3789252 baseEnd_3789252 := by
    simpa [prefixWord, tailWord_3789252, baseEnd_3789252] using wordTrace_append hprefix tailTrace_3789252
  have hstable : (prefixWord ++ tailWord_3789252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789252).length < 2 ^ (prefixWord ++ tailWord_3789252).sum := by decide
  have hdescent : baseEnd_3789252 < baseStart_3789252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789291 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 8]
def baseStart_3789291 : Nat := 118140960795 + 3789291 * 2 ^ 59
def prefixEnd_3789291 : Nat := 4983230072969 + 3 ^ 40 * 3789291 * 2
def baseEnd_3789291 : Nat := 432383916168053136719083

theorem tailTrace_3789291 : CollatzResearch.WordTrace tailWord_3789291 prefixEnd_3789291 432383916168053136719083 := by
  unfold tailWord_3789291
  simp only [CollatzResearch.WordTrace]
  refine ⟨138206796915053341224919727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92137864610035560816613151 138206796915053341224919727)
  ·
    refine ⟨207310195372580011837379591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138206796915053341224919727 207310195372580011837379591)
    ·
      refine ⟨310965293058870017756069387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207310195372580011837379591 310965293058870017756069387)
      ·
        refine ⟨466447939588305026634104081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310965293058870017756069387 466447939588305026634104081)
        ·
          refine ⟨349835954691228769975578061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466447939588305026634104081 349835954691228769975578061)
          ·
            refine ⟨131188483009210788740841773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349835954691228769975578061 131188483009210788740841773)
            ·
              refine ⟨49195681128454045777815665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131188483009210788740841773 49195681128454045777815665)
              ·
                refine ⟨36896760846340534333361749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49195681128454045777815665 36896760846340534333361749)
                ·
                  refine ⟨432383916168053136719083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36896760846340534333361749 432383916168053136719083)
                  ·
                    rfl

theorem cell22_3789291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 8].length) (baseStart_3789291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789291 prefixEnd_3789291 := by exact prefixLift 3789291
  have htrace : WordTrace (prefixWord ++ tailWord_3789291) baseStart_3789291 baseEnd_3789291 := by
    simpa [prefixWord, tailWord_3789291, baseEnd_3789291] using wordTrace_append hprefix tailTrace_3789291
  have hstable : (prefixWord ++ tailWord_3789291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789291).length < 2 ^ (prefixWord ++ tailWord_3789291).sum := by decide
  have hdescent : baseEnd_3789291 < baseStart_3789291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789314 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3789314 : Nat := 118140960795 + 3789314 * 2 ^ 59
def prefixEnd_3789314 : Nat := 4983230072969 + 3 ^ 40 * 3789314 * 2
def baseEnd_3789314 : Nat := 432386540624731672277393

theorem tailTrace_3789314 : CollatzResearch.WordTrace tailWord_3789314 prefixEnd_3789314 432386540624731672277393 := by
  unfold tailWord_3789314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34551908948492504038251749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92138423862646677435337997 34551908948492504038251749)
  ·
    refine ⟨6478482927842344507172203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34551908948492504038251749 6478482927842344507172203)
    ·
      refine ⟨9717724391763516760758305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6478482927842344507172203 9717724391763516760758305)
      ·
        refine ⟨7288293293822637570568729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9717724391763516760758305 7288293293822637570568729)
        ·
          refine ⟨5466219970366978177926547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7288293293822637570568729 5466219970366978177926547)
          ·
            refine ⟨8199329955550467266889821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466219970366978177926547 8199329955550467266889821)
            ·
              refine ⟨3074748733331425225083683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8199329955550467266889821 3074748733331425225083683)
              ·
                refine ⟨4612123099997137837625525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3074748733331425225083683 4612123099997137837625525)
                ·
                  refine ⟨432386540624731672277393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4612123099997137837625525 432386540624731672277393)
                  ·
                    rfl

theorem cell22_3789314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3789314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789314 prefixEnd_3789314 := by exact prefixLift 3789314
  have htrace : WordTrace (prefixWord ++ tailWord_3789314) baseStart_3789314 baseEnd_3789314 := by
    simpa [prefixWord, tailWord_3789314, baseEnd_3789314] using wordTrace_append hprefix tailTrace_3789314
  have hstable : (prefixWord ++ tailWord_3789314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789314).length < 2 ^ (prefixWord ++ tailWord_3789314).sum := by decide
  have hdescent : baseEnd_3789314 < baseStart_3789314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789338 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_3789338 : Nat := 118140960795 + 3789338 * 2 ^ 59
def prefixEnd_3789338 : Nat := 4983230072969 + 3 ^ 40 * 3789338 * 2
def baseEnd_3789338 : Nat := 1297167837564666954232105

theorem tailTrace_3789338 : CollatzResearch.WordTrace tailWord_3789338 prefixEnd_3789338 1297167837564666954232105 := by
  unfold tailWord_3789338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34552127786470767062970167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92139007430588712167920445 34552127786470767062970167)
  ·
    refine ⟨51828191679706150594455251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34552127786470767062970167 51828191679706150594455251)
    ·
      refine ⟨77742287519559225891682877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51828191679706150594455251 77742287519559225891682877)
      ·
        refine ⟨29153357819834709709381079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77742287519559225891682877 29153357819834709709381079)
        ·
          refine ⟨43730036729752064564071619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29153357819834709709381079 43730036729752064564071619)
          ·
            refine ⟨65595055094628096846107429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43730036729752064564071619 65595055094628096846107429)
            ·
              refine ⟨12299072830242768158645143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65595055094628096846107429 12299072830242768158645143)
              ·
                refine ⟨18448609245364152237967715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12299072830242768158645143 18448609245364152237967715)
                ·
                  refine ⟨27672913868046228356951573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18448609245364152237967715 27672913868046228356951573)
                  ·
                    refine ⟨1297167837564666954232105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27672913868046228356951573 1297167837564666954232105)
                    ·
                      rfl

theorem cell22_3789338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_3789338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789338 prefixEnd_3789338 := by exact prefixLift 3789338
  have htrace : WordTrace (prefixWord ++ tailWord_3789338) baseStart_3789338 baseEnd_3789338 := by
    simpa [prefixWord, tailWord_3789338, baseEnd_3789338] using wordTrace_append hprefix tailTrace_3789338
  have hstable : (prefixWord ++ tailWord_3789338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789338).length < 2 ^ (prefixWord ++ tailWord_3789338).sum := by decide
  have hdescent : baseEnd_3789338 < baseStart_3789338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789340 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 4, 3]
def baseStart_3789340 : Nat := 118140960795 + 3789340 * 2 ^ 59
def prefixEnd_3789340 : Nat := 4983230072969 + 3 ^ 40 * 3789340 * 2
def baseEnd_3789340 : Nat := 1297168522205539615682099

theorem tailTrace_3789340 : CollatzResearch.WordTrace tailWord_3789340 prefixEnd_3789340 1297168522205539615682099 := by
  unfold tailWord_3789340
  simp only [CollatzResearch.WordTrace]
  refine ⟨69104292045937911296726737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92139056061250548395635649 69104292045937911296726737)
  ·
    refine ⟨51828219034453433472545053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69104292045937911296726737 51828219034453433472545053)
    ·
      refine ⟨19435582137920037552204395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51828219034453433472545053 19435582137920037552204395)
      ·
        refine ⟨29153373206880056328306593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19435582137920037552204395 29153373206880056328306593)
        ·
          refine ⟨21865029905160042246229945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29153373206880056328306593 21865029905160042246229945)
          ·
            refine ⟨16398772428870031684672459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21865029905160042246229945 16398772428870031684672459)
            ·
              refine ⟨24598158643305047527008689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16398772428870031684672459 24598158643305047527008689)
              ·
                refine ⟨18448618982478785645256517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24598158643305047527008689 18448618982478785645256517)
                ·
                  refine ⟨3459116059214772308485597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18448618982478785645256517 3459116059214772308485597)
                  ·
                    refine ⟨1297168522205539615682099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3459116059214772308485597 1297168522205539615682099)
                    ·
                      rfl

theorem cell22_3789340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_3789340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789340 prefixEnd_3789340 := by exact prefixLift 3789340
  have htrace : WordTrace (prefixWord ++ tailWord_3789340) baseStart_3789340 baseEnd_3789340 := by
    simpa [prefixWord, tailWord_3789340, baseEnd_3789340] using wordTrace_append hprefix tailTrace_3789340
  have hstable : (prefixWord ++ tailWord_3789340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789340).length < 2 ^ (prefixWord ++ tailWord_3789340).sum := by decide
  have hdescent : baseEnd_3789340 < baseStart_3789340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789443 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 8]
def baseStart_3789443 : Nat := 118140960795 + 3789443 * 2 ^ 59
def prefixEnd_3789443 : Nat := 4983230072969 + 3 ^ 40 * 3789443 * 2
def baseEnd_3789443 : Nat := 432401260403493893452261

theorem tailTrace_3789443 : CollatzResearch.WordTrace tailWord_3789443 prefixEnd_3789443 432401260403493893452261 := by
  unfold tailWord_3789443
  simp only [CollatzResearch.WordTrace]
  refine ⟨138212340810502671184452983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92141560540335114122968655 138212340810502671184452983)
  ·
    refine ⟨207318511215754006776679475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138212340810502671184452983 207318511215754006776679475)
    ·
      refine ⟨310977766823631010165019213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207318511215754006776679475 310977766823631010165019213)
      ·
        refine ⟨116616662558861628811882205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310977766823631010165019213 116616662558861628811882205)
        ·
          refine ⟨43731248459573110804455827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116616662558861628811882205 43731248459573110804455827)
          ·
            refine ⟨65596872689359666206683741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43731248459573110804455827 65596872689359666206683741)
            ·
              refine ⟨24598827258509874827506403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65596872689359666206683741 24598827258509874827506403)
              ·
                refine ⟨36898240887764812241259605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24598827258509874827506403 36898240887764812241259605)
                ·
                  refine ⟨432401260403493893452261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36898240887764812241259605 432401260403493893452261)
                  ·
                    rfl

theorem cell22_3789443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 8].length) (baseStart_3789443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789443 prefixEnd_3789443 := by exact prefixLift 3789443
  have htrace : WordTrace (prefixWord ++ tailWord_3789443) baseStart_3789443 baseEnd_3789443 := by
    simpa [prefixWord, tailWord_3789443, baseEnd_3789443] using wordTrace_append hprefix tailTrace_3789443
  have hstable : (prefixWord ++ tailWord_3789443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789443).length < 2 ^ (prefixWord ++ tailWord_3789443).sum := by decide
  have hdescent : baseEnd_3789443 < baseStart_3789443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789445 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_3789445 : Nat := 118140960795 + 3789445 * 2 ^ 59
def prefixEnd_3789445 : Nat := 4983230072969 + 3 ^ 40 * 3789445 * 2
def baseEnd_3789445 : Nat := 1297204465851354341806777

theorem tailTrace_3789445 : CollatzResearch.WordTrace tailWord_3789445 prefixEnd_3789445 1297204465851354341806777 := by
  unfold tailWord_3789445
  simp only [CollatzResearch.WordTrace]
  refine ⟨138212413756495425526025789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92141609170996950350683859 138212413756495425526025789)
  ·
    refine ⟨51829655158685784572259671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138212413756495425526025789 51829655158685784572259671)
    ·
      refine ⟨77744482738028676858389507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51829655158685784572259671 77744482738028676858389507)
      ·
        refine ⟨116616724107043015287584261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77744482738028676858389507 116616724107043015287584261)
        ·
          refine ⟨21865635770070565366422049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116616724107043015287584261 21865635770070565366422049)
          ·
            refine ⟨16399226827552924024816537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21865635770070565366422049 16399226827552924024816537)
            ·
              refine ⟨12299420120664693018612403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16399226827552924024816537 12299420120664693018612403)
              ·
                refine ⟨18449130180997039527918605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12299420120664693018612403 18449130180997039527918605)
                ·
                  refine ⟨6918423817873889822969477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18449130180997039527918605 6918423817873889822969477)
                  ·
                    refine ⟨1297204465851354341806777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6918423817873889822969477 1297204465851354341806777)
                    ·
                      rfl

theorem cell22_3789445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_3789445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789445 prefixEnd_3789445 := by exact prefixLift 3789445
  have htrace : WordTrace (prefixWord ++ tailWord_3789445) baseStart_3789445 baseEnd_3789445 := by
    simpa [prefixWord, tailWord_3789445, baseEnd_3789445] using wordTrace_append hprefix tailTrace_3789445
  have hstable : (prefixWord ++ tailWord_3789445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789445).length < 2 ^ (prefixWord ++ tailWord_3789445).sum := by decide
  have hdescent : baseEnd_3789445 < baseStart_3789445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789466 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 5]
def baseStart_3789466 : Nat := 118140960795 + 3789466 * 2 ^ 59
def prefixEnd_3789466 : Nat := 4983230072969 + 3 ^ 40 * 3789466 * 2
def baseEnd_3789466 : Nat := 432403884860172429010571

theorem tailTrace_3789466 : CollatzResearch.WordTrace tailWord_3789466 prefixEnd_3789466 432403884860172429010571 := by
  unfold tailWord_3789466
  simp only [CollatzResearch.WordTrace]
  refine ⟨34553294922354836528135063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92142119792946230741693501 34553294922354836528135063)
  ·
    refine ⟨51829942383532254792202595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34553294922354836528135063 51829942383532254792202595)
    ·
      refine ⟨77744913575298382188303893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51829942383532254792202595 77744913575298382188303893)
      ·
        refine ⟨3644292823842111665076745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77744913575298382188303893 3644292823842111665076745)
        ·
          refine ⟨2733219617881583748807559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3644292823842111665076745 2733219617881583748807559)
          ·
            refine ⟨4099829426822375623211339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733219617881583748807559 4099829426822375623211339)
            ·
              refine ⟨6149744140233563434817009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099829426822375623211339 6149744140233563434817009)
              ·
                refine ⟨4612308105175172576112757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6149744140233563434817009 4612308105175172576112757)
                ·
                  refine ⟨432403884860172429010571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4612308105175172576112757 432403884860172429010571)
                  ·
                    rfl

theorem cell22_3789466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_3789466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789466 prefixEnd_3789466 := by exact prefixLift 3789466
  have htrace : WordTrace (prefixWord ++ tailWord_3789466) baseStart_3789466 baseEnd_3789466 := by
    simpa [prefixWord, tailWord_3789466, baseEnd_3789466] using wordTrace_append hprefix tailTrace_3789466
  have hstable : (prefixWord ++ tailWord_3789466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789466).length < 2 ^ (prefixWord ++ tailWord_3789466).sum := by decide
  have hdescent : baseEnd_3789466 < baseStart_3789466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789488 : List Nat := [2, 1, 1, 1, 2, 1, 3, 11]
def baseStart_3789488 : Nat := 118140960795 + 3789488 * 2 ^ 59
def prefixEnd_3789488 : Nat := 4983230072969 + 3 ^ 40 * 3789488 * 2
def baseEnd_3789488 : Nat := 144135465070012951442405

theorem tailTrace_3789488 : CollatzResearch.WordTrace tailWord_3789488 prefixEnd_3789488 144135465070012951442405 := by
  unfold tailWord_3789488
  simp only [CollatzResearch.WordTrace]
  refine ⟨69106991047669821934920559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92142654730226429246560745 69106991047669821934920559)
  ·
    refine ⟨103660486571504732902380839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69106991047669821934920559 103660486571504732902380839)
    ·
      refine ⟨155490729857257099353571259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103660486571504732902380839 155490729857257099353571259)
      ·
        refine ⟨233236094785885649030356889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155490729857257099353571259 233236094785885649030356889)
        ·
          refine ⟨174927071089414236772767667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233236094785885649030356889 174927071089414236772767667)
          ·
            refine ⟨262390606634121355159151501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174927071089414236772767667 262390606634121355159151501)
            ·
              refine ⟨98396477487795508184681813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262390606634121355159151501 98396477487795508184681813)
              ·
                refine ⟨144135465070012951442405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 98396477487795508184681813 144135465070012951442405)
                ·
                  rfl

theorem cell22_3789488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 11].length) (baseStart_3789488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789488 prefixEnd_3789488 := by exact prefixLift 3789488
  have htrace : WordTrace (prefixWord ++ tailWord_3789488) baseStart_3789488 baseEnd_3789488 := by
    simpa [prefixWord, tailWord_3789488, baseEnd_3789488] using wordTrace_append hprefix tailTrace_3789488
  have hstable : (prefixWord ++ tailWord_3789488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789488).length < 2 ^ (prefixWord ++ tailWord_3789488).sum := by decide
  have hdescent : baseEnd_3789488 < baseStart_3789488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789522 : List Nat := [3, 2, 2, 2, 3, 2, 8]
def baseStart_3789522 : Nat := 118140960795 + 3789522 * 2 ^ 59
def prefixEnd_3789522 : Nat := 4983230072969 + 3 ^ 40 * 3789522 * 2
def baseEnd_3789522 : Nat := 48045586093516733615983

theorem tailTrace_3789522 : CollatzResearch.WordTrace tailWord_3789522 prefixEnd_3789522 48045586093516733615983 := by
  unfold tailWord_3789522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34553805544304116919144705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92143481451477645117719213 34553805544304116919144705)
  ·
    refine ⟨25915354158228087689358529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34553805544304116919144705 25915354158228087689358529)
    ·
      refine ⟨19436515618671065767018897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25915354158228087689358529 19436515618671065767018897)
      ·
        refine ⟨14577386714003299325264173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19436515618671065767018897 14577386714003299325264173)
        ·
          refine ⟨5466520017751237246974065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14577386714003299325264173 5466520017751237246974065)
          ·
            refine ⟨4099890013313427935230549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5466520017751237246974065 4099890013313427935230549)
            ·
              refine ⟨48045586093516733615983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4099890013313427935230549 48045586093516733615983)
              ·
                rfl

theorem cell22_3789522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 8].length) (baseStart_3789522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789522 prefixEnd_3789522 := by exact prefixLift 3789522
  have htrace : WordTrace (prefixWord ++ tailWord_3789522) baseStart_3789522 baseEnd_3789522 := by
    simpa [prefixWord, tailWord_3789522, baseEnd_3789522] using wordTrace_append hprefix tailTrace_3789522
  have hstable : (prefixWord ++ tailWord_3789522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789522).length < 2 ^ (prefixWord ++ tailWord_3789522).sum := by decide
  have hdescent : baseEnd_3789522 < baseStart_3789522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789524 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_3789524 : Nat := 118140960795 + 3789524 * 2 ^ 59
def prefixEnd_3789524 : Nat := 4983230072969 + 3 ^ 40 * 3789524 * 2
def baseEnd_3789524 : Nat := 1297231509165824469081535

theorem tailTrace_3789524 : CollatzResearch.WordTrace tailWord_3789524 prefixEnd_3789524 1297231509165824469081535 := by
  unfold tailWord_3789524
  simp only [CollatzResearch.WordTrace]
  refine ⟨69107647561604611009075813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92143530082139481345434417 69107647561604611009075813)
  ·
    refine ⟨12957683917800864564201715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69107647561604611009075813 12957683917800864564201715)
    ·
      refine ⟨19436525876701296846302573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12957683917800864564201715 19436525876701296846302573)
      ·
        refine ⟨7288697203762986317363465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19436525876701296846302573 7288697203762986317363465)
        ·
          refine ⟨5466522902822239738022599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7288697203762986317363465 5466522902822239738022599)
          ·
            refine ⟨8199784354233359607033899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466522902822239738022599 8199784354233359607033899)
            ·
              refine ⟨12299676531350039410550849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8199784354233359607033899 12299676531350039410550849)
              ·
                refine ⟨9224757398512529557913137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12299676531350039410550849 9224757398512529557913137)
                ·
                  refine ⟨6918568048884397168434853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9224757398512529557913137 6918568048884397168434853)
                  ·
                    refine ⟨1297231509165824469081535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6918568048884397168434853 1297231509165824469081535)
                    ·
                      rfl

theorem cell22_3789524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_3789524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789524 prefixEnd_3789524 := by exact prefixLift 3789524
  have htrace : WordTrace (prefixWord ++ tailWord_3789524) baseStart_3789524 baseEnd_3789524 := by
    simpa [prefixWord, tailWord_3789524, baseEnd_3789524] using wordTrace_append hprefix tailTrace_3789524
  have hstable : (prefixWord ++ tailWord_3789524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789524).length < 2 ^ (prefixWord ++ tailWord_3789524).sum := by decide
  have hdescent : baseEnd_3789524 < baseStart_3789524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789614 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3789614 : Nat := 118140960795 + 3789614 * 2 ^ 59
def prefixEnd_3789614 : Nat := 4983230072969 + 3 ^ 40 * 3789614 * 2
def baseEnd_3789614 : Nat := 1297262318005094234331259

theorem tailTrace_3789614 : CollatzResearch.WordTrace tailWord_3789614 prefixEnd_3789614 1297262318005094234331259 := by
  unfold tailWord_3789614
  simp only [CollatzResearch.WordTrace]
  refine ⟨17277322211610395923615987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92145718461922111592618597 17277322211610395923615987)
  ·
    refine ⟨25915983317415593885423981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17277322211610395923615987 25915983317415593885423981)
    ·
      refine ⟨9718493744030847707033993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25915983317415593885423981 9718493744030847707033993)
      ·
        refine ⟨7288870308023135780275495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9718493744030847707033993 7288870308023135780275495)
        ·
          refine ⟨10933305462034703670413243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7288870308023135780275495 10933305462034703670413243)
          ·
            refine ⟨16399958193052055505619865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10933305462034703670413243 16399958193052055505619865)
            ·
              refine ⟨12299968644789041629214899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16399958193052055505619865 12299968644789041629214899)
              ·
                refine ⟨18449952967183562443822349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12299968644789041629214899 18449952967183562443822349)
                ·
                  refine ⟨6918732362693835916433381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18449952967183562443822349 6918732362693835916433381)
                  ·
                    refine ⟨1297262318005094234331259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6918732362693835916433381 1297262318005094234331259)
                    ·
                      rfl

theorem cell22_3789614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3789614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789614 prefixEnd_3789614 := by exact prefixLift 3789614
  have htrace : WordTrace (prefixWord ++ tailWord_3789614) baseStart_3789614 baseEnd_3789614 := by
    simpa [prefixWord, tailWord_3789614, baseEnd_3789614] using wordTrace_append hprefix tailTrace_3789614
  have hstable : (prefixWord ++ tailWord_3789614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789614).length < 2 ^ (prefixWord ++ tailWord_3789614).sum := by decide
  have hdescent : baseEnd_3789614 < baseStart_3789614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789631 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 1, 4]
def baseStart_3789631 : Nat := 118140960795 + 3789631 * 2 ^ 59
def prefixEnd_3789631 : Nat := 4983230072969 + 3 ^ 40 * 3789631 * 2
def baseEnd_3789631 : Nat := 1297268137452511856656207

theorem tailTrace_3789631 : CollatzResearch.WordTrace tailWord_3789631 prefixEnd_3789631 1297268137452511856656207 := by
  unfold tailWord_3789631
  simp only [CollatzResearch.WordTrace]
  refine ⟨138219197733821579292296747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92146131822547719528197831 138219197733821579292296747)
  ·
    refine ⟨207328796600732368938445121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138219197733821579292296747 207328796600732368938445121)
    ·
      refine ⟨155496597450549276703833841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207328796600732368938445121 155496597450549276703833841)
      ·
        refine ⟨116622448087911957527875381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155496597450549276703833841 116622448087911957527875381)
        ·
          refine ⟨10933354508241746018238317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116622448087911957527875381 10933354508241746018238317)
          ·
            refine ⟨4100007940590654756839369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10933354508241746018238317 4100007940590654756839369)
            ·
              refine ⟨3075005955442991067629527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4100007940590654756839369 3075005955442991067629527)
              ·
                refine ⟨4612508933164486601444291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075005955442991067629527 4612508933164486601444291)
                ·
                  refine ⟨6918763399746729902166437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612508933164486601444291 6918763399746729902166437)
                  ·
                    refine ⟨1297268137452511856656207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6918763399746729902166437 1297268137452511856656207)
                    ·
                      rfl

theorem cell22_3789631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 4].length) (baseStart_3789631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789631 prefixEnd_3789631 := by exact prefixLift 3789631
  have htrace : WordTrace (prefixWord ++ tailWord_3789631) baseStart_3789631 baseEnd_3789631 := by
    simpa [prefixWord, tailWord_3789631, baseEnd_3789631] using wordTrace_append hprefix tailTrace_3789631
  have hstable : (prefixWord ++ tailWord_3789631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789631).length < 2 ^ (prefixWord ++ tailWord_3789631).sum := by decide
  have hdescent : baseEnd_3789631 < baseStart_3789631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789640 : List Nat := [2, 1, 3, 1, 1, 3, 11]
def baseStart_3789640 : Nat := 118140960795 + 3789640 * 2 ^ 59
def prefixEnd_3789640 : Nat := 4983230072969 + 3 ^ 40 * 3789640 * 2
def baseEnd_3789640 : Nat := 48047082160608845673377

theorem tailTrace_3789640 : CollatzResearch.WordTrace tailWord_3789640 prefixEnd_3789640 48047082160608845673377 := by
  unfold tailWord_3789640
  simp only [CollatzResearch.WordTrace]
  refine ⟨69109762995394486914687187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92146350660525982552916249 69109762995394486914687187)
  ·
    refine ⟨103664644493091730372030781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69109762995394486914687187 103664644493091730372030781)
    ·
      refine ⟨38874241684909398889511543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103664644493091730372030781 38874241684909398889511543)
      ·
        refine ⟨58311362527364098334267315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38874241684909398889511543 58311362527364098334267315)
        ·
          refine ⟨87467043791046147501400973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58311362527364098334267315 87467043791046147501400973)
          ·
            refine ⟨32800141421642305313025365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87467043791046147501400973 32800141421642305313025365)
            ·
              refine ⟨48047082160608845673377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32800141421642305313025365 48047082160608845673377)
              ·
                rfl

theorem cell22_3789640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 11].length) (baseStart_3789640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789640 prefixEnd_3789640 := by exact prefixLift 3789640
  have htrace : WordTrace (prefixWord ++ tailWord_3789640) baseStart_3789640 baseEnd_3789640 := by
    simpa [prefixWord, tailWord_3789640, baseEnd_3789640] using wordTrace_append hprefix tailTrace_3789640
  have hstable : (prefixWord ++ tailWord_3789640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789640).length < 2 ^ (prefixWord ++ tailWord_3789640).sum := by decide
  have hdescent : baseEnd_3789640 < baseStart_3789640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789644 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 4, 3]
def baseStart_3789644 : Nat := 118140960795 + 3789644 * 2 ^ 59
def prefixEnd_3789644 : Nat := 4983230072969 + 3 ^ 40 * 3789644 * 2
def baseEnd_3789644 : Nat := 1297272587618184156081167

theorem tailTrace_3789644 : CollatzResearch.WordTrace tailWord_3789644 prefixEnd_3789644 1297272587618184156081167 := by
  unfold tailWord_3789644
  simp only [CollatzResearch.WordTrace]
  refine ⟨69109835941387241256259993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92146447921849655008346657 69109835941387241256259993)
  ·
    refine ⟨51832376956040430942194995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69109835941387241256259993 51832376956040430942194995)
    ·
      refine ⟨77748565434060646413292493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51832376956040430942194995 77748565434060646413292493)
      ·
        refine ⟨29155712037772742404984685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77748565434060646413292493 29155712037772742404984685)
        ·
          refine ⟨10933392014164778401869257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29155712037772742404984685 10933392014164778401869257)
          ·
            refine ⟨8200044010623583801401943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10933392014164778401869257 8200044010623583801401943)
            ·
              refine ⟨12300066015935375702102915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8200044010623583801401943 12300066015935375702102915)
              ·
                refine ⟨18450099023903063553154373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12300066015935375702102915 18450099023903063553154373)
                ·
                  refine ⟨3459393566981824416216445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18450099023903063553154373 3459393566981824416216445)
                  ·
                    refine ⟨1297272587618184156081167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3459393566981824416216445 1297272587618184156081167)
                    ·
                      rfl

theorem cell22_3789644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_3789644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789644 prefixEnd_3789644 := by exact prefixLift 3789644
  have htrace : WordTrace (prefixWord ++ tailWord_3789644) baseStart_3789644 baseEnd_3789644 := by
    simpa [prefixWord, tailWord_3789644, baseEnd_3789644] using wordTrace_append hprefix tailTrace_3789644
  have hstable : (prefixWord ++ tailWord_3789644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789644).length < 2 ^ (prefixWord ++ tailWord_3789644).sum := by decide
  have hdescent : baseEnd_3789644 < baseStart_3789644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789706 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 3, 3]
def baseStart_3789706 : Nat := 118140960795 + 3789706 * 2 ^ 59
def prefixEnd_3789706 : Nat := 4983230072969 + 3 ^ 40 * 3789706 * 2
def baseEnd_3789706 : Nat := 1297293811485236661030977

theorem tailTrace_3789706 : CollatzResearch.WordTrace tailWord_3789706 prefixEnd_3789706 1297293811485236661030977 := by
  unfold tailWord_3789706
  simp only [CollatzResearch.WordTrace]
  refine ⟨34555483302137466775319243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92147955472366578067517981 34555483302137466775319243)
  ·
    refine ⟨51833224953206200162978865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34555483302137466775319243 51833224953206200162978865)
    ·
      refine ⟨38874918714904650122234149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51833224953206200162978865 38874918714904650122234149)
      ·
        refine ⟨7289047259044621897918903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38874918714904650122234149 7289047259044621897918903)
        ·
          refine ⟨10933570888566932846878355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7289047259044621897918903 10933570888566932846878355)
          ·
            refine ⟨16400356332850399270317533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10933570888566932846878355 16400356332850399270317533)
            ·
              refine ⟨6150133624818899726369075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16400356332850399270317533 6150133624818899726369075)
              ·
                refine ⟨9225200437228349589553613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6150133624818899726369075 9225200437228349589553613)
                ·
                  refine ⟨3459450163960631096082605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9225200437228349589553613 3459450163960631096082605)
                  ·
                    refine ⟨1297293811485236661030977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3459450163960631096082605 1297293811485236661030977)
                    ·
                      rfl

theorem cell22_3789706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_3789706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789706 prefixEnd_3789706 := by exact prefixLift 3789706
  have htrace : WordTrace (prefixWord ++ tailWord_3789706) baseStart_3789706 baseEnd_3789706 := by
    simpa [prefixWord, tailWord_3789706, baseEnd_3789706] using wordTrace_append hprefix tailTrace_3789706
  have hstable : (prefixWord ++ tailWord_3789706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789706).length < 2 ^ (prefixWord ++ tailWord_3789706).sum := by decide
  have hdescent : baseEnd_3789706 < baseStart_3789706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789757 : List Nat := [1, 4, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_3789757 : Nat := 118140960795 + 3789757 * 2 ^ 59
def prefixEnd_3789757 : Nat := 4983230072969 + 3 ^ 40 * 3789757 * 2
def baseEnd_3789757 : Nat := 1297311269827489528005821

theorem tailTrace_3789757 : CollatzResearch.WordTrace tailWord_3789757 prefixEnd_3789757 1297311269827489528005821 := by
  unfold tailWord_3789757
  simp only [CollatzResearch.WordTrace]
  refine ⟨138223793331365102811383525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92149195554243401874255683 138223793331365102811383525)
  ·
    refine ⟨25916961249630956777134411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138223793331365102811383525 25916961249630956777134411)
    ·
      refine ⟨38875441874446435165701617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25916961249630956777134411 38875441874446435165701617)
      ·
        refine ⟨29156581405834826374276213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38875441874446435165701617 29156581405834826374276213)
        ·
          refine ⟨2733429506797014972588395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29156581405834826374276213 2733429506797014972588395)
          ·
            refine ⟨4100144260195522458882593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733429506797014972588395 4100144260195522458882593)
            ·
              refine ⟨3075108195146641844161945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4100144260195522458882593 3075108195146641844161945)
              ·
                refine ⟨2306331146359981383121459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075108195146641844161945 2306331146359981383121459)
                ·
                  refine ⟨3459496719539972074682189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306331146359981383121459 3459496719539972074682189)
                  ·
                    refine ⟨1297311269827489528005821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3459496719539972074682189 1297311269827489528005821)
                    ·
                      rfl

theorem cell22_3789757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_3789757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789757 prefixEnd_3789757 := by exact prefixLift 3789757
  have htrace : WordTrace (prefixWord ++ tailWord_3789757) baseStart_3789757 baseEnd_3789757 := by
    simpa [prefixWord, tailWord_3789757, baseEnd_3789757] using wordTrace_append hprefix tailTrace_3789757
  have hstable : (prefixWord ++ tailWord_3789757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789757).length < 2 ^ (prefixWord ++ tailWord_3789757).sum := by decide
  have hdescent : baseEnd_3789757 < baseStart_3789757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789777 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 1, 6]
def baseStart_3789777 : Nat := 118140960795 + 3789777 * 2 ^ 59
def prefixEnd_3789777 : Nat := 4983230072969 + 3 ^ 40 * 3789777 * 2
def baseEnd_3789777 : Nat := 1297318116236216142505759

theorem tailTrace_3789777 : CollatzResearch.WordTrace tailWord_3789777 prefixEnd_3789777 1297318116236216142505759 := by
  unfold tailWord_3789777
  simp only [CollatzResearch.WordTrace]
  refine ⟨138224522791292646227111585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92149681860861764151407723 138224522791292646227111585)
  ·
    refine ⟨103668392093469484670333689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138224522791292646227111585 103668392093469484670333689)
    ·
      refine ⟨77751294070102113502750267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103668392093469484670333689 77751294070102113502750267)
      ·
        refine ⟨116626941105153170254125401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77751294070102113502750267 116626941105153170254125401)
        ·
          refine ⟨87470205828864877690594051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116626941105153170254125401 87470205828864877690594051)
          ·
            refine ⟨131205308743297316535891077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87470205828864877690594051 131205308743297316535891077)
            ·
              refine ⟨24600995389368246850479577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131205308743297316535891077 24600995389368246850479577)
              ·
                refine ⟨18450746542026185137859683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24600995389368246850479577 18450746542026185137859683)
                ·
                  refine ⟨27676119813039277706789525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18450746542026185137859683 27676119813039277706789525)
                  ·
                    refine ⟨1297318116236216142505759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27676119813039277706789525 1297318116236216142505759)
                    ·
                      rfl

theorem cell22_3789777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_3789777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789777 prefixEnd_3789777 := by exact prefixLift 3789777
  have htrace : WordTrace (prefixWord ++ tailWord_3789777) baseStart_3789777 baseEnd_3789777 := by
    simpa [prefixWord, tailWord_3789777, baseEnd_3789777] using wordTrace_append hprefix tailTrace_3789777
  have hstable : (prefixWord ++ tailWord_3789777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789777).length < 2 ^ (prefixWord ++ tailWord_3789777).sum := by decide
  have hdescent : baseEnd_3789777 < baseStart_3789777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789933 : List Nat := [1, 5, 1, 1, 2, 3, 1, 4, 4]
def baseStart_3789933 : Nat := 118140960795 + 3789933 * 2 ^ 59
def prefixEnd_3789933 : Nat := 4983230072969 + 3 ^ 40 * 3789933 * 2
def baseEnd_3789933 : Nat := 432457172741427911868427

theorem tailTrace_3789933 : CollatzResearch.WordTrace tailWord_3789933 prefixEnd_3789933 432457172741427911868427 := by
  unfold tailWord_3789933
  simp only [CollatzResearch.WordTrace]
  refine ⟨138230212578727484869790453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92153475052484989913193635 138230212578727484869790453)
  ·
    refine ⟨12959082429255701706542855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138230212578727484869790453 12959082429255701706542855)
    ·
      refine ⟨19438623643883552559814283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12959082429255701706542855 19438623643883552559814283)
      ·
        refine ⟨29157935465825328839721425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19438623643883552559814283 29157935465825328839721425)
        ·
          refine ⟨21868451599368996629791069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29157935465825328839721425 21868451599368996629791069)
          ·
            refine ⟨8200669349763373736171651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21868451599368996629791069 8200669349763373736171651)
            ·
              refine ⟨12301004024645060604257477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8200669349763373736171651 12301004024645060604257477)
              ·
                refine ⟨2306438254620948863298277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12301004024645060604257477 2306438254620948863298277)
                ·
                  refine ⟨432457172741427911868427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2306438254620948863298277 432457172741427911868427)
                  ·
                    rfl

theorem cell22_3789933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_3789933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789933 prefixEnd_3789933 := by exact prefixLift 3789933
  have htrace : WordTrace (prefixWord ++ tailWord_3789933) baseStart_3789933 baseEnd_3789933 := by
    simpa [prefixWord, tailWord_3789933, baseEnd_3789933] using wordTrace_append hprefix tailTrace_3789933
  have hstable : (prefixWord ++ tailWord_3789933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789933).length < 2 ^ (prefixWord ++ tailWord_3789933).sum := by decide
  have hdescent : baseEnd_3789933 < baseStart_3789933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789944 : List Nat := [2, 1, 2, 1, 1, 1, 7, 7]
def baseStart_3789944 : Nat := 118140960795 + 3789944 * 2 ^ 59
def prefixEnd_3789944 : Nat := 4983230072969 + 3 ^ 40 * 3789944 * 2
def baseEnd_3789944 : Nat := 144152809305453708175583

theorem tailTrace_3789944 : CollatzResearch.WordTrace tailWord_3789944 prefixEnd_3789944 144152809305453708175583 := by
  unfold tailWord_3789944
  simp only [CollatzResearch.WordTrace]
  refine ⟨69115306890843816874220443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92153742521125089165627257 69115306890843816874220443)
  ·
    refine ⟨103672960336265725311330665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69115306890843816874220443 103672960336265725311330665)
    ·
      refine ⟨77754720252199293983497999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103672960336265725311330665 77754720252199293983497999)
      ·
        refine ⟨116632080378298940975246999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77754720252199293983497999 116632080378298940975246999)
        ·
          refine ⟨174948120567448411462870499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116632080378298940975246999 174948120567448411462870499)
          ·
            refine ⟨262422180851172617194305749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174948120567448411462870499 262422180851172617194305749)
            ·
              refine ⟨6150519863699358215491541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 262422180851172617194305749 6150519863699358215491541)
              ·
                refine ⟨144152809305453708175583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6150519863699358215491541 144152809305453708175583)
                ·
                  rfl

theorem cell22_3789944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 7].length) (baseStart_3789944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789944 prefixEnd_3789944 := by exact prefixLift 3789944
  have htrace : WordTrace (prefixWord ++ tailWord_3789944) baseStart_3789944 baseEnd_3789944 := by
    simpa [prefixWord, tailWord_3789944, baseEnd_3789944] using wordTrace_append hprefix tailTrace_3789944
  have hstable : (prefixWord ++ tailWord_3789944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789944).length < 2 ^ (prefixWord ++ tailWord_3789944).sum := by decide
  have hdescent : baseEnd_3789944 < baseStart_3789944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789961 : List Nat := [1, 2, 1, 1, 4, 4, 3, 6]
def baseStart_3789961 : Nat := 118140960795 + 3789961 * 2 ^ 59
def prefixEnd_3789961 : Nat := 4983230072969 + 3 ^ 40 * 3789961 * 2
def baseEnd_3789961 : Nat := 144153455910722332878355

theorem tailTrace_3789961 : CollatzResearch.WordTrace tailWord_3789961 prefixEnd_3789961 144153455910722332878355 := by
  unfold tailWord_3789961
  simp only [CollatzResearch.WordTrace]
  refine ⟨138231233822626045651809737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92154155881750697101206491 138231233822626045651809737)
  ·
    refine ⟨103673425366969534238857303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138231233822626045651809737 103673425366969534238857303)
    ·
      refine ⟨155510138050454301358285955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103673425366969534238857303 155510138050454301358285955)
      ·
        refine ⟨233265207075681452037428933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155510138050454301358285955 233265207075681452037428933)
        ·
          refine ⟨43737226326690272257017925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233265207075681452037428933 43737226326690272257017925)
          ·
            refine ⟨8200729936254426048190861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43737226326690272257017925 8200729936254426048190861)
            ·
              refine ⟨3075273726095409768071573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8200729936254426048190861 3075273726095409768071573)
              ·
                refine ⟨144153455910722332878355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3075273726095409768071573 144153455910722332878355)
                ·
                  rfl

theorem cell22_3789961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 6].length) (baseStart_3789961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789961 prefixEnd_3789961 := by exact prefixLift 3789961
  have htrace : WordTrace (prefixWord ++ tailWord_3789961) baseStart_3789961 baseEnd_3789961 := by
    simpa [prefixWord, tailWord_3789961, baseEnd_3789961] using wordTrace_append hprefix tailTrace_3789961
  have hstable : (prefixWord ++ tailWord_3789961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789961).length < 2 ^ (prefixWord ++ tailWord_3789961).sum := by decide
  have hdescent : baseEnd_3789961 < baseStart_3789961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789982 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3789982 : Nat := 118140960795 + 3789982 * 2 ^ 59
def prefixEnd_3789982 : Nat := 4983230072969 + 3 ^ 40 * 3789982 * 2
def baseEnd_3789982 : Nat := 1297388291925663941130131

theorem tailTrace_3789982 : CollatzResearch.WordTrace tailWord_3789982 prefixEnd_3789982 1297388291925663941130131 := by
  unfold tailWord_3789982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17278999969443745779790525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92154666503699977492216133 17278999969443745779790525)
  ·
    refine ⟨6479624988541404667421447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17278999969443745779790525 6479624988541404667421447)
    ·
      refine ⟨9719437482812107001132171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6479624988541404667421447 9719437482812107001132171)
      ·
        refine ⟨14579156224218160501698257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9719437482812107001132171 14579156224218160501698257)
        ·
          refine ⟨10934367168163620376273693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14579156224218160501698257 10934367168163620376273693)
          ·
            refine ⟨4100387688061357641102635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10934367168163620376273693 4100387688061357641102635)
            ·
              refine ⟨6150581532092036461653953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100387688061357641102635 6150581532092036461653953)
              ·
                refine ⟨4612936149069027346240465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6150581532092036461653953 4612936149069027346240465)
                ·
                  refine ⟨3459702111801770509680349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4612936149069027346240465 3459702111801770509680349)
                  ·
                    refine ⟨1297388291925663941130131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3459702111801770509680349 1297388291925663941130131)
                    ·
                      rfl

theorem cell22_3789982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3789982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789982 prefixEnd_3789982 := by exact prefixLift 3789982
  have htrace : WordTrace (prefixWord ++ tailWord_3789982) baseStart_3789982 baseEnd_3789982 := by
    simpa [prefixWord, tailWord_3789982, baseEnd_3789982] using wordTrace_append hprefix tailTrace_3789982
  have hstable : (prefixWord ++ tailWord_3789982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789982).length < 2 ^ (prefixWord ++ tailWord_3789982).sum := by decide
  have hdescent : baseEnd_3789982 < baseStart_3789982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790128 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 3, 3]
def baseStart_3790128 : Nat := 118140960795 + 3790128 * 2 ^ 59
def prefixEnd_3790128 : Nat := 4983230072969 + 3 ^ 40 * 3790128 * 2
def baseEnd_3790128 : Nat := 1297438270709368226979683

theorem tailTrace_3790128 : CollatzResearch.WordTrace tailWord_3790128 prefixEnd_3790128 1297438270709368226979683 := by
  unfold tailWord_3790128
  simp only [CollatzResearch.WordTrace]
  refine ⟨69118662406510516586569519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92158216542014022115426025 69118662406510516586569519)
  ·
    refine ⟨103677993609765774879854279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69118662406510516586569519 103677993609765774879854279)
    ·
      refine ⟨155516990414648662319781419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103677993609765774879854279 155516990414648662319781419)
      ·
        refine ⟨233275485621972993479672129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155516990414648662319781419 233275485621972993479672129)
        ·
          refine ⟨174956614216479745109754097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233275485621972993479672129 174956614216479745109754097)
          ·
            refine ⟨131217460662359808832315573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174956614216479745109754097 131217460662359808832315573)
            ·
              refine ⟨12301636937096232078029585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131217460662359808832315573 12301636937096232078029585)
              ·
                refine ⟨9226227702822174058522189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12301636937096232078029585 9226227702822174058522189)
                ·
                  refine ⟨3459835388558315271945821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9226227702822174058522189 3459835388558315271945821)
                  ·
                    refine ⟨1297438270709368226979683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3459835388558315271945821 1297438270709368226979683)
                    ·
                      rfl

theorem cell22_3790128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 3, 3].length) (baseStart_3790128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790128 prefixEnd_3790128 := by exact prefixLift 3790128
  have htrace : WordTrace (prefixWord ++ tailWord_3790128) baseStart_3790128 baseEnd_3790128 := by
    simpa [prefixWord, tailWord_3790128, baseEnd_3790128] using wordTrace_append hprefix tailTrace_3790128
  have hstable : (prefixWord ++ tailWord_3790128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790128).length < 2 ^ (prefixWord ++ tailWord_3790128).sum := by decide
  have hdescent : baseEnd_3790128 < baseStart_3790128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790226 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 5]
def baseStart_3790226 : Nat := 118140960795 + 3790226 * 2 ^ 59
def prefixEnd_3790226 : Nat := 4983230072969 + 3 ^ 40 * 3790226 * 2
def baseEnd_3790226 : Nat := 432490606037376212676461

theorem tailTrace_3790226 : CollatzResearch.WordTrace tailWord_3790226 prefixEnd_3790226 432490606037376212676461 := by
  unfold tailWord_3790226
  simp only [CollatzResearch.WordTrace]
  refine ⟨34560224791666498977551633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92160599444443997273471021 34560224791666498977551633)
  ·
    refine ⟨25920168593749874233163725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34560224791666498977551633 25920168593749874233163725)
    ·
      refine ⟨9720063222656202837436397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25920168593749874233163725 9720063222656202837436397)
      ·
        refine ⟨3645023708496076064038649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9720063222656202837436397 3645023708496076064038649)
        ·
          refine ⟨2733767781372057048028987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3645023708496076064038649 2733767781372057048028987)
          ·
            refine ⟨4100651672058085572043481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733767781372057048028987 4100651672058085572043481)
            ·
              refine ⟨3075488754043564179032611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4100651672058085572043481 3075488754043564179032611)
              ·
                refine ⟨4613233131065346268548917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075488754043564179032611 4613233131065346268548917)
                ·
                  refine ⟨432490606037376212676461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4613233131065346268548917 432490606037376212676461)
                  ·
                    rfl

theorem cell22_3790226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_3790226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790226 prefixEnd_3790226 := by exact prefixLift 3790226
  have htrace : WordTrace (prefixWord ++ tailWord_3790226) baseStart_3790226 baseEnd_3790226 := by
    simpa [prefixWord, tailWord_3790226, baseEnd_3790226] using wordTrace_append hprefix tailTrace_3790226
  have hstable : (prefixWord ++ tailWord_3790226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790226).length < 2 ^ (prefixWord ++ tailWord_3790226).sum := by decide
  have hdescent : baseEnd_3790226 < baseStart_3790226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790280 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 3, 3]
def baseStart_3790280 : Nat := 118140960795 + 3790280 * 2 ^ 59
def prefixEnd_3790280 : Nat := 4983230072969 + 3 ^ 40 * 3790280 * 2
def baseEnd_3790280 : Nat := 1297490303415690497179217

theorem tailTrace_3790280 : CollatzResearch.WordTrace tailWord_3790280 prefixEnd_3790280 1297490303415690497179217 := by
  unfold tailWord_3790280
  simp only [CollatzResearch.WordTrace]
  refine ⟨69121434354235181566336147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92161912472313575421781529 69121434354235181566336147)
  ·
    refine ⟨103682151531352772349504221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69121434354235181566336147 103682151531352772349504221)
    ·
      refine ⟨38880806824257289631064083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103682151531352772349504221 38880806824257289631064083)
      ·
        refine ⟨58321210236385934446596125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38880806824257289631064083 58321210236385934446596125)
        ·
          refine ⟨21870453838644725417473547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58321210236385934446596125 21870453838644725417473547)
          ·
            refine ⟨32805680757967088126210321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21870453838644725417473547 32805680757967088126210321)
            ·
              refine ⟨24604260568475316094657741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32805680757967088126210321 24604260568475316094657741)
              ·
                refine ⟨9226597713178243535496653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24604260568475316094657741 9226597713178243535496653)
                ·
                  refine ⟨3459974142441841325811245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9226597713178243535496653 3459974142441841325811245)
                  ·
                    refine ⟨1297490303415690497179217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3459974142441841325811245 1297490303415690497179217)
                    ·
                      rfl

theorem cell22_3790280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_3790280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790280 prefixEnd_3790280 := by exact prefixLift 3790280
  have htrace : WordTrace (prefixWord ++ tailWord_3790280) baseStart_3790280 baseEnd_3790280 := by
    simpa [prefixWord, tailWord_3790280, baseEnd_3790280] using wordTrace_append hprefix tailTrace_3790280
  have hstable : (prefixWord ++ tailWord_3790280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790280).length < 2 ^ (prefixWord ++ tailWord_3790280).sum := by decide
  have hdescent : baseEnd_3790280 < baseStart_3790280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790323 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 5, 4]
def baseStart_3790323 : Nat := 118140960795 + 3790323 * 2 ^ 59
def prefixEnd_3790323 : Nat := 4983230072969 + 3 ^ 40 * 3790323 * 2
def baseEnd_3790323 : Nat := 1297505023194452718354085

theorem tailTrace_3790323 : CollatzResearch.WordTrace tailWord_3790323 prefixEnd_3790323 1297505023194452718354085 := by
  unfold tailWord_3790323
  simp only [CollatzResearch.WordTrace]
  refine ⟨138244437047314581476487623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92162958031543054317658415 138244437047314581476487623)
  ·
    refine ⟨207366655570971872214731435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138244437047314581476487623 207366655570971872214731435)
    ·
      refine ⟨311049983356457808322097153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207366655570971872214731435 311049983356457808322097153)
      ·
        refine ⟨233287487517343356241572865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311049983356457808322097153 233287487517343356241572865)
        ·
          refine ⟨174965615638007517181179649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233287487517343356241572865 174965615638007517181179649)
          ·
            refine ⟨131224211728505637885884737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174965615638007517181179649 131224211728505637885884737)
            ·
              refine ⟨98418158796379228414413553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131224211728505637885884737 98418158796379228414413553)
              ·
                refine ⟨73813619097284421310810165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98418158796379228414413553 73813619097284421310810165)
                ·
                  refine ⟨6920026790370414497888453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73813619097284421310810165 6920026790370414497888453)
                  ·
                    refine ⟨1297505023194452718354085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6920026790370414497888453 1297505023194452718354085)
                    ·
                      rfl

theorem cell22_3790323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 4].length) (baseStart_3790323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790323 prefixEnd_3790323 := by exact prefixLift 3790323
  have htrace : WordTrace (prefixWord ++ tailWord_3790323) baseStart_3790323 baseEnd_3790323 := by
    simpa [prefixWord, tailWord_3790323, baseEnd_3790323] using wordTrace_append hprefix tailTrace_3790323
  have hstable : (prefixWord ++ tailWord_3790323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790323).length < 2 ^ (prefixWord ++ tailWord_3790323).sum := by decide
  have hdescent : baseEnd_3790323 < baseStart_3790323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790357 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_3790357 : Nat := 118140960795 + 3790357 * 2 ^ 59
def prefixEnd_3790357 : Nat := 4983230072969 + 3 ^ 40 * 3790357 * 2
def baseEnd_3790357 : Nat := 1297516662089287963003981

theorem tailTrace_3790357 : CollatzResearch.WordTrace tailWord_3790357 prefixEnd_3790357 1297516662089287963003981 := by
  unfold tailWord_3790357
  simp only [CollatzResearch.WordTrace]
  refine ⟨138245677129191405283225325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92163784752794270188816883 138245677129191405283225325)
  ·
    refine ⟨51842128923446776981209497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138245677129191405283225325 51842128923446776981209497)
    ·
      refine ⟨38881596692585082735907123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51842128923446776981209497 38881596692585082735907123)
      ·
        refine ⟨58322395038877624103860685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38881596692585082735907123 58322395038877624103860685)
        ·
          refine ⟨21870898139579109038947757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58322395038877624103860685 21870898139579109038947757)
          ·
            refine ⟨8201586802342165889605409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21870898139579109038947757 8201586802342165889605409)
            ·
              refine ⟨6151190101756624417204057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8201586802342165889605409 6151190101756624417204057)
              ·
                refine ⟨4613392576317468312903043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6151190101756624417204057 4613392576317468312903043)
                ·
                  refine ⟨6920088864476202469354565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4613392576317468312903043 6920088864476202469354565)
                  ·
                    refine ⟨1297516662089287963003981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6920088864476202469354565 1297516662089287963003981)
                    ·
                      rfl

theorem cell22_3790357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_3790357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790357 prefixEnd_3790357 := by exact prefixLift 3790357
  have htrace : WordTrace (prefixWord ++ tailWord_3790357) baseStart_3790357 baseEnd_3790357 := by
    simpa [prefixWord, tailWord_3790357, baseEnd_3790357] using wordTrace_append hprefix tailTrace_3790357
  have hstable : (prefixWord ++ tailWord_3790357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790357).length < 2 ^ (prefixWord ++ tailWord_3790357).sum := by decide
  have hdescent : baseEnd_3790357 < baseStart_3790357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790370 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3790370 : Nat := 118140960795 + 3790370 * 2 ^ 59
def prefixEnd_3790370 : Nat := 4983230072969 + 3 ^ 40 * 3790370 * 2
def baseEnd_3790370 : Nat := 1297521112254960262428941

theorem tailTrace_3790370 : CollatzResearch.WordTrace tailWord_3790370 prefixEnd_3790370 1297521112254960262428941 := by
  unfold tailWord_3790370
  simp only [CollatzResearch.WordTrace]
  refine ⟨34561537819536077125862141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92164100852096205668965709 34561537819536077125862141)
  ·
    refine ⟨12960576682326028922198303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34561537819536077125862141 12960576682326028922198303)
    ·
      refine ⟨19440865023489043383297455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12960576682326028922198303 19440865023489043383297455)
      ·
        refine ⟨29161297535233565074946183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19440865023489043383297455 29161297535233565074946183)
        ·
          refine ⟨43741946302850347612419275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29161297535233565074946183 43741946302850347612419275)
          ·
            refine ⟨65612919454275521418628913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43741946302850347612419275 65612919454275521418628913)
            ·
              refine ⟨49209689590706641063971685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65612919454275521418628913 49209689590706641063971685)
              ·
                refine ⟨9226816798257495199494691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49209689590706641063971685 9226816798257495199494691)
                ·
                  refine ⟨13840225197386242799242037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9226816798257495199494691 13840225197386242799242037)
                  ·
                    refine ⟨1297521112254960262428941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13840225197386242799242037 1297521112254960262428941)
                    ·
                      rfl

theorem cell22_3790370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3790370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790370 prefixEnd_3790370 := by exact prefixLift 3790370
  have htrace : WordTrace (prefixWord ++ tailWord_3790370) baseStart_3790370 baseEnd_3790370 := by
    simpa [prefixWord, tailWord_3790370, baseEnd_3790370] using wordTrace_append hprefix tailTrace_3790370
  have hstable : (prefixWord ++ tailWord_3790370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790370).length < 2 ^ (prefixWord ++ tailWord_3790370).sum := by decide
  have hdescent : baseEnd_3790370 < baseStart_3790370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790389 : List Nat := [1, 3, 3, 1, 1, 4, 3, 2, 4]
def baseStart_3790389 : Nat := 118140960795 + 3790389 * 2 ^ 59
def prefixEnd_3790389 : Nat := 4983230072969 + 3 ^ 40 * 3790389 * 2
def baseEnd_3790389 : Nat := 432509205447750182067961

theorem tailTrace_3790389 : CollatzResearch.WordTrace tailWord_3790389 prefixEnd_3790389 432509205447750182067961 := by
  unfold tailWord_3790389
  simp only [CollatzResearch.WordTrace]
  refine ⟨138246844265075474748390221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92164562843383649832260147 138246844265075474748390221)
  ·
    refine ⟨51842566599403303030646333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138246844265075474748390221 51842566599403303030646333)
    ·
      refine ⟨19440962474776238636492375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51842566599403303030646333 19440962474776238636492375)
      ·
        refine ⟨29161443712164357954738563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19440962474776238636492375 29161443712164357954738563)
        ·
          refine ⟨43742165568246536932107845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29161443712164357954738563 43742165568246536932107845)
          ·
            refine ⟨8201656044046225674770221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43742165568246536932107845 8201656044046225674770221)
            ·
              refine ⟨3075621016517334628038833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8201656044046225674770221 3075621016517334628038833)
              ·
                refine ⟨2306715762388000971029125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075621016517334628038833 2306715762388000971029125)
                ·
                  refine ⟨432509205447750182067961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2306715762388000971029125 432509205447750182067961)
                  ·
                    rfl

theorem cell22_3790389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_3790389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790389 prefixEnd_3790389 := by exact prefixLift 3790389
  have htrace : WordTrace (prefixWord ++ tailWord_3790389) baseStart_3790389 baseEnd_3790389 := by
    simpa [prefixWord, tailWord_3790389, baseEnd_3790389] using wordTrace_append hprefix tailTrace_3790389
  have hstable : (prefixWord ++ tailWord_3790389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790389).length < 2 ^ (prefixWord ++ tailWord_3790389).sum := by decide
  have hdescent : baseEnd_3790389 < baseStart_3790389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790415 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 5, 3]
def baseStart_3790415 : Nat := 118140960795 + 3790415 * 2 ^ 59
def prefixEnd_3790415 : Nat := 4983230072969 + 3 ^ 40 * 3790415 * 2
def baseEnd_3790415 : Nat := 1297536516674595145053803

theorem tailTrace_3790415 : CollatzResearch.WordTrace tailWord_3790415 prefixEnd_3790415 1297536516674595145053803 := by
  unfold tailWord_3790415
  simp only [CollatzResearch.WordTrace]
  refine ⟨138247792562981281188836699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92165195041987520792557799 138247792562981281188836699)
  ·
    refine ⟨207371688844471921783255049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138247792562981281188836699 207371688844471921783255049)
    ·
      refine ⟨155528766633353941337441287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207371688844471921783255049 155528766633353941337441287)
      ·
        refine ⟨233293149950030912006161931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155528766633353941337441287 233293149950030912006161931)
        ·
          refine ⟨349939724925046368009242897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233293149950030912006161931 349939724925046368009242897)
          ·
            refine ⟨262454793693784776006932173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349939724925046368009242897 262454793693784776006932173)
            ·
              refine ⟨98420547635169291002599565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262454793693784776006932173 98420547635169291002599565)
              ·
                refine ⟨36907705363188484125974837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98420547635169291002599565 36907705363188484125974837)
                ·
                  refine ⟨3460097377798920386810141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36907705363188484125974837 3460097377798920386810141)
                  ·
                    refine ⟨1297536516674595145053803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3460097377798920386810141 1297536516674595145053803)
                    ·
                      rfl

theorem cell22_3790415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 3].length) (baseStart_3790415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790415 prefixEnd_3790415 := by exact prefixLift 3790415
  have htrace : WordTrace (prefixWord ++ tailWord_3790415) baseStart_3790415 baseEnd_3790415 := by
    simpa [prefixWord, tailWord_3790415, baseEnd_3790415] using wordTrace_append hprefix tailTrace_3790415
  have hstable : (prefixWord ++ tailWord_3790415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790415).length < 2 ^ (prefixWord ++ tailWord_3790415).sum := by decide
  have hdescent : baseEnd_3790415 < baseStart_3790415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790475 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 3, 4]
def baseStart_3790475 : Nat := 118140960795 + 3790475 * 2 ^ 59
def prefixEnd_3790475 : Nat := 4983230072969 + 3 ^ 40 * 3790475 * 2
def baseEnd_3790475 : Nat := 1297557055900774988553619

theorem tailTrace_3790475 : CollatzResearch.WordTrace tailWord_3790475 prefixEnd_3790475 1297557055900774988553619 := by
  unfold tailWord_3790475
  simp only [CollatzResearch.WordTrace]
  refine ⟨138249980942763911436020879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92166653961842607624013919 138249980942763911436020879)
  ·
    refine ⟨207374971414145867154031319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138249980942763911436020879 207374971414145867154031319)
    ·
      refine ⟨311062457121218800731046979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207374971414145867154031319 311062457121218800731046979)
      ·
        refine ⟨466593685681828201096570469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311062457121218800731046979 466593685681828201096570469)
        ·
          refine ⟨87486316065342787705606963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466593685681828201096570469 87486316065342787705606963)
          ·
            refine ⟨131229474098014181558410445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87486316065342787705606963 131229474098014181558410445)
            ·
              refine ⟨49211052786755318084403917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131229474098014181558410445 49211052786755318084403917)
              ·
                refine ⟨18454144795033244281651469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49211052786755318084403917 18454144795033244281651469)
                ·
                  refine ⟨6920304298137466605619301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18454144795033244281651469 6920304298137466605619301)
                  ·
                    refine ⟨1297557055900774988553619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6920304298137466605619301 1297557055900774988553619)
                    ·
                      rfl

theorem cell22_3790475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 4].length) (baseStart_3790475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790475 prefixEnd_3790475 := by exact prefixLift 3790475
  have htrace : WordTrace (prefixWord ++ tailWord_3790475) baseStart_3790475 baseEnd_3790475 := by
    simpa [prefixWord, tailWord_3790475, baseEnd_3790475] using wordTrace_append hprefix tailTrace_3790475
  have hstable : (prefixWord ++ tailWord_3790475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790475).length < 2 ^ (prefixWord ++ tailWord_3790475).sum := by decide
  have hdescent : baseEnd_3790475 < baseStart_3790475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790522 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_3790522 : Nat := 118140960795 + 3790522 * 2 ^ 59
def prefixEnd_3790522 : Nat := 4983230072969 + 3 ^ 40 * 3790522 * 2
def baseEnd_3790522 : Nat := 1297573144961282532628475

theorem tailTrace_3790522 : CollatzResearch.WordTrace tailWord_3790522 prefixEnd_3790522 1297573144961282532628475 := by
  unfold tailWord_3790522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34562923793398409615745455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92167796782395758975321213 34562923793398409615745455)
  ·
    refine ⟨51844385690097614423618183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34562923793398409615745455 51844385690097614423618183)
    ·
      refine ⟨77766578535146421635427275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51844385690097614423618183 77766578535146421635427275)
      ·
        refine ⟨116649867802719632453140913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77766578535146421635427275 116649867802719632453140913)
        ·
          refine ⟨87487400852039724339855685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116649867802719632453140913 87487400852039724339855685)
          ·
            refine ⟨16403887659757448313722941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87487400852039724339855685 16403887659757448313722941)
            ·
              refine ⟨6151457872409043117646103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16403887659757448313722941 6151457872409043117646103)
              ·
                refine ⟨9227186808613564676469155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6151457872409043117646103 9227186808613564676469155)
                ·
                  refine ⟨13840780212920347014703733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9227186808613564676469155 13840780212920347014703733)
                  ·
                    refine ⟨1297573144961282532628475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13840780212920347014703733 1297573144961282532628475)
                    ·
                      rfl

theorem cell22_3790522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_3790522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790522 prefixEnd_3790522 := by exact prefixLift 3790522
  have htrace : WordTrace (prefixWord ++ tailWord_3790522) baseStart_3790522 baseEnd_3790522 := by
    simpa [prefixWord, tailWord_3790522, baseEnd_3790522] using wordTrace_append hprefix tailTrace_3790522
  have hstable : (prefixWord ++ tailWord_3790522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790522).length < 2 ^ (prefixWord ++ tailWord_3790522).sum := by decide
  have hdescent : baseEnd_3790522 < baseStart_3790522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790535 : List Nat := [1, 1, 4, 1, 1, 1, 5, 8]
def baseStart_3790535 : Nat := 118140960795 + 3790535 * 2 ^ 59
def prefixEnd_3790535 : Nat := 4983230072969 + 3 ^ 40 * 3790535 * 2
def baseEnd_3790535 : Nat := 144175288347439425783715

theorem tailTrace_3790535 : CollatzResearch.WordTrace tailWord_3790535 prefixEnd_3790535 144175288347439425783715 := by
  unfold tailWord_3790535
  simp only [CollatzResearch.WordTrace]
  refine ⟨138252169322546541683205059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92168112881697694455470039 138252169322546541683205059)
  ·
    refine ⟨207378253983819812524807589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138252169322546541683205059 207378253983819812524807589)
    ·
      refine ⟨38883422621966214848401423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207378253983819812524807589 38883422621966214848401423)
      ·
        refine ⟨58325133932949322272602135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38883422621966214848401423 58325133932949322272602135)
        ·
          refine ⟨87487700899423983408903203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58325133932949322272602135 87487700899423983408903203)
          ·
            refine ⟨131231551349135975113354805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87487700899423983408903203 131231551349135975113354805)
            ·
              refine ⟨12302957938981497666877013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131231551349135975113354805 12302957938981497666877013)
              ·
                refine ⟨144175288347439425783715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12302957938981497666877013 144175288347439425783715)
                ·
                  rfl

theorem cell22_3790535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 8].length) (baseStart_3790535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790535 prefixEnd_3790535 := by exact prefixLift 3790535
  have htrace : WordTrace (prefixWord ++ tailWord_3790535) baseStart_3790535 baseEnd_3790535 := by
    simpa [prefixWord, tailWord_3790535, baseEnd_3790535] using wordTrace_append hprefix tailTrace_3790535
  have hstable : (prefixWord ++ tailWord_3790535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790535).length < 2 ^ (prefixWord ++ tailWord_3790535).sum := by decide
  have hdescent : baseEnd_3790535 < baseStart_3790535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790573 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_3790573 : Nat := 118140960795 + 3790573 * 2 ^ 59
def prefixEnd_3790573 : Nat := 4983230072969 + 3 ^ 40 * 3790573 * 2
def baseEnd_3790573 : Nat := 1297590603303535399603319

theorem tailTrace_3790573 : CollatzResearch.WordTrace tailWord_3790573 prefixEnd_3790573 1297590603303535399603319 := by
  unfold tailWord_3790573
  simp only [CollatzResearch.WordTrace]
  refine ⟨138253555296408874173088373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92169036864272582782058915 138253555296408874173088373)
  ·
    refine ⟨12961270809038331953727035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138253555296408874173088373 12961270809038331953727035)
    ·
      refine ⟨19441906213557497930590553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12961270809038331953727035 19441906213557497930590553)
      ·
        refine ⟨14581429660168123447942915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19441906213557497930590553 14581429660168123447942915)
        ·
          refine ⟨21872144490252185171914373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14581429660168123447942915 21872144490252185171914373)
          ·
            refine ⟨4101027091922284719733945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21872144490252185171914373 4101027091922284719733945)
            ·
              refine ⟨3075770318941713539800459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4101027091922284719733945 3075770318941713539800459)
              ·
                refine ⟨4613655478412570309700689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075770318941713539800459 4613655478412570309700689)
                ·
                  refine ⟨3460241608809427732275517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4613655478412570309700689 3460241608809427732275517)
                  ·
                    refine ⟨1297590603303535399603319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3460241608809427732275517 1297590603303535399603319)
                    ·
                      rfl

theorem cell22_3790573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_3790573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790573 prefixEnd_3790573 := by exact prefixLift 3790573
  have htrace : WordTrace (prefixWord ++ tailWord_3790573) baseStart_3790573 baseEnd_3790573 := by
    simpa [prefixWord, tailWord_3790573, baseEnd_3790573] using wordTrace_append hprefix tailTrace_3790573
  have hstable : (prefixWord ++ tailWord_3790573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790573).length < 2 ^ (prefixWord ++ tailWord_3790573).sum := by decide
  have hdescent : baseEnd_3790573 < baseStart_3790573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790618 : List Nat := [3, 1, 1, 3, 2, 2, 4, 2, 1, 3]
def baseStart_3790618 : Nat := 118140960795 + 3790618 * 2 ^ 59
def prefixEnd_3790618 : Nat := 4983230072969 + 3 ^ 40 * 3790618 * 2
def baseEnd_3790618 : Nat := 1297606007723170282228181

theorem tailTrace_3790618 : CollatzResearch.WordTrace tailWord_3790618 prefixEnd_3790618 1297606007723170282228181 := by
  unfold tailWord_3790618
  simp only [CollatzResearch.WordTrace]
  refine ⟨34563799145311461714619127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92170131054163897905651005 34563799145311461714619127)
  ·
    refine ⟨51845698717967192571928691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34563799145311461714619127 51845698717967192571928691)
    ·
      refine ⟨77768548076950788857893037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51845698717967192571928691 77768548076950788857893037)
      ·
        refine ⟨29163205528856545821709889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77768548076950788857893037 29163205528856545821709889)
        ·
          refine ⟨21872404146642409366282417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29163205528856545821709889 21872404146642409366282417)
          ·
            refine ⟨16404303109981807024711813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21872404146642409366282417 16404303109981807024711813)
            ·
              refine ⟨3075806833121588817133465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16404303109981807024711813 3075806833121588817133465)
              ·
                refine ⟨2306855124841191612850099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075806833121588817133465 2306855124841191612850099)
                ·
                  refine ⟨3460282687261787419275149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306855124841191612850099 3460282687261787419275149)
                  ·
                    refine ⟨1297606007723170282228181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3460282687261787419275149 1297606007723170282228181)
                    ·
                      rfl

theorem cell22_3790618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_3790618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790618 prefixEnd_3790618 := by exact prefixLift 3790618
  have htrace : WordTrace (prefixWord ++ tailWord_3790618) baseStart_3790618 baseEnd_3790618 := by
    simpa [prefixWord, tailWord_3790618, baseEnd_3790618] using wordTrace_append hprefix tailTrace_3790618
  have hstable : (prefixWord ++ tailWord_3790618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790618).length < 2 ^ (prefixWord ++ tailWord_3790618).sum := by decide
  have hdescent : baseEnd_3790618 < baseStart_3790618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790627 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 3, 4]
def baseStart_3790627 : Nat := 118140960795 + 3790627 * 2 ^ 59
def prefixEnd_3790627 : Nat := 4983230072969 + 3 ^ 40 * 3790627 * 2
def baseEnd_3790627 : Nat := 1297609088607097258753153

theorem tailTrace_3790627 : CollatzResearch.WordTrace tailWord_3790627 prefixEnd_3790627 1297609088607097258753153 := by
  unfold tailWord_3790627
  simp only [CollatzResearch.WordTrace]
  refine ⟨138255524838213241395554135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92170349892142160930369423 138255524838213241395554135)
  ·
    refine ⟨207383287257319862093331203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138255524838213241395554135 207383287257319862093331203)
    ·
      refine ⟨311074930885979793139996805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207383287257319862093331203 311074930885979793139996805)
      ·
        refine ⟨58326549541121211213749401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311074930885979793139996805 58326549541121211213749401)
        ·
          refine ⟨43744912155840908410312051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58326549541121211213749401 43744912155840908410312051)
          ·
            refine ⟨65617368233761362615468077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43744912155840908410312051 65617368233761362615468077)
            ·
              refine ⟨24606513087660510980800529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65617368233761362615468077 24606513087660510980800529)
              ·
                refine ⟨18454884815745383235600397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24606513087660510980800529 18454884815745383235600397)
                ·
                  refine ⟨6920581805904518713350149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18454884815745383235600397 6920581805904518713350149)
                  ·
                    refine ⟨1297609088607097258753153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6920581805904518713350149 1297609088607097258753153)
                    ·
                      rfl

theorem cell22_3790627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 4].length) (baseStart_3790627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790627 prefixEnd_3790627 := by exact prefixLift 3790627
  have htrace : WordTrace (prefixWord ++ tailWord_3790627) baseStart_3790627 baseEnd_3790627 := by
    simpa [prefixWord, tailWord_3790627, baseEnd_3790627] using wordTrace_append hprefix tailTrace_3790627
  have hstable : (prefixWord ++ tailWord_3790627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790627).length < 2 ^ (prefixWord ++ tailWord_3790627).sum := by decide
  have hdescent : baseEnd_3790627 < baseStart_3790627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790642 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_3790642 : Nat := 118140960795 + 3790642 * 2 ^ 59
def prefixEnd_3790642 : Nat := 4983230072969 + 3 ^ 40 * 3790642 * 2
def baseEnd_3790642 : Nat := 432538074471214073209369

theorem tailTrace_3790642 : CollatzResearch.WordTrace tailWord_3790642 prefixEnd_3790642 432538074471214073209369 := by
  unfold tailWord_3790642
  simp only [CollatzResearch.WordTrace]
  refine ⟨34564017983289724739337545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92170714622105932638233453 34564017983289724739337545)
  ·
    refine ⟨25923013487467293554503159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34564017983289724739337545 25923013487467293554503159)
    ·
      refine ⟨38884520231200940331754739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25923013487467293554503159 38884520231200940331754739)
      ·
        refine ⟨58326780346801410497632109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38884520231200940331754739 58326780346801410497632109)
        ·
          refine ⟨21872542630050528936612041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58326780346801410497632109 21872542630050528936612041)
          ·
            refine ⟨16404406972537896702459031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21872542630050528936612041 16404406972537896702459031)
            ·
              refine ⟨24606610458806845053688547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16404406972537896702459031 24606610458806845053688547)
              ·
                refine ⟨36909915688210267580532821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24606610458806845053688547 36909915688210267580532821)
                ·
                  refine ⟨432538074471214073209369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36909915688210267580532821 432538074471214073209369)
                  ·
                    rfl

theorem cell22_3790642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_3790642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790642 prefixEnd_3790642 := by exact prefixLift 3790642
  have htrace : WordTrace (prefixWord ++ tailWord_3790642) baseStart_3790642 baseEnd_3790642 := by
    simpa [prefixWord, tailWord_3790642, baseEnd_3790642] using wordTrace_append hprefix tailTrace_3790642
  have hstable : (prefixWord ++ tailWord_3790642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790642).length < 2 ^ (prefixWord ++ tailWord_3790642).sum := by decide
  have hdescent : baseEnd_3790642 < baseStart_3790642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790659 : List Nat := [1, 1, 1, 3, 1, 5, 1, 5, 4]
def baseStart_3790659 : Nat := 118140960795 + 3790659 * 2 ^ 59
def prefixEnd_3790659 : Nat := 4983230072969 + 3 ^ 40 * 3790659 * 2
def baseEnd_3790659 : Nat := 432540014287019947317685

theorem tailTrace_3790659 : CollatzResearch.WordTrace tailWord_3790659 prefixEnd_3790659 432540014287019947317685 := by
  unfold tailWord_3790659
  simp only [CollatzResearch.WordTrace]
  refine ⟨138256691974097310860719031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92171127982731540573812687 138256691974097310860719031)
  ·
    refine ⟨207385037961145966291078547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138256691974097310860719031 207385037961145966291078547)
    ·
      refine ⟨311077556941718949436617821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207385037961145966291078547 311077556941718949436617821)
      ·
        refine ⟨116654083853144606038731683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311077556941718949436617821 116654083853144606038731683)
        ·
          refine ⟨174981125779716909058097525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116654083853144606038731683 174981125779716909058097525)
          ·
            refine ⟨16404480541848460224196643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174981125779716909058097525 16404480541848460224196643)
            ·
              refine ⟨24606720812772690336294965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16404480541848460224196643 24606720812772690336294965)
              ·
                refine ⟨2306880076197439719027653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24606720812772690336294965 2306880076197439719027653)
                ·
                  refine ⟨432540014287019947317685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2306880076197439719027653 432540014287019947317685)
                  ·
                    rfl

theorem cell22_3790659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 4].length) (baseStart_3790659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790659 prefixEnd_3790659 := by exact prefixLift 3790659
  have htrace : WordTrace (prefixWord ++ tailWord_3790659) baseStart_3790659 baseEnd_3790659 := by
    simpa [prefixWord, tailWord_3790659, baseEnd_3790659] using wordTrace_append hprefix tailTrace_3790659
  have hstable : (prefixWord ++ tailWord_3790659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790659).length < 2 ^ (prefixWord ++ tailWord_3790659).sum := by decide
  have hdescent : baseEnd_3790659 < baseStart_3790659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790672 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 4, 4]
def baseStart_3790672 : Nat := 118140960795 + 3790672 * 2 ^ 59
def prefixEnd_3790672 : Nat := 4983230072969 + 3 ^ 40 * 3790672 * 2
def baseEnd_3790672 : Nat := 1297624493026732141378015

theorem tailTrace_3790672 : CollatzResearch.WordTrace tailWord_3790672 prefixEnd_3790672 1297624493026732141378015 := by
  unfold tailWord_3790672
  simp only [CollatzResearch.WordTrace]
  refine ⟨69128583061525107040471135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92171444082033476053961513 69128583061525107040471135)
  ·
    refine ⟨103692874592287660560706703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69128583061525107040471135 103692874592287660560706703)
    ·
      refine ⟨155539311888431490841060055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103692874592287660560706703 155539311888431490841060055)
      ·
        refine ⟨233308967832647236261590083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155539311888431490841060055 233308967832647236261590083)
        ·
          refine ⟨349963451748970854392385125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233308967832647236261590083 349963451748970854392385125)
          ·
            refine ⟨65618147202932035198572211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349963451748970854392385125 65618147202932035198572211)
            ·
              refine ⟨98427220804398052797858317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65618147202932035198572211 98427220804398052797858317)
              ·
                refine ⟨36910207801649269799196869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98427220804398052797858317 36910207801649269799196869)
                ·
                  refine ⟨6920663962809238087349413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36910207801649269799196869 6920663962809238087349413)
                  ·
                    refine ⟨1297624493026732141378015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6920663962809238087349413 1297624493026732141378015)
                    ·
                      rfl

theorem cell22_3790672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_3790672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790672 prefixEnd_3790672 := by exact prefixLift 3790672
  have htrace : WordTrace (prefixWord ++ tailWord_3790672) baseStart_3790672 baseEnd_3790672 := by
    simpa [prefixWord, tailWord_3790672, baseEnd_3790672] using wordTrace_append hprefix tailTrace_3790672
  have hstable : (prefixWord ++ tailWord_3790672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790672).length < 2 ^ (prefixWord ++ tailWord_3790672).sum := by decide
  have hdescent : baseEnd_3790672 < baseStart_3790672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790676 : List Nat := [2, 4, 1, 1, 3, 1, 2, 4, 4]
def baseStart_3790676 : Nat := 118140960795 + 3790676 * 2 ^ 59
def prefixEnd_3790676 : Nat := 4983230072969 + 3 ^ 40 * 3790676 * 2
def baseEnd_3790676 : Nat := 432541954102825821426001

theorem tailTrace_3790676 : CollatzResearch.WordTrace tailWord_3790676 prefixEnd_3790676 432541954102825821426001 := by
  unfold tailWord_3790676
  simp only [CollatzResearch.WordTrace]
  refine ⟨69128656007517861382043941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92171541343357148509391921 69128656007517861382043941)
  ·
    refine ⟨12961623001409599009133239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69128656007517861382043941 12961623001409599009133239)
    ·
      refine ⟨19442434502114398513699859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12961623001409599009133239 19442434502114398513699859)
      ·
        refine ⟨29163651753171597770549789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19442434502114398513699859 29163651753171597770549789)
        ·
          refine ⟨10936369407439349163956171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29163651753171597770549789 10936369407439349163956171)
          ·
            refine ⟨16404554111159023745934257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10936369407439349163956171 16404554111159023745934257)
            ·
              refine ⟨12303415583369267809450693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16404554111159023745934257 12303415583369267809450693)
              ·
                refine ⟨2306890421881737714272005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12303415583369267809450693 2306890421881737714272005)
                ·
                  refine ⟨432541954102825821426001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2306890421881737714272005 432541954102825821426001)
                  ·
                    rfl

theorem cell22_3790676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_3790676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790676 prefixEnd_3790676 := by exact prefixLift 3790676
  have htrace : WordTrace (prefixWord ++ tailWord_3790676) baseStart_3790676 baseEnd_3790676 := by
    simpa [prefixWord, tailWord_3790676, baseEnd_3790676] using wordTrace_append hprefix tailTrace_3790676
  have hstable : (prefixWord ++ tailWord_3790676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790676).length < 2 ^ (prefixWord ++ tailWord_3790676).sum := by decide
  have hdescent : baseEnd_3790676 < baseStart_3790676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790691 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 1, 5]
def baseStart_3790691 : Nat := 118140960795 + 3790691 * 2 ^ 59
def prefixEnd_3790691 : Nat := 4983230072969 + 3 ^ 40 * 3790691 * 2
def baseEnd_3790691 : Nat := 1297630997115022425152957

theorem tailTrace_3790691 : CollatzResearch.WordTrace tailWord_3790691 prefixEnd_3790691 1297630997115022425152957 := by
  unfold tailWord_3790691
  simp only [CollatzResearch.WordTrace]
  refine ⟨138257859109981380325883927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92171906073320920217255951 138257859109981380325883927)
  ·
    refine ⟨207386788664972070488825891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138257859109981380325883927 207386788664972070488825891)
    ·
      refine ⟨311080182997458105733238837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207386788664972070488825891 311080182997458105733238837)
      ·
        refine ⟨29163767156011697412491141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311080182997458105733238837 29163767156011697412491141)
        ·
          refine ⟨5468206341752193264842089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29163767156011697412491141 5468206341752193264842089)
          ·
            refine ⟨4101154756314144948631567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5468206341752193264842089 4101154756314144948631567)
            ·
              refine ⟨6151732134471217422947351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101154756314144948631567 6151732134471217422947351)
              ·
                refine ⟨9227598201706826134421027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6151732134471217422947351 9227598201706826134421027)
                ·
                  refine ⟨13841397302560239201631541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9227598201706826134421027 13841397302560239201631541)
                  ·
                    refine ⟨1297630997115022425152957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13841397302560239201631541 1297630997115022425152957)
                    ·
                      rfl

theorem cell22_3790691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 5].length) (baseStart_3790691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790691 prefixEnd_3790691 := by exact prefixLift 3790691
  have htrace : WordTrace (prefixWord ++ tailWord_3790691) baseStart_3790691 baseEnd_3790691 := by
    simpa [prefixWord, tailWord_3790691, baseEnd_3790691] using wordTrace_append hprefix tailTrace_3790691
  have hstable : (prefixWord ++ tailWord_3790691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790691).length < 2 ^ (prefixWord ++ tailWord_3790691).sum := by decide
  have hdescent : baseEnd_3790691 < baseStart_3790691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790710 : List Nat := [5, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_3790710 : Nat := 118140960795 + 3790710 * 2 ^ 59
def prefixEnd_3790710 : Nat := 4983230072969 + 3 ^ 40 * 3790710 * 2
def baseEnd_3790710 : Nat := 432545833734437569642633

theorem tailTrace_3790710 : CollatzResearch.WordTrace tailWord_3790710 prefixEnd_3790710 432545833734437569642633 := by
  unfold tailWord_3790710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8641159506057034160676599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92172368064608364380550389 8641159506057034160676599)
  ·
    refine ⟨12961739259085551241014899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8641159506057034160676599 12961739259085551241014899)
    ·
      refine ⟨19442608888628326861522349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12961739259085551241014899 19442608888628326861522349)
      ·
        refine ⟨7290978333235622573070881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19442608888628326861522349 7290978333235622573070881)
        ·
          refine ⟨5468233749926716929803161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7290978333235622573070881 5468233749926716929803161)
          ·
            refine ⟨4101175312445037697352371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5468233749926716929803161 4101175312445037697352371)
            ·
              refine ⟨6151762968667556546028557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101175312445037697352371 6151762968667556546028557)
              ·
                refine ⟨2306911113250333704760709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6151762968667556546028557 2306911113250333704760709)
                ·
                  refine ⟨432545833734437569642633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2306911113250333704760709 432545833734437569642633)
                  ·
                    rfl

theorem cell22_3790710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_3790710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790710 prefixEnd_3790710 := by exact prefixLift 3790710
  have htrace : WordTrace (prefixWord ++ tailWord_3790710) baseStart_3790710 baseEnd_3790710 := by
    simpa [prefixWord, tailWord_3790710, baseEnd_3790710] using wordTrace_append hprefix tailTrace_3790710
  have hstable : (prefixWord ++ tailWord_3790710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790710).length < 2 ^ (prefixWord ++ tailWord_3790710).sum := by decide
  have hdescent : baseEnd_3790710 < baseStart_3790710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790717 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3790717 : Nat := 118140960795 + 3790717 * 2 ^ 59
def prefixEnd_3790717 : Nat := 4983230072969 + 3 ^ 40 * 3790717 * 2
def baseEnd_3790717 : Nat := 1297639897446367024002877

theorem tailTrace_3790717 : CollatzResearch.WordTrace tailWord_3790717 prefixEnd_3790717 1297639897446367024002877 := by
  unfold tailWord_3790717
  simp only [CollatzResearch.WordTrace]
  refine ⟨138258807407887186766330405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92172538271924791177553603 138258807407887186766330405)
  ·
    refine ⟨25923526388978847518686951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138258807407887186766330405 25923526388978847518686951)
    ·
      refine ⟨38885289583468271278030427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25923526388978847518686951 38885289583468271278030427)
      ·
        refine ⟨58327934375202406917045641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38885289583468271278030427 58327934375202406917045641)
        ·
          refine ⟨43745950781401805187784231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58327934375202406917045641 43745950781401805187784231)
          ·
            refine ⟨65618926172102707781676347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43745950781401805187784231 65618926172102707781676347)
            ·
              refine ⟨98428389258154061672514521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65618926172102707781676347 98428389258154061672514521)
              ·
                refine ⟨73821291943615546254385891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98428389258154061672514521 73821291943615546254385891)
                ·
                  refine ⟨110731937915423319381578837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73821291943615546254385891 110731937915423319381578837)
                  ·
                    refine ⟨1297639897446367024002877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110731937915423319381578837 1297639897446367024002877)
                    ·
                      rfl

theorem cell22_3790717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3790717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790717 prefixEnd_3790717 := by exact prefixLift 3790717
  have htrace : WordTrace (prefixWord ++ tailWord_3790717) baseStart_3790717 baseEnd_3790717 := by
    simpa [prefixWord, tailWord_3790717, baseEnd_3790717] using wordTrace_append hprefix tailTrace_3790717
  have hstable : (prefixWord ++ tailWord_3790717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790717).length < 2 ^ (prefixWord ++ tailWord_3790717).sum := by decide
  have hdescent : baseEnd_3790717 < baseStart_3790717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790721 : List Nat := [1, 2, 4, 4, 1, 2, 8]
def baseStart_3790721 : Nat := 118140960795 + 3790721 * 2 ^ 59
def prefixEnd_3790721 : Nat := 4983230072969 + 3 ^ 40 * 3790721 * 2
def baseEnd_3790721 : Nat := 48060787656596753588995

theorem tailTrace_3790721 : CollatzResearch.WordTrace tailWord_3790721 prefixEnd_3790721 48060787656596753588995 := by
  unfold tailWord_3790721
  simp only [CollatzResearch.WordTrace]
  refine ⟨138258953299872695449476017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92172635533248463632984011 138258953299872695449476017)
  ·
    refine ⟨103694214974904521587107013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138258953299872695449476017 103694214974904521587107013)
    ·
      refine ⟨19442665307794597797582565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103694214974904521587107013 19442665307794597797582565)
      ·
        refine ⟨3645499745211487087046731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19442665307794597797582565 3645499745211487087046731)
        ·
          refine ⟨5468249617817230630570097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645499745211487087046731 5468249617817230630570097)
          ·
            refine ⟨4101187213362922972927573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5468249617817230630570097 4101187213362922972927573)
            ·
              refine ⟨48060787656596753588995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4101187213362922972927573 48060787656596753588995)
              ·
                rfl

theorem cell22_3790721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 8].length) (baseStart_3790721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790721 prefixEnd_3790721 := by exact prefixLift 3790721
  have htrace : WordTrace (prefixWord ++ tailWord_3790721) baseStart_3790721 baseEnd_3790721 := by
    simpa [prefixWord, tailWord_3790721, baseEnd_3790721] using wordTrace_append hprefix tailTrace_3790721
  have hstable : (prefixWord ++ tailWord_3790721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790721).length < 2 ^ (prefixWord ++ tailWord_3790721).sum := by decide
  have hdescent : baseEnd_3790721 < baseStart_3790721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790742 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3790742 : Nat := 118140960795 + 3790742 * 2 ^ 59
def prefixEnd_3790742 : Nat := 4983230072969 + 3 ^ 40 * 3790742 * 2
def baseEnd_3790742 : Nat := 1297648455457275292127801

theorem tailTrace_3790742 : CollatzResearch.WordTrace tailWord_3790742 prefixEnd_3790742 1297648455457275292127801 := by
  unfold tailWord_3790742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8641232452049788502249405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92173146155197744023993653 8641232452049788502249405)
  ·
    refine ⟨3240462169518670688343527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8641232452049788502249405 3240462169518670688343527)
    ·
      refine ⟨4860693254278006032515291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3240462169518670688343527 4860693254278006032515291)
      ·
        refine ⟨7291039881417009048772937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4860693254278006032515291 7291039881417009048772937)
        ·
          refine ⟨5468279911062756786579703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7291039881417009048772937 5468279911062756786579703)
          ·
            refine ⟨8202419866594135179869555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5468279911062756786579703 8202419866594135179869555)
            ·
              refine ⟨12303629799891202769804333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8202419866594135179869555 12303629799891202769804333)
              ·
                refine ⟨4613861174959201038676625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12303629799891202769804333 4613861174959201038676625)
                ·
                  refine ⟨3460395881219400779007469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4613861174959201038676625 3460395881219400779007469)
                  ·
                    refine ⟨1297648455457275292127801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3460395881219400779007469 1297648455457275292127801)
                    ·
                      rfl

theorem cell22_3790742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3790742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790742 prefixEnd_3790742 := by exact prefixLift 3790742
  have htrace : WordTrace (prefixWord ++ tailWord_3790742) baseStart_3790742 baseEnd_3790742 := by
    simpa [prefixWord, tailWord_3790742, baseEnd_3790742] using wordTrace_append hprefix tailTrace_3790742
  have hstable : (prefixWord ++ tailWord_3790742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790742).length < 2 ^ (prefixWord ++ tailWord_3790742).sum := by decide
  have hdescent : baseEnd_3790742 < baseStart_3790742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790826 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 4, 3]
def baseStart_3790826 : Nat := 118140960795 + 3790826 * 2 ^ 59
def prefixEnd_3790826 : Nat := 4983230072969 + 3 ^ 40 * 3790826 * 2
def baseEnd_3790826 : Nat := 1297677210373927073027543

theorem tailTrace_3790826 : CollatzResearch.WordTrace tailWord_3790826 prefixEnd_3790826 1297677210373927073027543 := by
  unfold tailWord_3790826
  simp only [CollatzResearch.WordTrace]
  refine ⟨34565695741123074595512083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92175188642994865588032221 34565695741123074595512083)
  ·
    refine ⟨51848543611684611893268125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34565695741123074595512083 51848543611684611893268125)
    ·
      refine ⟨19443203854381729459975547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51848543611684611893268125 19443203854381729459975547)
      ·
        refine ⟨29164805781572594189963321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19443203854381729459975547 29164805781572594189963321)
        ·
          refine ⟨21873604336179445642472491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29164805781572594189963321 21873604336179445642472491)
          ·
            refine ⟨32810406504269168463708737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21873604336179445642472491 32810406504269168463708737)
            ·
              refine ⟨24607804878201876347781553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32810406504269168463708737 24607804878201876347781553)
              ·
                refine ⟨18455853658651407260836165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24607804878201876347781553 18455853658651407260836165)
                ·
                  refine ⟨3460472560997138861406781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18455853658651407260836165 3460472560997138861406781)
                  ·
                    refine ⟨1297677210373927073027543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3460472560997138861406781 1297677210373927073027543)
                    ·
                      rfl

theorem cell22_3790826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_3790826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790826 prefixEnd_3790826 := by exact prefixLift 3790826
  have htrace : WordTrace (prefixWord ++ tailWord_3790826) baseStart_3790826 baseEnd_3790826 := by
    simpa [prefixWord, tailWord_3790826, baseEnd_3790826] using wordTrace_append hprefix tailTrace_3790826
  have hstable : (prefixWord ++ tailWord_3790826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790826).length < 2 ^ (prefixWord ++ tailWord_3790826).sum := by decide
  have hdescent : baseEnd_3790826 < baseStart_3790826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790830 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_3790830 : Nat := 118140960795 + 3790830 * 2 ^ 59
def prefixEnd_3790830 : Nat := 4983230072969 + 3 ^ 40 * 3790830 * 2
def baseEnd_3790830 : Nat := 1297678579655672395927531

theorem tailTrace_3790830 : CollatzResearch.WordTrace tailWord_3790830 prefixEnd_3790830 1297678579655672395927531 := by
  unfold tailWord_3790830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17282866107059725883149243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92175285904318538043462629 17282866107059725883149243)
  ·
    refine ⟨25924299160589588824723865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17282866107059725883149243 25924299160589588824723865)
    ·
      refine ⟨19443224370442191618542899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25924299160589588824723865 19443224370442191618542899)
      ·
        refine ⟨29164836555663287427814349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19443224370442191618542899 29164836555663287427814349)
        ·
          refine ⟨10936813708373732785430381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29164836555663287427814349 10936813708373732785430381)
          ·
            refine ⟨4101305140640149794536393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10936813708373732785430381 4101305140640149794536393)
            ·
              refine ⟨3075978855480112345902295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4101305140640149794536393 3075978855480112345902295)
              ·
                refine ⟨4613968283220168518853443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075978855480112345902295 4613968283220168518853443)
                ·
                  refine ⟨6920952424830252778280165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4613968283220168518853443 6920952424830252778280165)
                  ·
                    refine ⟨1297678579655672395927531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6920952424830252778280165 1297678579655672395927531)
                    ·
                      rfl

theorem cell22_3790830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_3790830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790830 prefixEnd_3790830 := by exact prefixLift 3790830
  have htrace : WordTrace (prefixWord ++ tailWord_3790830) baseStart_3790830 baseEnd_3790830 := by
    simpa [prefixWord, tailWord_3790830, baseEnd_3790830] using wordTrace_append hprefix tailTrace_3790830
  have hstable : (prefixWord ++ tailWord_3790830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790830).length < 2 ^ (prefixWord ++ tailWord_3790830).sum := by decide
  have hdescent : baseEnd_3790830 < baseStart_3790830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790899 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 4, 5]
def baseStart_3790899 : Nat := 118140960795 + 3790899 * 2 ^ 59
def prefixEnd_3790899 : Nat := 4983230072969 + 3 ^ 40 * 3790899 * 2
def baseEnd_3790899 : Nat := 1297702199765779215952319

theorem tailTrace_3790899 : CollatzResearch.WordTrace tailWord_3790899 prefixEnd_3790899 1297702199765779215952319 := by
  unfold tailWord_3790899
  simp only [CollatzResearch.WordTrace]
  refine ⟨138265445493227831849455751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92176963662151887899637167 138265445493227831849455751)
  ·
    refine ⟨207398168239841747774183627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138265445493227831849455751 207398168239841747774183627)
    ·
      refine ⟨311097252359762621661275441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207398168239841747774183627 311097252359762621661275441)
      ·
        refine ⟨233322939269821966245956581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311097252359762621661275441 233322939269821966245956581)
        ·
          refine ⟨43748051113091618671116859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233322939269821966245956581 43748051113091618671116859)
          ·
            refine ⟨65622076669637428006675289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43748051113091618671116859 65622076669637428006675289)
            ·
              refine ⟨49216557502228071005006467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65622076669637428006675289 49216557502228071005006467)
              ·
                refine ⟨73824836253342106507509701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49216557502228071005006467 73824836253342106507509701)
                ·
                  refine ⟨13842156797501644970158069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73824836253342106507509701 13842156797501644970158069)
                  ·
                    refine ⟨1297702199765779215952319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13842156797501644970158069 1297702199765779215952319)
                    ·
                      rfl

theorem cell22_3790899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_3790899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790899 prefixEnd_3790899 := by exact prefixLift 3790899
  have htrace : WordTrace (prefixWord ++ tailWord_3790899) baseStart_3790899 baseEnd_3790899 := by
    simpa [prefixWord, tailWord_3790899, baseEnd_3790899] using wordTrace_append hprefix tailTrace_3790899
  have hstable : (prefixWord ++ tailWord_3790899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790899).length < 2 ^ (prefixWord ++ tailWord_3790899).sum := by decide
  have hdescent : baseEnd_3790899 < baseStart_3790899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790905 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 3, 3]
def baseStart_3790905 : Nat := 118140960795 + 3790905 * 2 ^ 59
def prefixEnd_3790905 : Nat := 4983230072969 + 3 ^ 40 * 3790905 * 2
def baseEnd_3790905 : Nat := 1297704253688397200302301

theorem tailTrace_3790905 : CollatzResearch.WordTrace tailWord_3790905 prefixEnd_3790905 1297704253688397200302301 := by
  unfold tailWord_3790905
  simp only [CollatzResearch.WordTrace]
  refine ⟨138265664331206094874174169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92177109554137396582782779 138265664331206094874174169)
  ·
    refine ⟨103699248248404571155630627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138265664331206094874174169 103699248248404571155630627)
    ·
      refine ⟨155548872372606856733445941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103699248248404571155630627 155548872372606856733445941)
      ·
        refine ⟨14582706784931892818760557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155548872372606856733445941 14582706784931892818760557)
        ·
          refine ⟨5468515044349459807035209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14582706784931892818760557 5468515044349459807035209)
          ·
            refine ⟨4101386283262094855276407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5468515044349459807035209 4101386283262094855276407)
            ·
              refine ⟨6152079424893142282914611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101386283262094855276407 6152079424893142282914611)
              ·
                refine ⟨9228119137339713424371917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6152079424893142282914611 9228119137339713424371917)
                ·
                  refine ⟨3460544676502392534139469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9228119137339713424371917 3460544676502392534139469)
                  ·
                    refine ⟨1297704253688397200302301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3460544676502392534139469 1297704253688397200302301)
                    ·
                      rfl

theorem cell22_3790905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 3].length) (baseStart_3790905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790905 prefixEnd_3790905 := by exact prefixLift 3790905
  have htrace : WordTrace (prefixWord ++ tailWord_3790905) baseStart_3790905 baseEnd_3790905 := by
    simpa [prefixWord, tailWord_3790905, baseEnd_3790905] using wordTrace_append hprefix tailTrace_3790905
  have hstable : (prefixWord ++ tailWord_3790905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790905).length < 2 ^ (prefixWord ++ tailWord_3790905).sum := by decide
  have hdescent : baseEnd_3790905 < baseStart_3790905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3790929 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 8]
def baseStart_3790929 : Nat := 118140960795 + 3790929 * 2 ^ 59
def prefixEnd_3790929 : Nat := 4983230072969 + 3 ^ 40 * 3790929 * 2
def baseEnd_3790929 : Nat := 432570823126289712567409

theorem tailTrace_3790929 : CollatzResearch.WordTrace tailWord_3790929 prefixEnd_3790929 432570823126289712567409 := by
  unfold tailWord_3790929
  simp only [CollatzResearch.WordTrace]
  refine ⟨138266539683119146973047841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92177693122079431315365227 138266539683119146973047841)
  ·
    refine ⟨103699904762339360229785881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138266539683119146973047841 103699904762339360229785881)
    ·
      refine ⟨77774928571754520172339411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103699904762339360229785881 77774928571754520172339411)
      ·
        refine ⟨116662392857631780258509117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77774928571754520172339411 116662392857631780258509117)
        ·
          refine ⟨43748397321611917596940919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116662392857631780258509117 43748397321611917596940919)
          ·
            refine ⟨65622595982417876395411379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43748397321611917596940919 65622595982417876395411379)
            ·
              refine ⟨98433893973626814593117069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65622595982417876395411379 98433893973626814593117069)
              ·
                refine ⟨36912710240110055472418901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98433893973626814593117069 36912710240110055472418901)
                ·
                  refine ⟨432570823126289712567409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36912710240110055472418901 432570823126289712567409)
                  ·
                    rfl

theorem cell22_3790929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_3790929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3790929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3790929 prefixEnd_3790929 := by exact prefixLift 3790929
  have htrace : WordTrace (prefixWord ++ tailWord_3790929) baseStart_3790929 baseEnd_3790929 := by
    simpa [prefixWord, tailWord_3790929, baseEnd_3790929] using wordTrace_append hprefix tailTrace_3790929
  have hstable : (prefixWord ++ tailWord_3790929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3790929).length < 2 ^ (prefixWord ++ tailWord_3790929).sum := by decide
  have hdescent : baseEnd_3790929 < baseStart_3790929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3790929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791012 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_3791012 : Nat := 118140960795 + 3791012 * 2 ^ 59
def prefixEnd_3791012 : Nat := 4983230072969 + 3 ^ 40 * 3791012 * 2
def baseEnd_3791012 : Nat := 1297740881975084587876973

theorem tailTrace_3791012 : CollatzResearch.WordTrace tailWord_3791012 prefixEnd_3791012 1297740881975084587876973 := by
  unfold tailWord_3791012
  simp only [CollatzResearch.WordTrace]
  refine ⟨69134783470909226074159645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92179711294545634765546193 69134783470909226074159645)
  ·
    refine ⟨25925543801590959777809867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69134783470909226074159645 25925543801590959777809867)
    ·
      refine ⟨38888315702386439666714801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25925543801590959777809867 38888315702386439666714801)
      ·
        refine ⟨29166236776789829750036101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38888315702386439666714801 29166236776789829750036101)
        ·
          refine ⟨5468669395648093078131769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29166236776789829750036101 5468669395648093078131769)
          ·
            refine ⟨4101502046736069808598827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5468669395648093078131769 4101502046736069808598827)
            ·
              refine ⟨6152253070104104712898241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101502046736069808598827 6152253070104104712898241)
              ·
                refine ⟨4614189802578078534673681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6152253070104104712898241 4614189802578078534673681)
                ·
                  refine ⟨3460642351933558901005261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4614189802578078534673681 3460642351933558901005261)
                  ·
                    refine ⟨1297740881975084587876973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3460642351933558901005261 1297740881975084587876973)
                    ·
                      rfl

theorem cell22_3791012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_3791012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791012 prefixEnd_3791012 := by exact prefixLift 3791012
  have htrace : WordTrace (prefixWord ++ tailWord_3791012) baseStart_3791012 baseEnd_3791012 := by
    simpa [prefixWord, tailWord_3791012, baseEnd_3791012] using wordTrace_append hprefix tailTrace_3791012
  have hstable : (prefixWord ++ tailWord_3791012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791012).length < 2 ^ (prefixWord ++ tailWord_3791012).sum := by decide
  have hdescent : baseEnd_3791012 < baseStart_3791012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791029 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3791029 : Nat := 118140960795 + 3791029 * 2 ^ 59
def prefixEnd_3791029 : Nat := 4983230072969 + 3 ^ 40 * 3791029 * 2
def baseEnd_3791029 : Nat := 1297746701422502210201921

theorem tailTrace_3791029 : CollatzResearch.WordTrace tailWord_3791029 prefixEnd_3791029 1297746701422502210201921 := by
  unfold tailWord_3791029
  simp only [CollatzResearch.WordTrace]
  refine ⟨138270186982756864051688141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92180124655171242701125427 138270186982756864051688141)
  ·
    refine ⟨51851320118533824019383053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138270186982756864051688141 51851320118533824019383053)
    ·
      refine ⟨19444245044450184007268645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51851320118533824019383053 19444245044450184007268645)
      ·
        refine ⟨3645795945834409501362871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19444245044450184007268645 3645795945834409501362871)
        ·
          refine ⟨5468693918751614252044307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645795945834409501362871 5468693918751614252044307)
          ·
            refine ⟨8203040878127421378066461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5468693918751614252044307 8203040878127421378066461)
            ·
              refine ⟨3076140329297783016774923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8203040878127421378066461 3076140329297783016774923)
              ·
                refine ⟨4614210493946674525162385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076140329297783016774923 4614210493946674525162385)
                ·
                  refine ⟨3460657870460005893871789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4614210493946674525162385 3460657870460005893871789)
                  ·
                    refine ⟨1297746701422502210201921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3460657870460005893871789 1297746701422502210201921)
                    ·
                      rfl

theorem cell22_3791029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3791029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791029 prefixEnd_3791029 := by exact prefixLift 3791029
  have htrace : WordTrace (prefixWord ++ tailWord_3791029) baseStart_3791029 baseEnd_3791029 := by
    simpa [prefixWord, tailWord_3791029, baseEnd_3791029] using wordTrace_append hprefix tailTrace_3791029
  have hstable : (prefixWord ++ tailWord_3791029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791029).length < 2 ^ (prefixWord ++ tailWord_3791029).sum := by decide
  have hdescent : baseEnd_3791029 < baseStart_3791029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791042 : List Nat := [3, 5, 1, 1, 1, 1, 4, 6]
def baseStart_3791042 : Nat := 118140960795 + 3791042 * 2 ^ 59
def prefixEnd_3791042 : Nat := 4983230072969 + 3 ^ 40 * 3791042 * 2
def baseEnd_3791042 : Nat := 144194572398686056625209

theorem tailTrace_3791042 : CollatzResearch.WordTrace tailWord_3791042 prefixEnd_3791042 144194572398686056625209 := by
  unfold tailWord_3791042
  simp only [CollatzResearch.WordTrace]
  refine ⟨34567665282927441817977845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92180440754473178181274253 34567665282927441817977845)
  ·
    refine ⟨3240718620274447670435423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34567665282927441817977845 3240718620274447670435423)
    ·
      refine ⟨4861077930411671505653135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3240718620274447670435423 4861077930411671505653135)
      ·
        refine ⟨7291616895617507258479703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4861077930411671505653135 7291616895617507258479703)
        ·
          refine ⟨10937425343426260887719555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7291616895617507258479703 10937425343426260887719555)
          ·
            refine ⟨16406138015139391331579333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10937425343426260887719555 16406138015139391331579333)
            ·
              refine ⟨3076150877838635874671125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16406138015139391331579333 3076150877838635874671125)
              ·
                refine ⟨144194572398686056625209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3076150877838635874671125 144194572398686056625209)
                ·
                  rfl

theorem cell22_3791042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_3791042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791042 prefixEnd_3791042 := by exact prefixLift 3791042
  have htrace : WordTrace (prefixWord ++ tailWord_3791042) baseStart_3791042 baseEnd_3791042 := by
    simpa [prefixWord, tailWord_3791042, baseEnd_3791042] using wordTrace_append hprefix tailTrace_3791042
  have hstable : (prefixWord ++ tailWord_3791042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791042).length < 2 ^ (prefixWord ++ tailWord_3791042).sum := by decide
  have hdescent : baseEnd_3791042 < baseStart_3791042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791096 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_3791096 : Nat := 118140960795 + 3791096 * 2 ^ 59
def prefixEnd_3791096 : Nat := 4983230072969 + 3 ^ 40 * 3791096 * 2
def baseEnd_3791096 : Nat := 1297769636891736368776715

theorem tailTrace_3791096 : CollatzResearch.WordTrace tailWord_3791096 prefixEnd_3791096 1297769636891736368776715 := by
  unfold tailWord_3791096
  simp only [CollatzResearch.WordTrace]
  refine ⟨69136315336757067247188571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92181753782342756329584761 69136315336757067247188571)
  ·
    refine ⟨103704473005135600870782857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69136315336757067247188571 103704473005135600870782857)
    ·
      refine ⟨77778354753851700653087143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103704473005135600870782857 77778354753851700653087143)
      ·
        refine ⟨116667532130777550979630715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77778354753851700653087143 116667532130777550979630715)
        ·
          refine ⟨175001298196166326469446073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116667532130777550979630715 175001298196166326469446073)
          ·
            refine ⟨131250973647124744852084555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175001298196166326469446073 131250973647124744852084555)
            ·
              refine ⟨196876460470687117278126833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131250973647124744852084555 196876460470687117278126833)
              ·
                refine ⟨147657345353015337958595125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196876460470687117278126833 147657345353015337958595125)
                ·
                  refine ⟨13842876126845187933618293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147657345353015337958595125 13842876126845187933618293)
                  ·
                    refine ⟨1297769636891736368776715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13842876126845187933618293 1297769636891736368776715)
                    ·
                      rfl

theorem cell22_3791096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_3791096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791096 prefixEnd_3791096 := by exact prefixLift 3791096
  have htrace : WordTrace (prefixWord ++ tailWord_3791096) baseStart_3791096 baseEnd_3791096 := by
    simpa [prefixWord, tailWord_3791096, baseEnd_3791096] using wordTrace_append hprefix tailTrace_3791096
  have hstable : (prefixWord ++ tailWord_3791096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791096).length < 2 ^ (prefixWord ++ tailWord_3791096).sum := by decide
  have hdescent : baseEnd_3791096 < baseStart_3791096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791100 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_3791100 : Nat := 118140960795 + 3791100 * 2 ^ 59
def prefixEnd_3791100 : Nat := 4983230072969 + 3 ^ 40 * 3791100 * 2
def baseEnd_3791100 : Nat := 1297771006173481691676703

theorem tailTrace_3791100 : CollatzResearch.WordTrace tailWord_3791100 prefixEnd_3791100 1297771006173481691676703 := by
  unfold tailWord_3791100
  simp only [CollatzResearch.WordTrace]
  refine ⟨69136388282749821588761377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92181851043666428785015169 69136388282749821588761377)
  ·
    refine ⟨51852291212062366191571033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69136388282749821588761377 51852291212062366191571033)
    ·
      refine ⟨38889218409046774643678275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51852291212062366191571033 38889218409046774643678275)
      ·
        refine ⟨58333827613570161965517413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38889218409046774643678275 58333827613570161965517413)
        ·
          refine ⟨10937592677544405368534515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58333827613570161965517413 10937592677544405368534515)
          ·
            refine ⟨16406389016316608052801773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10937592677544405368534515 16406389016316608052801773)
            ·
              refine ⟨6152395881118728019800665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16406389016316608052801773 6152395881118728019800665)
              ·
                refine ⟨4614296910839046014850499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6152395881118728019800665 4614296910839046014850499)
                ·
                  refine ⟨6921445366258569022275749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614296910839046014850499 6921445366258569022275749)
                  ·
                    refine ⟨1297771006173481691676703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6921445366258569022275749 1297771006173481691676703)
                    ·
                      rfl

theorem cell22_3791100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_3791100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791100 prefixEnd_3791100 := by exact prefixLift 3791100
  have htrace : WordTrace (prefixWord ++ tailWord_3791100) baseStart_3791100 baseEnd_3791100 := by
    simpa [prefixWord, tailWord_3791100, baseEnd_3791100] using wordTrace_append hprefix tailTrace_3791100
  have hstable : (prefixWord ++ tailWord_3791100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791100).length < 2 ^ (prefixWord ++ tailWord_3791100).sum := by decide
  have hdescent : baseEnd_3791100 < baseStart_3791100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791113 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 1, 5]
def baseStart_3791113 : Nat := 118140960795 + 3791113 * 2 ^ 59
def prefixEnd_3791113 : Nat := 4983230072969 + 3 ^ 40 * 3791113 * 2
def baseEnd_3791113 : Nat := 1297775456339153991101663

theorem tailTrace_3791113 : CollatzResearch.WordTrace tailWord_3791113 prefixEnd_3791113 1297775456339153991101663 := by
  unfold tailWord_3791113
  simp only [CollatzResearch.WordTrace]
  refine ⟨138273250714452546397745993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92182167142968364265163995 138273250714452546397745993)
  ·
    refine ⟨103704938035839409798309495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138273250714452546397745993 103704938035839409798309495)
    ·
      refine ⟨155557407053759114697464243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103704938035839409798309495 155557407053759114697464243)
      ·
        refine ⟨233336110580638672046196365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155557407053759114697464243 233336110580638672046196365)
        ·
          refine ⟨87501041467739502017323637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233336110580638672046196365 87501041467739502017323637)
          ·
            refine ⟨8203222637600578314124091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87501041467739502017323637 8203222637600578314124091)
            ·
              refine ⟨12304833956400867471186137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8203222637600578314124091 12304833956400867471186137)
              ·
                refine ⟨9228625467300650603389603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12304833956400867471186137 9228625467300650603389603)
                ·
                  refine ⟨13842938200950975905084405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9228625467300650603389603 13842938200950975905084405)
                  ·
                    refine ⟨1297775456339153991101663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13842938200950975905084405 1297775456339153991101663)
                    ·
                      rfl

theorem cell22_3791113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_3791113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791113 prefixEnd_3791113 := by exact prefixLift 3791113
  have htrace : WordTrace (prefixWord ++ tailWord_3791113) baseStart_3791113 baseEnd_3791113 := by
    simpa [prefixWord, tailWord_3791113, baseEnd_3791113] using wordTrace_append hprefix tailTrace_3791113
  have hstable : (prefixWord ++ tailWord_3791113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791113).length < 2 ^ (prefixWord ++ tailWord_3791113).sum := by decide
  have hdescent : baseEnd_3791113 < baseStart_3791113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791128 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 2, 4]
def baseStart_3791128 : Nat := 118140960795 + 3791128 * 2 ^ 59
def prefixEnd_3791128 : Nat := 4983230072969 + 3 ^ 40 * 3791128 * 2
def baseEnd_3791128 : Nat := 1297780591145698951976617

theorem tailTrace_3791128 : CollatzResearch.WordTrace tailWord_3791128 prefixEnd_3791128 1297780591145698951976617 := by
  unfold tailWord_3791128
  simp only [CollatzResearch.WordTrace]
  refine ⟨69136898904699101979771019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92182531872932135973028025 69136898904699101979771019)
  ·
    refine ⟨103705348357048652969656529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69136898904699101979771019 103705348357048652969656529)
    ·
      refine ⟨77779011267786489727242397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103705348357048652969656529 77779011267786489727242397)
      ·
        refine ⟨29167129225419933647715899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77779011267786489727242397 29167129225419933647715899)
        ·
          refine ⟨43750693838129900471573849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29167129225419933647715899 43750693838129900471573849)
          ·
            refine ⟨32813020378597425353680387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43750693838129900471573849 32813020378597425353680387)
            ·
              refine ⟨49219530567896138030520581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32813020378597425353680387 49219530567896138030520581)
              ·
                refine ⟨9228661981480525880722609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49219530567896138030520581 9228661981480525880722609)
                ·
                  refine ⟨6921496486110394410541957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9228661981480525880722609 6921496486110394410541957)
                  ·
                    refine ⟨1297780591145698951976617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6921496486110394410541957 1297780591145698951976617)
                    ·
                      rfl

theorem cell22_3791128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_3791128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791128 prefixEnd_3791128 := by exact prefixLift 3791128
  have htrace : WordTrace (prefixWord ++ tailWord_3791128) baseStart_3791128 baseEnd_3791128 := by
    simpa [prefixWord, tailWord_3791128, baseEnd_3791128] using wordTrace_append hprefix tailTrace_3791128
  have hstable : (prefixWord ++ tailWord_3791128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791128).length < 2 ^ (prefixWord ++ tailWord_3791128).sum := by decide
  have hdescent : baseEnd_3791128 < baseStart_3791128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791198 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3791198 : Nat := 118140960795 + 3791198 * 2 ^ 59
def prefixEnd_3791198 : Nat := 4983230072969 + 3 ^ 40 * 3791198 * 2
def baseEnd_3791198 : Nat := 1297804553576242102726403

theorem tailTrace_3791198 : CollatzResearch.WordTrace tailWord_3791198 prefixEnd_3791198 1297804553576242102726403 := by
  unfold tailWord_3791198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17284543864893075739323781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92184233946096403943060165 17284543864893075739323781)
  ·
    refine ⟨3240851974667451701123209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17284543864893075739323781 3240851974667451701123209)
    ·
      refine ⟨2430638981000588775842407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3240851974667451701123209 2430638981000588775842407)
      ·
        refine ⟨3645958471500883163763611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430638981000588775842407 3645958471500883163763611)
        ·
          refine ⟨5468937707251324745645417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645958471500883163763611 5468937707251324745645417)
          ·
            refine ⟨4101703280438493559234063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5468937707251324745645417 4101703280438493559234063)
            ·
              refine ⟨6152554920657740338851095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101703280438493559234063 6152554920657740338851095)
              ·
                refine ⟨9228832380986610508276643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6152554920657740338851095 9228832380986610508276643)
                ·
                  refine ⟨13843248571479915762414965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9228832380986610508276643 13843248571479915762414965)
                  ·
                    refine ⟨1297804553576242102726403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13843248571479915762414965 1297804553576242102726403)
                    ·
                      rfl

theorem cell22_3791198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3791198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791198 prefixEnd_3791198 := by exact prefixLift 3791198
  have htrace : WordTrace (prefixWord ++ tailWord_3791198) baseStart_3791198 baseEnd_3791198 := by
    simpa [prefixWord, tailWord_3791198, baseEnd_3791198] using wordTrace_append hprefix tailTrace_3791198
  have hstable : (prefixWord ++ tailWord_3791198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791198).length < 2 ^ (prefixWord ++ tailWord_3791198).sum := by decide
  have hdescent : baseEnd_3791198 < baseStart_3791198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791203 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 2, 5]
def baseStart_3791203 : Nat := 118140960795 + 3791203 * 2 ^ 59
def prefixEnd_3791203 : Nat := 4983230072969 + 3 ^ 40 * 3791203 * 2
def baseEnd_3791203 : Nat := 1297806265178423756351387

theorem tailTrace_3791203 : CollatzResearch.WordTrace tailWord_3791203 prefixEnd_3791203 1297806265178423756351387 := by
  unfold tailWord_3791203
  simp only [CollatzResearch.WordTrace]
  refine ⟨138276533284126491768522263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92184355522750994512348175 138276533284126491768522263)
  ·
    refine ⟨207414799926189737652783395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138276533284126491768522263 207414799926189737652783395)
    ·
      refine ⟨311122199889284606479175093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207414799926189737652783395 311122199889284606479175093)
      ·
        refine ⟨29167706239620431857422665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311122199889284606479175093 29167706239620431857422665)
        ·
          refine ⟨21875779679715323893066999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29167706239620431857422665 21875779679715323893066999)
          ·
            refine ⟨32813669519572985839600499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21875779679715323893066999 32813669519572985839600499)
            ·
              refine ⟨49220504279359478759400749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32813669519572985839600499 49220504279359478759400749)
              ·
                refine ⟨18457689104759804534775281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49220504279359478759400749 18457689104759804534775281)
                ·
                  refine ⟨13843266828569853401081461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18457689104759804534775281 13843266828569853401081461)
                  ·
                    refine ⟨1297806265178423756351387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13843266828569853401081461 1297806265178423756351387)
                    ·
                      rfl

theorem cell22_3791203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_3791203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791203 prefixEnd_3791203 := by exact prefixLift 3791203
  have htrace : WordTrace (prefixWord ++ tailWord_3791203) baseStart_3791203 baseEnd_3791203 := by
    simpa [prefixWord, tailWord_3791203, baseEnd_3791203] using wordTrace_append hprefix tailTrace_3791203
  have hstable : (prefixWord ++ tailWord_3791203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791203).length < 2 ^ (prefixWord ++ tailWord_3791203).sum := by decide
  have hdescent : baseEnd_3791203 < baseStart_3791203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791325 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3791325 : Nat := 118140960795 + 3791325 * 2 ^ 59
def prefixEnd_3791325 : Nat := 4983230072969 + 3 ^ 40 * 3791325 * 2
def baseEnd_3791325 : Nat := 1297848028271656104801013

theorem tailTrace_3791325 : CollatzResearch.WordTrace tailWord_3791325 prefixEnd_3791325 1297848028271656104801013 := by
  unfold tailWord_3791325
  simp only [CollatzResearch.WordTrace]
  refine ⟨138280982989684506604463429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92187321993123004402975619 138280982989684506604463429)
  ·
    refine ⟨25927684310565844988336893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138280982989684506604463429 25927684310565844988336893)
    ·
      refine ⟨9722881616462191870626335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25927684310565844988336893 9722881616462191870626335)
      ·
        refine ⟨14584322424693287805939503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9722881616462191870626335 14584322424693287805939503)
        ·
          refine ⟨21876483637039931708909255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14584322424693287805939503 21876483637039931708909255)
          ·
            refine ⟨32814725455559897563363883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21876483637039931708909255 32814725455559897563363883)
            ·
              refine ⟨49222088183339846345045825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32814725455559897563363883 49222088183339846345045825)
              ·
                refine ⟨36916566137504884758784369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49222088183339846345045825 36916566137504884758784369)
                ·
                  refine ⟨27687424603128663569088277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36916566137504884758784369 27687424603128663569088277)
                  ·
                    refine ⟨1297848028271656104801013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27687424603128663569088277 1297848028271656104801013)
                    ·
                      rfl

theorem cell22_3791325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3791325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791325 prefixEnd_3791325 := by exact prefixLift 3791325
  have htrace : WordTrace (prefixWord ++ tailWord_3791325) baseStart_3791325 baseEnd_3791325 := by
    simpa [prefixWord, tailWord_3791325, baseEnd_3791325] using wordTrace_append hprefix tailTrace_3791325
  have hstable : (prefixWord ++ tailWord_3791325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791325).length < 2 ^ (prefixWord ++ tailWord_3791325).sum := by decide
  have hdescent : baseEnd_3791325 < baseStart_3791325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791327 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 3, 3]
def baseStart_3791327 : Nat := 118140960795 + 3791327 * 2 ^ 59
def prefixEnd_3791327 : Nat := 4983230072969 + 3 ^ 40 * 3791327 * 2
def baseEnd_3791327 : Nat := 1297848712912528766251007

theorem tailTrace_3791327 : CollatzResearch.WordTrace tailWord_3791327 prefixEnd_3791327 1297848712912528766251007 := by
  unfold tailWord_3791327
  simp only [CollatzResearch.WordTrace]
  refine ⟨138281055935677260946036235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92187370623784840630690823 138281055935677260946036235)
  ·
    refine ⟨207421583903515891419054353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138281055935677260946036235 207421583903515891419054353)
    ·
      refine ⟨155566187927636918564290765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207421583903515891419054353 155566187927636918564290765)
      ·
        refine ⟨58337320472863844461609037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155566187927636918564290765 58337320472863844461609037)
        ·
          refine ⟨21876495177323941673103389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58337320472863844461609037 21876495177323941673103389)
          ·
            refine ⟨8203685691496478127413771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21876495177323941673103389 8203685691496478127413771)
            ·
              refine ⟨12305528537244717191120657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8203685691496478127413771 12305528537244717191120657)
              ·
                refine ⟨9229146402933537893340493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12305528537244717191120657 9229146402933537893340493)
                ·
                  refine ⟨3460929901100076710002685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9229146402933537893340493 3460929901100076710002685)
                  ·
                    refine ⟨1297848712912528766251007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3460929901100076710002685 1297848712912528766251007)
                    ·
                      rfl

theorem cell22_3791327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 3].length) (baseStart_3791327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791327 prefixEnd_3791327 := by exact prefixLift 3791327
  have htrace : WordTrace (prefixWord ++ tailWord_3791327) baseStart_3791327 baseEnd_3791327 := by
    simpa [prefixWord, tailWord_3791327, baseEnd_3791327] using wordTrace_append hprefix tailTrace_3791327
  have hstable : (prefixWord ++ tailWord_3791327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791327).length < 2 ^ (prefixWord ++ tailWord_3791327).sum := by decide
  have hdescent : baseEnd_3791327 < baseStart_3791327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791344 : List Nat := [2, 1, 1, 1, 3, 3, 4, 3, 1, 3]
def baseStart_3791344 : Nat := 118140960795 + 3791344 * 2 ^ 59
def prefixEnd_3791344 : Nat := 4983230072969 + 3 ^ 40 * 3791344 * 2
def baseEnd_3791344 : Nat := 1297854532359946388575955

theorem tailTrace_3791344 : CollatzResearch.WordTrace tailWord_3791344 prefixEnd_3791344 1297854532359946388575955 := by
  unfold tailWord_3791344
  simp only [CollatzResearch.WordTrace]
  refine ⟨69140837988307836424702543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92187783984410448566270057 69140837988307836424702543)
  ·
    refine ⟨103711256982461754637053815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69140837988307836424702543 103711256982461754637053815)
    ·
      refine ⟨155566885473692631955580723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103711256982461754637053815 155566885473692631955580723)
      ·
        refine ⟨233350328210538947933371085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155566885473692631955580723 233350328210538947933371085)
        ·
          refine ⟨87506373078952105475014157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233350328210538947933371085 87506373078952105475014157)
          ·
            refine ⟨32814889904607039553130309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87506373078952105475014157 32814889904607039553130309)
            ·
              refine ⟨6152791857113819916211933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32814889904607039553130309 6152791857113819916211933)
              ·
                refine ⟨2307296946417682468579475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6152791857113819916211933 2307296946417682468579475)
                ·
                  refine ⟨3460945419626523702869213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307296946417682468579475 3460945419626523702869213)
                  ·
                    refine ⟨1297854532359946388575955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3460945419626523702869213 1297854532359946388575955)
                    ·
                      rfl

theorem cell22_3791344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 1, 3].length) (baseStart_3791344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791344 prefixEnd_3791344 := by exact prefixLift 3791344
  have htrace : WordTrace (prefixWord ++ tailWord_3791344) baseStart_3791344 baseEnd_3791344 := by
    simpa [prefixWord, tailWord_3791344, baseEnd_3791344] using wordTrace_append hprefix tailTrace_3791344
  have hstable : (prefixWord ++ tailWord_3791344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791344).length < 2 ^ (prefixWord ++ tailWord_3791344).sum := by decide
  have hdescent : baseEnd_3791344 < baseStart_3791344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791374 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_3791374 : Nat := 118140960795 + 3791374 * 2 ^ 59
def prefixEnd_3791374 : Nat := 4983230072969 + 3 ^ 40 * 3791374 * 2
def baseEnd_3791374 : Nat := 432621600657678770108621

theorem tailTrace_3791374 : CollatzResearch.WordTrace tailWord_3791374 prefixEnd_3791374 432621600657678770108621 := by
  unfold tailWord_3791374
  simp only [CollatzResearch.WordTrace]
  refine ⟨17285346270813373496624647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92188513444337991981998117 17285346270813373496624647)
  ·
    refine ⟨25928019406220060244936971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17285346270813373496624647 25928019406220060244936971)
    ·
      refine ⟨38892029109330090367405457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25928019406220060244936971 38892029109330090367405457)
      ·
        refine ⟨29169021831997567775554093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38892029109330090367405457 29169021831997567775554093)
        ·
          refine ⟨10938383186999087915832785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29169021831997567775554093 10938383186999087915832785)
          ·
            refine ⟨8203787390249315936874589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10938383186999087915832785 8203787390249315936874589)
            ·
              refine ⟨3076420271343493476327971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8203787390249315936874589 3076420271343493476327971)
              ·
                refine ⟨4614630407015240214491957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076420271343493476327971 4614630407015240214491957)
                ·
                  refine ⟨432621600657678770108621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4614630407015240214491957 432621600657678770108621)
                  ·
                    rfl

theorem cell22_3791374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_3791374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791374 prefixEnd_3791374 := by exact prefixLift 3791374
  have htrace : WordTrace (prefixWord ++ tailWord_3791374) baseStart_3791374 baseEnd_3791374 := by
    simpa [prefixWord, tailWord_3791374, baseEnd_3791374] using wordTrace_append hprefix tailTrace_3791374
  have hstable : (prefixWord ++ tailWord_3791374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791374).length < 2 ^ (prefixWord ++ tailWord_3791374).sum := by decide
  have hdescent : baseEnd_3791374 < baseStart_3791374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791417 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 4, 3]
def baseStart_3791417 : Nat := 118140960795 + 3791417 * 2 ^ 59
def prefixEnd_3791417 : Nat := 4983230072969 + 3 ^ 40 * 3791417 * 2
def baseEnd_3791417 : Nat := 1297879521751798531500731

theorem tailTrace_3791417 : CollatzResearch.WordTrace tailWord_3791417 prefixEnd_3791417 1297879521751798531500731 := by
  unfold tailWord_3791417
  simp only [CollatzResearch.WordTrace]
  refine ⟨138284338505351206316812505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92189559003567470877875003 138284338505351206316812505)
  ·
    refine ⟨103713253879013404737609379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138284338505351206316812505 103713253879013404737609379)
    ·
      refine ⟨155569880818520107106414069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103713253879013404737609379 155569880818520107106414069)
      ·
        refine ⟨14584676326736260041226319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155569880818520107106414069 14584676326736260041226319)
        ·
          refine ⟨21877014490104390061839479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14584676326736260041226319 21877014490104390061839479)
          ·
            refine ⟨32815521735156585092759219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21877014490104390061839479 32815521735156585092759219)
            ·
              refine ⟨49223282602734877639138829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32815521735156585092759219 49223282602734877639138829)
              ·
                refine ⟨18458730976025579114677061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49223282602734877639138829 18458730976025579114677061)
                ·
                  refine ⟨3461012058004796084001949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18458730976025579114677061 3461012058004796084001949)
                  ·
                    refine ⟨1297879521751798531500731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461012058004796084001949 1297879521751798531500731)
                    ·
                      rfl

theorem cell22_3791417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 3].length) (baseStart_3791417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791417 prefixEnd_3791417 := by exact prefixLift 3791417
  have htrace : WordTrace (prefixWord ++ tailWord_3791417) baseStart_3791417 baseEnd_3791417 := by
    simpa [prefixWord, tailWord_3791417, baseEnd_3791417] using wordTrace_append hprefix tailTrace_3791417
  have hstable : (prefixWord ++ tailWord_3791417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791417).length < 2 ^ (prefixWord ++ tailWord_3791417).sum := by decide
  have hdescent : baseEnd_3791417 < baseStart_3791417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791434 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 2, 3]
def baseStart_3791434 : Nat := 118140960795 + 3791434 * 2 ^ 59
def prefixEnd_3791434 : Nat := 4983230072969 + 3 ^ 40 * 3791434 * 2
def baseEnd_3791434 : Nat := 1297885341199216153825679

theorem tailTrace_3791434 : CollatzResearch.WordTrace tailWord_3791434 prefixEnd_3791434 1297885341199216153825679 := by
  unfold tailWord_3791434
  simp only [CollatzResearch.WordTrace]
  refine ⟨34571239636572404555045339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92189972364193078813454237 34571239636572404555045339)
  ·
    refine ⟨51856859454858606832568009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34571239636572404555045339 51856859454858606832568009)
    ·
      refine ⟨38892644591143955124426007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51856859454858606832568009 38892644591143955124426007)
      ·
        refine ⟨58338966886715932686639011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38892644591143955124426007 58338966886715932686639011)
        ·
          refine ⟨87508450330073899029958517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58338966886715932686639011 87508450330073899029958517)
          ·
            refine ⟨8203917218444428034058611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87508450330073899029958517 8203917218444428034058611)
            ·
              refine ⟨12305875827666642051087917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8203917218444428034058611 12305875827666642051087917)
              ·
                refine ⟨4614703435374990769157969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12305875827666642051087917 4614703435374990769157969)
                ·
                  refine ⟨3461027576531243076868477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4614703435374990769157969 3461027576531243076868477)
                  ·
                    refine ⟨1297885341199216153825679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461027576531243076868477 1297885341199216153825679)
                    ·
                      rfl

theorem cell22_3791434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_3791434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791434 prefixEnd_3791434 := by exact prefixLift 3791434
  have htrace : WordTrace (prefixWord ++ tailWord_3791434) baseStart_3791434 baseEnd_3791434 := by
    simpa [prefixWord, tailWord_3791434, baseEnd_3791434] using wordTrace_append hprefix tailTrace_3791434
  have hstable : (prefixWord ++ tailWord_3791434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791434).length < 2 ^ (prefixWord ++ tailWord_3791434).sum := by decide
  have hdescent : baseEnd_3791434 < baseStart_3791434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791445 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_3791445 : Nat := 118140960795 + 3791445 * 2 ^ 59
def prefixEnd_3791445 : Nat := 4983230072969 + 3 ^ 40 * 3791445 * 2
def baseEnd_3791445 : Nat := 1297889106724015791800645

theorem tailTrace_3791445 : CollatzResearch.WordTrace tailWord_3791445 prefixEnd_3791445 1297889106724015791800645 := by
  unfold tailWord_3791445
  simp only [CollatzResearch.WordTrace]
  refine ⟨138285359749249767098831789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92190239832833178065887859 138285359749249767098831789)
  ·
    refine ⟨51857009905968662662061921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138285359749249767098831789 51857009905968662662061921)
    ·
      refine ⟨38892757429476496996546441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51857009905968662662061921 38892757429476496996546441)
      ·
        refine ⟨29169568072107372747409831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38892757429476496996546441 29169568072107372747409831)
        ·
          refine ⟨43754352108161059121114747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29169568072107372747409831 43754352108161059121114747)
          ·
            refine ⟨65631528162241588681672121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43754352108161059121114747 65631528162241588681672121)
            ·
              refine ⟨49223646121681191511254091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65631528162241588681672121 49223646121681191511254091)
              ·
                refine ⟨73835469182521787266881137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49223646121681191511254091 73835469182521787266881137)
                ·
                  refine ⟨55376601886891340450160853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73835469182521787266881137 55376601886891340450160853)
                  ·
                    refine ⟨1297889106724015791800645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55376601886891340450160853 1297889106724015791800645)
                    ·
                      rfl

theorem cell22_3791445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_3791445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791445 prefixEnd_3791445 := by exact prefixLift 3791445
  have htrace : WordTrace (prefixWord ++ tailWord_3791445) baseStart_3791445 baseEnd_3791445 := by
    simpa [prefixWord, tailWord_3791445, baseEnd_3791445] using wordTrace_append hprefix tailTrace_3791445
  have hstable : (prefixWord ++ tailWord_3791445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791445).length < 2 ^ (prefixWord ++ tailWord_3791445).sum := by decide
  have hdescent : baseEnd_3791445 < baseStart_3791445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791556 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_3791556 : Nat := 118140960795 + 3791556 * 2 ^ 59
def prefixEnd_3791556 : Nat := 4983230072969 + 3 ^ 40 * 3791556 * 2
def baseEnd_3791556 : Nat := 1297927104292448502275305

theorem tailTrace_3791556 : CollatzResearch.WordTrace tailWord_3791556 prefixEnd_3791556 1297927104292448502275305 := by
  unfold tailWord_3791556
  simp only [CollatzResearch.WordTrace]
  refine ⟨69144704125923816528061261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92192938834565088704081681 69144704125923816528061261)
  ·
    refine ⟨25929264047221431198022973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69144704125923816528061261 25929264047221431198022973)
    ·
      refine ⟨9723474017708036699258615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25929264047221431198022973 9723474017708036699258615)
      ·
        refine ⟨14585211026562055048887923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9723474017708036699258615 14585211026562055048887923)
        ·
          refine ⟨21877816539843082573331885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14585211026562055048887923 21877816539843082573331885)
          ·
            refine ⟨8204181202441155964999457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21877816539843082573331885 8204181202441155964999457)
            ·
              refine ⟨6153135901830866973749593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8204181202441155964999457 6153135901830866973749593)
              ·
                refine ⟨4614851926373150230312195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6153135901830866973749593 4614851926373150230312195)
                ·
                  refine ⟨6922277889559725345468293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614851926373150230312195 6922277889559725345468293)
                  ·
                    refine ⟨1297927104292448502275305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6922277889559725345468293 1297927104292448502275305)
                    ·
                      rfl

theorem cell22_3791556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_3791556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791556 prefixEnd_3791556 := by exact prefixLift 3791556
  have htrace : WordTrace (prefixWord ++ tailWord_3791556) baseStart_3791556 baseEnd_3791556 := by
    simpa [prefixWord, tailWord_3791556, baseEnd_3791556] using wordTrace_append hprefix tailTrace_3791556
  have hstable : (prefixWord ++ tailWord_3791556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791556).length < 2 ^ (prefixWord ++ tailWord_3791556).sum := by decide
  have hdescent : baseEnd_3791556 < baseStart_3791556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791631 : List Nat := [1, 1, 2, 1, 1, 1, 6, 5, 1, 3]
def baseStart_3791631 : Nat := 118140960795 + 3791631 * 2 ^ 59
def prefixEnd_3791631 : Nat := 4983230072969 + 3 ^ 40 * 3791631 * 2
def baseEnd_3791631 : Nat := 1297952778325173306650075

theorem tailTrace_3791631 : CollatzResearch.WordTrace tailWord_3791631 prefixEnd_3791631 1297952778325173306650075 := by
  unfold tailWord_3791631
  simp only [CollatzResearch.WordTrace]
  refine ⟨138292143726575920865102747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92194762484383947243401831 138292143726575920865102747)
  ·
    refine ⟨207438215589863881297654121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138292143726575920865102747 207438215589863881297654121)
    ·
      refine ⟨155578661692397910973240591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207438215589863881297654121 155578661692397910973240591)
      ·
        refine ⟨233367992538596866459860887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155578661692397910973240591 233367992538596866459860887)
        ·
          refine ⟨350051988807895299689791331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233367992538596866459860887 350051988807895299689791331)
          ·
            refine ⟨525077983211842949534686997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350051988807895299689791331 525077983211842949534686997)
            ·
              refine ⟨24613030463055138259438453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 525077983211842949534686997 24613030463055138259438453)
              ·
                refine ⟨2307471605911419211822355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24613030463055138259438453 2307471605911419211822355)
                ·
                  refine ⟨3461207408867128817733533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307471605911419211822355 3461207408867128817733533)
                  ·
                    refine ⟨1297952778325173306650075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461207408867128817733533 1297952778325173306650075)
                    ·
                      rfl

theorem cell22_3791631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 1, 3].length) (baseStart_3791631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791631 prefixEnd_3791631 := by exact prefixLift 3791631
  have htrace : WordTrace (prefixWord ++ tailWord_3791631) baseStart_3791631 baseEnd_3791631 := by
    simpa [prefixWord, tailWord_3791631, baseEnd_3791631] using wordTrace_append hprefix tailTrace_3791631
  have hstable : (prefixWord ++ tailWord_3791631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791631).length < 2 ^ (prefixWord ++ tailWord_3791631).sum := by decide
  have hdescent : baseEnd_3791631 < baseStart_3791631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791644 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 5]
def baseStart_3791644 : Nat := 118140960795 + 3791644 * 2 ^ 59
def prefixEnd_3791644 : Nat := 4983230072969 + 3 ^ 40 * 3791644 * 2
def baseEnd_3791644 : Nat := 432652409496948535358345

theorem tailTrace_3791644 : CollatzResearch.WordTrace tailWord_3791644 prefixEnd_3791644 432652409496948535358345 := by
  unfold tailWord_3791644
  simp only [CollatzResearch.WordTrace]
  refine ⟨69146308937764412042662993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92195078583685882723550657 69146308937764412042662993)
  ·
    refine ⟨51859731703323309031997245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69146308937764412042662993 51859731703323309031997245)
    ·
      refine ⟨19447399388746240886998967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51859731703323309031997245 19447399388746240886998967)
      ·
        refine ⟨29171099083119361330498451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19447399388746240886998967 29171099083119361330498451)
        ·
          refine ⟨43756648624679041995747677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29171099083119361330498451 43756648624679041995747677)
          ·
            refine ⟨16408743234254640748405379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43756648624679041995747677 16408743234254640748405379)
            ·
              refine ⟨24613114851381961122608069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16408743234254640748405379 24613114851381961122608069)
              ·
                refine ⟨4614959034634117710489013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24613114851381961122608069 4614959034634117710489013)
                ·
                  refine ⟨432652409496948535358345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4614959034634117710489013 432652409496948535358345)
                  ·
                    rfl

theorem cell22_3791644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_3791644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791644 prefixEnd_3791644 := by exact prefixLift 3791644
  have htrace : WordTrace (prefixWord ++ tailWord_3791644) baseStart_3791644 baseEnd_3791644 := by
    simpa [prefixWord, tailWord_3791644, baseEnd_3791644] using wordTrace_append hprefix tailTrace_3791644
  have hstable : (prefixWord ++ tailWord_3791644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791644).length < 2 ^ (prefixWord ++ tailWord_3791644).sum := by decide
  have hdescent : baseEnd_3791644 < baseStart_3791644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791648 : List Nat := [2, 1, 1, 5, 1, 3, 1, 4, 1, 3]
def baseStart_3791648 : Nat := 118140960795 + 3791648 * 2 ^ 59
def prefixEnd_3791648 : Nat := 4983230072969 + 3 ^ 40 * 3791648 * 2
def baseEnd_3791648 : Nat := 1297958597772590928975023

theorem tailTrace_3791648 : CollatzResearch.WordTrace tailWord_3791648 prefixEnd_3791648 1297958597772590928975023 := by
  unfold tailWord_3791648
  simp only [CollatzResearch.WordTrace]
  refine ⟨69146381883757166384235799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92195175845009555178981065 69146381883757166384235799)
  ·
    refine ⟨103719572825635749576353699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69146381883757166384235799 103719572825635749576353699)
    ·
      refine ⟨155579359238453624364530549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103719572825635749576353699 155579359238453624364530549)
      ·
        refine ⟨14585564928605027284174739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155579359238453624364530549 14585564928605027284174739)
        ·
          refine ⟨21878347392907540926262109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14585564928605027284174739 21878347392907540926262109)
          ·
            refine ⟨8204380272340327847348291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21878347392907540926262109 8204380272340327847348291)
            ·
              refine ⟨12306570408510491771022437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8204380272340327847348291 12306570408510491771022437)
              ·
                refine ⟨2307481951595717207066707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12306570408510491771022437 2307481951595717207066707)
                ·
                  refine ⟨3461222927393575810600061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307481951595717207066707 3461222927393575810600061)
                  ·
                    refine ⟨1297958597772590928975023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461222927393575810600061 1297958597772590928975023)
                    ·
                      rfl

theorem cell22_3791648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 1, 3].length) (baseStart_3791648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791648 prefixEnd_3791648 := by exact prefixLift 3791648
  have htrace : WordTrace (prefixWord ++ tailWord_3791648) baseStart_3791648 baseEnd_3791648 := by
    simpa [prefixWord, tailWord_3791648, baseEnd_3791648] using wordTrace_append hprefix tailTrace_3791648
  have hstable : (prefixWord ++ tailWord_3791648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791648).length < 2 ^ (prefixWord ++ tailWord_3791648).sum := by decide
  have hdescent : baseEnd_3791648 < baseStart_3791648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791706 : List Nat := [3, 1, 1, 2, 1, 4, 2, 4, 4]
def baseStart_3791706 : Nat := 118140960795 + 3791706 * 2 ^ 59
def prefixEnd_3791706 : Nat := 4983230072969 + 3 ^ 40 * 3791706 * 2
def baseEnd_3791706 : Nat := 432659484119299370341615

theorem tailTrace_3791706 : CollatzResearch.WordTrace tailWord_3791706 prefixEnd_3791706 432659484119299370341615 := by
  unfold tailWord_3791706
  simp only [CollatzResearch.WordTrace]
  refine ⟨34573719800326052168520743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92196586134202805782721981 34573719800326052168520743)
  ·
    refine ⟨51860579700489078252781115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34573719800326052168520743 51860579700489078252781115)
    ·
      refine ⟨77790869550733617379171673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51860579700489078252781115 77790869550733617379171673)
      ·
        refine ⟨58343152163050213034378755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77790869550733617379171673 58343152163050213034378755)
        ·
          refine ⟨87514728244575319551568133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58343152163050213034378755 87514728244575319551568133)
          ·
            refine ⟨16409011545857872415919025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87514728244575319551568133 16409011545857872415919025)
            ·
              refine ⟨12306758659393404311939269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16409011545857872415919025 12306758659393404311939269)
              ·
                refine ⟨2307517248636263308488613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12306758659393404311939269 2307517248636263308488613)
                ·
                  refine ⟨432659484119299370341615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2307517248636263308488613 432659484119299370341615)
                  ·
                    rfl

theorem cell22_3791706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_3791706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791706 prefixEnd_3791706 := by exact prefixLift 3791706
  have htrace : WordTrace (prefixWord ++ tailWord_3791706) baseStart_3791706 baseEnd_3791706 := by
    simpa [prefixWord, tailWord_3791706, baseEnd_3791706] using wordTrace_append hprefix tailTrace_3791706
  have hstable : (prefixWord ++ tailWord_3791706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791706).length < 2 ^ (prefixWord ++ tailWord_3791706).sum := by decide
  have hdescent : baseEnd_3791706 < baseStart_3791706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791719 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3791719 : Nat := 118140960795 + 3791719 * 2 ^ 59
def prefixEnd_3791719 : Nat := 4983230072969 + 3 ^ 40 * 3791719 * 2
def baseEnd_3791719 : Nat := 1297982902523570410449805

theorem tailTrace_3791719 : CollatzResearch.WordTrace tailWord_3791719 prefixEnd_3791719 1297982902523570410449805 := by
  unfold tailWord_3791719
  simp only [CollatzResearch.WordTrace]
  refine ⟨138295353350257111894306211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92196902233504741262870807 138295353350257111894306211)
  ·
    refine ⟨207443030025385667841459317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138295353350257111894306211 207443030025385667841459317)
    ·
      refine ⟨19447784064879906360136811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207443030025385667841459317 19447784064879906360136811)
      ·
        refine ⟨29171676097319859540205217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19447784064879906360136811 29171676097319859540205217)
        ·
          refine ⟨21878757072989894655153913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29171676097319859540205217 21878757072989894655153913)
          ·
            refine ⟨16409067804742420991365435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21878757072989894655153913 16409067804742420991365435)
            ·
              refine ⟨24613601707113631487048153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16409067804742420991365435 24613601707113631487048153)
              ·
                refine ⟨18460201280335223615286115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24613601707113631487048153 18460201280335223615286115)
                ·
                  refine ⟨27690301920502835422929173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18460201280335223615286115 27690301920502835422929173)
                  ·
                    refine ⟨1297982902523570410449805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27690301920502835422929173 1297982902523570410449805)
                    ·
                      rfl

theorem cell22_3791719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3791719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791719 prefixEnd_3791719 := by exact prefixLift 3791719
  have htrace : WordTrace (prefixWord ++ tailWord_3791719) baseStart_3791719 baseEnd_3791719 := by
    simpa [prefixWord, tailWord_3791719, baseEnd_3791719] using wordTrace_append hprefix tailTrace_3791719
  have hstable : (prefixWord ++ tailWord_3791719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791719).length < 2 ^ (prefixWord ++ tailWord_3791719).sum := by decide
  have hdescent : baseEnd_3791719 < baseStart_3791719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791772 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 2, 3]
def baseStart_3791772 : Nat := 118140960795 + 3791772 * 2 ^ 59
def prefixEnd_3791772 : Nat := 4983230072969 + 3 ^ 40 * 3791772 * 2
def baseEnd_3791772 : Nat := 1298001045506695938874643

theorem tailTrace_3791772 : CollatzResearch.WordTrace tailWord_3791772 prefixEnd_3791772 1298001045506695938874643 := by
  unfold tailWord_3791772
  simp only [CollatzResearch.WordTrace]
  refine ⟨69148643209532550972992785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92198190946043401297323713 69148643209532550972992785)
  ·
    refine ⟨51861482407149413229744589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69148643209532550972992785 51861482407149413229744589)
    ·
      refine ⟨19448055902681029961154221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51861482407149413229744589 19448055902681029961154221)
      ·
        refine ⟨7293020963505386235432833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19448055902681029961154221 7293020963505386235432833)
        ·
          refine ⟨5469765722629039676574625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7293020963505386235432833 5469765722629039676574625)
          ·
            refine ⟨4102324291971779757430969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5469765722629039676574625 4102324291971779757430969)
            ·
              refine ⟨3076743218978834818073227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4102324291971779757430969 3076743218978834818073227)
              ·
                refine ⟨4615114828468252227109841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076743218978834818073227 4615114828468252227109841)
                ·
                  refine ⟨3461336121351189170332381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4615114828468252227109841 3461336121351189170332381)
                  ·
                    refine ⟨1298001045506695938874643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461336121351189170332381 1298001045506695938874643)
                    ·
                      rfl

theorem cell22_3791772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_3791772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791772 prefixEnd_3791772 := by exact prefixLift 3791772
  have htrace : WordTrace (prefixWord ++ tailWord_3791772) baseStart_3791772 baseEnd_3791772 := by
    simpa [prefixWord, tailWord_3791772, baseEnd_3791772] using wordTrace_append hprefix tailTrace_3791772
  have hstable : (prefixWord ++ tailWord_3791772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791772).length < 2 ^ (prefixWord ++ tailWord_3791772).sum := by decide
  have hdescent : baseEnd_3791772 < baseStart_3791772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791794 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_3791794 : Nat := 118140960795 + 3791794 * 2 ^ 59
def prefixEnd_3791794 : Nat := 4983230072969 + 3 ^ 40 * 3791794 * 2
def baseEnd_3791794 : Nat := 1298008576556295214824575

theorem tailTrace_3791794 : CollatzResearch.WordTrace tailWord_3791794 prefixEnd_3791794 1298008576556295214824575 := by
  unfold tailWord_3791794
  simp only [CollatzResearch.WordTrace]
  refine ⟨34574522206246349925821609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92198725883323599802190957 34574522206246349925821609)
  ·
    refine ⟨25930891654684762444366207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34574522206246349925821609 25930891654684762444366207)
    ·
      refine ⟨38896337482027143666549311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25930891654684762444366207 38896337482027143666549311)
      ·
        refine ⟨58344506223040715499823967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38896337482027143666549311 58344506223040715499823967)
        ·
          refine ⟨87516759334561073249735951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58344506223040715499823967 87516759334561073249735951)
          ·
            refine ⟨131275139001841609874603927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87516759334561073249735951 131275139001841609874603927)
            ·
              refine ⟨196912708502762414811905891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131275139001841609874603927 196912708502762414811905891)
              ·
                refine ⟨295369062754143622217858837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196912708502762414811905891 295369062754143622217858837)
                ·
                  refine ⟨13845424816600482291462133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 295369062754143622217858837 13845424816600482291462133)
                  ·
                    refine ⟨1298008576556295214824575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13845424816600482291462133 1298008576556295214824575)
                    ·
                      rfl

theorem cell22_3791794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_3791794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791794 prefixEnd_3791794 := by exact prefixLift 3791794
  have htrace : WordTrace (prefixWord ++ tailWord_3791794) baseStart_3791794 baseEnd_3791794 := by
    simpa [prefixWord, tailWord_3791794, baseEnd_3791794] using wordTrace_append hprefix tailTrace_3791794
  have hstable : (prefixWord ++ tailWord_3791794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791794).length < 2 ^ (prefixWord ++ tailWord_3791794).sum := by decide
  have hdescent : baseEnd_3791794 < baseStart_3791794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791824 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 6]
def baseStart_3791824 : Nat := 118140960795 + 3791824 * 2 ^ 59
def prefixEnd_3791824 : Nat := 4983230072969 + 3 ^ 40 * 3791824 * 2
def baseEnd_3791824 : Nat := 432672948723128378858161

theorem tailTrace_3791824 : CollatzResearch.WordTrace tailWord_3791824 prefixEnd_3791824 432672948723128378858161 := by
  unfold tailWord_3791824
  simp only [CollatzResearch.WordTrace]
  refine ⟨69149591507438357413439263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92199455343251143217919017 69149591507438357413439263)
  ·
    refine ⟨103724387261157536120158895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69149591507438357413439263 103724387261157536120158895)
    ·
      refine ⟨155586580891736304180238343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103724387261157536120158895 155586580891736304180238343)
      ·
        refine ⟨233379871337604456270357515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155586580891736304180238343 233379871337604456270357515)
        ·
          refine ⟨350069807006406684405536273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233379871337604456270357515 350069807006406684405536273)
          ·
            refine ⟨262552355254805013304152205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350069807006406684405536273 262552355254805013304152205)
            ·
              refine ⟨98457133220551879989057077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262552355254805013304152205 98457133220551879989057077)
              ·
                refine ⟨9230356239426738748974101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98457133220551879989057077 9230356239426738748974101)
                ·
                  refine ⟨432672948723128378858161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9230356239426738748974101 432672948723128378858161)
                  ·
                    rfl

theorem cell22_3791824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_3791824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791824 prefixEnd_3791824 := by exact prefixLift 3791824
  have htrace : WordTrace (prefixWord ++ tailWord_3791824) baseStart_3791824 baseEnd_3791824 := by
    simpa [prefixWord, tailWord_3791824, baseEnd_3791824] using wordTrace_append hprefix tailTrace_3791824
  have hstable : (prefixWord ++ tailWord_3791824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791824).length < 2 ^ (prefixWord ++ tailWord_3791824).sum := by decide
  have hdescent : baseEnd_3791824 < baseStart_3791824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791856 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 4, 3]
def baseStart_3791856 : Nat := 118140960795 + 3791856 * 2 ^ 59
def prefixEnd_3791856 : Nat := 4983230072969 + 3 ^ 40 * 3791856 * 2
def baseEnd_3791856 : Nat := 1298029800423347719774385

theorem tailTrace_3791856 : CollatzResearch.WordTrace tailWord_3791856 prefixEnd_3791856 1298029800423347719774385 := by
  unfold tailWord_3791856
  simp only [CollatzResearch.WordTrace]
  refine ⟨69150175075380392146021711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92200233433840522861362281 69150175075380392146021711)
  ·
    refine ⟨103725262613070588219032567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69150175075380392146021711 103725262613070588219032567)
    ·
      refine ⟨155587893919605882328548851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103725262613070588219032567 155587893919605882328548851)
      ·
        refine ⟨233381840879408823492823277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155587893919605882328548851 233381840879408823492823277)
        ·
          refine ⟨87518190329778308809808729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233381840879408823492823277 87518190329778308809808729)
          ·
            refine ⟨65638642747333731607356547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87518190329778308809808729 65638642747333731607356547)
            ·
              refine ⟨98457964121000597411034821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65638642747333731607356547 98457964121000597411034821)
              ·
                refine ⟨18460868272687612014569029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98457964121000597411034821 18460868272687612014569029)
                ·
                  refine ⟨3461412801128927252731693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18460868272687612014569029 3461412801128927252731693)
                  ·
                    refine ⟨1298029800423347719774385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461412801128927252731693 1298029800423347719774385)
                    ·
                      rfl

theorem cell22_3791856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4, 3].length) (baseStart_3791856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791856 prefixEnd_3791856 := by exact prefixLift 3791856
  have htrace : WordTrace (prefixWord ++ tailWord_3791856) baseStart_3791856 baseEnd_3791856 := by
    simpa [prefixWord, tailWord_3791856, baseEnd_3791856] using wordTrace_append hprefix tailTrace_3791856
  have hstable : (prefixWord ++ tailWord_3791856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791856).length < 2 ^ (prefixWord ++ tailWord_3791856).sum := by decide
  have hdescent : baseEnd_3791856 < baseStart_3791856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791873 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 4, 3]
def baseStart_3791873 : Nat := 118140960795 + 3791873 * 2 ^ 59
def prefixEnd_3791873 : Nat := 4983230072969 + 3 ^ 40 * 3791873 * 2
def baseEnd_3791873 : Nat := 1298035619870765342099333

theorem tailTrace_3791873 : CollatzResearch.WordTrace tailWord_3791873 prefixEnd_3791873 1298035619870765342099333 := by
  unfold tailWord_3791873
  simp only [CollatzResearch.WordTrace]
  refine ⟨138300970191699196195412273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92200646794466130796941515 138300970191699196195412273)
  ·
    refine ⟨103725727643774397146559205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138300970191699196195412273 103725727643774397146559205)
    ·
      refine ⟨19448573933207699464979851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103725727643774397146559205 19448573933207699464979851)
      ·
        refine ⟨29172860899811549197469777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19448573933207699464979851 29172860899811549197469777)
        ·
          refine ⟨21879645674858661898102333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29172860899811549197469777 21879645674858661898102333)
          ·
            refine ⟨8204867128071998211788375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21879645674858661898102333 8204867128071998211788375)
            ·
              refine ⟨12307300692107997317682563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8204867128071998211788375 12307300692107997317682563)
              ·
                refine ⟨18460951038161995976523845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307300692107997317682563 18460951038161995976523845)
                ·
                  refine ⟨3461428319655374245598221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18460951038161995976523845 3461428319655374245598221)
                  ·
                    refine ⟨1298035619870765342099333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461428319655374245598221 1298035619870765342099333)
                    ·
                      rfl

theorem cell22_3791873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_3791873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791873 prefixEnd_3791873 := by exact prefixLift 3791873
  have htrace : WordTrace (prefixWord ++ tailWord_3791873) baseStart_3791873 baseEnd_3791873 := by
    simpa [prefixWord, tailWord_3791873, baseEnd_3791873] using wordTrace_append hprefix tailTrace_3791873
  have hstable : (prefixWord ++ tailWord_3791873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791873).length < 2 ^ (prefixWord ++ tailWord_3791873).sum := by decide
  have hdescent : baseEnd_3791873 < baseStart_3791873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791899 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 3, 8]
def baseStart_3791899 : Nat := 118140960795 + 3791899 * 2 ^ 59
def prefixEnd_3791899 : Nat := 4983230072969 + 3 ^ 40 * 3791899 * 2
def baseEnd_3791899 : Nat := 1298044520202109940949253

theorem tailTrace_3791899 : CollatzResearch.WordTrace tailWord_3791899 prefixEnd_3791899 1298044520202109940949253 := by
  unfold tailWord_3791899
  simp only [CollatzResearch.WordTrace]
  refine ⟨138301918489605002635858751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92201278993070001757239167 138301918489605002635858751)
  ·
    refine ⟨207452877734407503953788127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138301918489605002635858751 207452877734407503953788127)
    ·
      refine ⟨311179316601611255930682191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207452877734407503953788127 311179316601611255930682191)
      ·
        refine ⟨466768974902416883896023287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311179316601611255930682191 466768974902416883896023287)
        ·
          refine ⟨700153462353625325844034931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466768974902416883896023287 700153462353625325844034931)
          ·
            refine ⟨1050230193530437988766052397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700153462353625325844034931 1050230193530437988766052397)
            ·
              refine ⟨393836322573914245787269649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1050230193530437988766052397 393836322573914245787269649)
              ·
                refine ⟨295377241930435684340452237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393836322573914245787269649 295377241930435684340452237)
                ·
                  refine ⟨110766465723913381627669589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295377241930435684340452237 110766465723913381627669589)
                  ·
                    refine ⟨1298044520202109940949253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110766465723913381627669589 1298044520202109940949253)
                    ·
                      rfl

theorem cell22_3791899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_3791899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791899 prefixEnd_3791899 := by exact prefixLift 3791899
  have htrace : WordTrace (prefixWord ++ tailWord_3791899) baseStart_3791899 baseEnd_3791899 := by
    simpa [prefixWord, tailWord_3791899, baseEnd_3791899] using wordTrace_append hprefix tailTrace_3791899
  have hstable : (prefixWord ++ tailWord_3791899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791899).length < 2 ^ (prefixWord ++ tailWord_3791899).sum := by decide
  have hdescent : baseEnd_3791899 < baseStart_3791899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791903 : List Nat := [1, 1, 2, 4, 1, 5, 2, 6]
def baseStart_3791903 : Nat := 118140960795 + 3791903 * 2 ^ 59
def prefixEnd_3791903 : Nat := 4983230072969 + 3 ^ 40 * 3791903 * 2
def baseEnd_3791903 : Nat := 144227321053761695983249

theorem tailTrace_3791903 : CollatzResearch.WordTrace tailWord_3791903 prefixEnd_3791903 144227321053761695983249 := by
  unfold tailWord_3791903
  simp only [CollatzResearch.WordTrace]
  refine ⟨138302064381590511319004363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92201376254393674212669575 138302064381590511319004363)
  ·
    refine ⟨207453096572385766978506545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138302064381590511319004363 207453096572385766978506545)
    ·
      refine ⟨155589822429289325233879909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207453096572385766978506545 155589822429289325233879909)
      ·
        refine ⟨29173091705491748481352483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155589822429289325233879909 29173091705491748481352483)
        ·
          refine ⟨43759637558237622722028725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29173091705491748481352483 43759637558237622722028725)
          ·
            refine ⟨4102466021084777130190193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43759637558237622722028725 4102466021084777130190193)
            ·
              refine ⟨3076849515813582847642645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4102466021084777130190193 3076849515813582847642645)
              ·
                refine ⟨144227321053761695983249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3076849515813582847642645 144227321053761695983249)
                ·
                  rfl

theorem cell22_3791903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 6].length) (baseStart_3791903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791903 prefixEnd_3791903 := by exact prefixLift 3791903
  have htrace : WordTrace (prefixWord ++ tailWord_3791903) baseStart_3791903 baseEnd_3791903 := by
    simpa [prefixWord, tailWord_3791903, baseEnd_3791903] using wordTrace_append hprefix tailTrace_3791903
  have hstable : (prefixWord ++ tailWord_3791903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791903).length < 2 ^ (prefixWord ++ tailWord_3791903).sum := by decide
  have hdescent : baseEnd_3791903 < baseStart_3791903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791946 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_3791946 : Nat := 118140960795 + 3791946 * 2 ^ 59
def prefixEnd_3791946 : Nat := 4983230072969 + 3 ^ 40 * 3791946 * 2
def baseEnd_3791946 : Nat := 1298060609262617485024109

theorem tailTrace_3791946 : CollatzResearch.WordTrace tailWord_3791946 prefixEnd_3791946 1298060609262617485024109 := by
  unfold tailWord_3791946
  simp only [CollatzResearch.WordTrace]
  refine ⟨34575908180108682415704923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92202421813623153108546461 34575908180108682415704923)
  ·
    refine ⟨51863862270163023623557385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34575908180108682415704923 51863862270163023623557385)
    ·
      refine ⟨38897896702622267717668039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51863862270163023623557385 38897896702622267717668039)
      ·
        refine ⟨58346845053933401576502059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38897896702622267717668039 58346845053933401576502059)
        ·
          refine ⟨87520267580900102364753089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58346845053933401576502059 87520267580900102364753089)
          ·
            refine ⟨65640200685675076773564817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87520267580900102364753089 65640200685675076773564817)
            ·
              refine ⟨49230150514256307580173613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65640200685675076773564817 49230150514256307580173613)
              ·
                refine ⟨18461306442846115342565105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49230150514256307580173613 18461306442846115342565105)
                ·
                  refine ⟨13845979832134586506923829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18461306442846115342565105 13845979832134586506923829)
                  ·
                    refine ⟨1298060609262617485024109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13845979832134586506923829 1298060609262617485024109)
                    ·
                      rfl

theorem cell22_3791946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_3791946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791946 prefixEnd_3791946 := by exact prefixLift 3791946
  have htrace : WordTrace (prefixWord ++ tailWord_3791946) baseStart_3791946 baseEnd_3791946 := by
    simpa [prefixWord, tailWord_3791946, baseEnd_3791946] using wordTrace_append hprefix tailTrace_3791946
  have hstable : (prefixWord ++ tailWord_3791946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791946).length < 2 ^ (prefixWord ++ tailWord_3791946).sum := by decide
  have hdescent : baseEnd_3791946 < baseStart_3791946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3791991 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 3, 5]
def baseStart_3791991 : Nat := 118140960795 + 3791991 * 2 ^ 59
def prefixEnd_3791991 : Nat := 4983230072969 + 3 ^ 40 * 3791991 * 2
def baseEnd_3791991 : Nat := 1298076013682252367648971

theorem tailTrace_3791991 : CollatzResearch.WordTrace tailWord_3791991 prefixEnd_3791991 1298076013682252367648971 := by
  unfold tailWord_3791991
  simp only [CollatzResearch.WordTrace]
  refine ⟨138305274005271702348207827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92203516003514468232138551 138305274005271702348207827)
  ·
    refine ⟨207457911007907553522311741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138305274005271702348207827 207457911007907553522311741)
    ·
      refine ⟨77796716627965332570866903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207457911007907553522311741 77796716627965332570866903)
      ·
        refine ⟨116695074941947998856300355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77796716627965332570866903 116695074941947998856300355)
        ·
          refine ⟨175042612412921998284450533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116695074941947998856300355 175042612412921998284450533)
          ·
            refine ⟨32820489827422874678334475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175042612412921998284450533 32820489827422874678334475)
            ·
              refine ⟨49230734741134312017501713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32820489827422874678334475 49230734741134312017501713)
              ·
                refine ⟨36923051055850734013126285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49230734741134312017501713 36923051055850734013126285)
                ·
                  refine ⟨13846144145944025254922357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36923051055850734013126285 13846144145944025254922357)
                  ·
                    refine ⟨1298076013682252367648971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13846144145944025254922357 1298076013682252367648971)
                    ·
                      rfl

theorem cell22_3791991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_3791991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3791991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3791991 prefixEnd_3791991 := by exact prefixLift 3791991
  have htrace : WordTrace (prefixWord ++ tailWord_3791991) baseStart_3791991 baseEnd_3791991 := by
    simpa [prefixWord, tailWord_3791991, baseEnd_3791991] using wordTrace_append hprefix tailTrace_3791991
  have hstable : (prefixWord ++ tailWord_3791991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3791991).length < 2 ^ (prefixWord ++ tailWord_3791991).sum := by decide
  have hdescent : baseEnd_3791991 < baseStart_3791991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3791991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792023 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 1, 6]
def baseStart_3792023 : Nat := 118140960795 + 3792023 * 2 ^ 59
def prefixEnd_3792023 : Nat := 4983230072969 + 3 ^ 40 * 3792023 * 2
def baseEnd_3792023 : Nat := 1298086967936214950848873

theorem tailTrace_3792023 : CollatzResearch.WordTrace tailWord_3792023 prefixEnd_3792023 1298086967936214950848873 := by
  unfold tailWord_3792023
  simp only [CollatzResearch.WordTrace]
  refine ⟨138306441141155771813372723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92204294094103847875581815 138306441141155771813372723)
  ·
    refine ⟨207459661711733657720059085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138306441141155771813372723 207459661711733657720059085)
    ·
      refine ⟨77797373141900121645022157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207459661711733657720059085 77797373141900121645022157)
      ·
        refine ⟨29174014928212545616883309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77797373141900121645022157 29174014928212545616883309)
        ·
          refine ⟨10940255598079704606331241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29174014928212545616883309 10940255598079704606331241)
          ·
            refine ⟨8205191698559778454748431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10940255598079704606331241 8205191698559778454748431)
            ·
              refine ⟨12307787547839667682122647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8205191698559778454748431 12307787547839667682122647)
              ·
                refine ⟨18461681321759501523183971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307787547839667682122647 18461681321759501523183971)
                ·
                  refine ⟨27692521982639252284775957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18461681321759501523183971 27692521982639252284775957)
                  ·
                    refine ⟨1298086967936214950848873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27692521982639252284775957 1298086967936214950848873)
                    ·
                      rfl

theorem cell22_3792023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_3792023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792023 prefixEnd_3792023 := by exact prefixLift 3792023
  have htrace : WordTrace (prefixWord ++ tailWord_3792023) baseStart_3792023 baseEnd_3792023 := by
    simpa [prefixWord, tailWord_3792023, baseEnd_3792023] using wordTrace_append hprefix tailTrace_3792023
  have hstable : (prefixWord ++ tailWord_3792023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792023).length < 2 ^ (prefixWord ++ tailWord_3792023).sum := by decide
  have hdescent : baseEnd_3792023 < baseStart_3792023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792042 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3792042 : Nat := 118140960795 + 3792042 * 2 ^ 59
def prefixEnd_3792042 : Nat := 4983230072969 + 3 ^ 40 * 3792042 * 2
def baseEnd_3792042 : Nat := 1298093472024505234623815

theorem tailTrace_3792042 : CollatzResearch.WordTrace tailWord_3792042 prefixEnd_3792042 1298093472024505234623815 := by
  unfold tailWord_3792042
  simp only [CollatzResearch.WordTrace]
  refine ⟨34576783532021734514578595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92204756085391292038876253 34576783532021734514578595)
  ·
    refine ⟨51865175298032601771867893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34576783532021734514578595 51865175298032601771867893)
    ·
      refine ⟨4862360184190556416112615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51865175298032601771867893 4862360184190556416112615)
      ·
        refine ⟨7293540276285834624168923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4862360184190556416112615 7293540276285834624168923)
        ·
          refine ⟨10940310414428751936253385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7293540276285834624168923 10940310414428751936253385)
          ·
            refine ⟨8205232810821563952190039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10940310414428751936253385 8205232810821563952190039)
            ·
              refine ⟨12307849216232345928285059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8205232810821563952190039 12307849216232345928285059)
              ·
                refine ⟨18461773824348518892427589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307849216232345928285059 18461773824348518892427589)
                ·
                  refine ⟨3461582592065347292330173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18461773824348518892427589 3461582592065347292330173)
                  ·
                    refine ⟨1298093472024505234623815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461582592065347292330173 1298093472024505234623815)
                    ·
                      rfl

theorem cell22_3792042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3792042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792042 prefixEnd_3792042 := by exact prefixLift 3792042
  have htrace : WordTrace (prefixWord ++ tailWord_3792042) baseStart_3792042 baseEnd_3792042 := by
    simpa [prefixWord, tailWord_3792042, baseEnd_3792042] using wordTrace_append hprefix tailTrace_3792042
  have hstable : (prefixWord ++ tailWord_3792042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792042).length < 2 ^ (prefixWord ++ tailWord_3792042).sum := by decide
  have hdescent : baseEnd_3792042 < baseStart_3792042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792051 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 1, 8]
def baseStart_3792051 : Nat := 118140960795 + 3792051 * 2 ^ 59
def prefixEnd_3792051 : Nat := 4983230072969 + 3 ^ 40 * 3792051 * 2
def baseEnd_3792051 : Nat := 1298096552908432211148787

theorem tailTrace_3792051 : CollatzResearch.WordTrace tailWord_3792051 prefixEnd_3792051 1298096552908432211148787 := by
  unfold tailWord_3792051
  simp only [CollatzResearch.WordTrace]
  refine ⟨138307462385054332595392007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92204974923369555063594671 138307462385054332595392007)
  ·
    refine ⟨207461193577581498893088011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138307462385054332595392007 207461193577581498893088011)
    ·
      refine ⟨311191790366372248339632017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207461193577581498893088011 311191790366372248339632017)
      ·
        refine ⟨233393842774779186254724013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311191790366372248339632017 233393842774779186254724013)
        ·
          refine ⟨87522691040542194845521505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233393842774779186254724013 87522691040542194845521505)
          ·
            refine ⟨65642018280406646134141129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87522691040542194845521505 65642018280406646134141129)
            ·
              refine ⟨49231513710304984600605847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65642018280406646134141129 49231513710304984600605847)
              ·
                refine ⟨73847270565457476900908771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49231513710304984600605847 73847270565457476900908771)
                ·
                  refine ⟨110770905848186215351363157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73847270565457476900908771 110770905848186215351363157)
                  ·
                    refine ⟨1298096552908432211148787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110770905848186215351363157 1298096552908432211148787)
                    ·
                      rfl

theorem cell22_3792051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_3792051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792051 prefixEnd_3792051 := by exact prefixLift 3792051
  have htrace : WordTrace (prefixWord ++ tailWord_3792051) baseStart_3792051 baseEnd_3792051 := by
    simpa [prefixWord, tailWord_3792051, baseEnd_3792051] using wordTrace_append hprefix tailTrace_3792051
  have hstable : (prefixWord ++ tailWord_3792051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792051).length < 2 ^ (prefixWord ++ tailWord_3792051).sum := by decide
  have hdescent : baseEnd_3792051 < baseStart_3792051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792087 : List Nat := [1, 1, 3, 2, 1, 2, 5, 3, 1, 3]
def baseStart_3792087 : Nat := 118140960795 + 3792087 * 2 ^ 59
def prefixEnd_3792087 : Nat := 4983230072969 + 3 ^ 40 * 3792087 * 2
def baseEnd_3792087 : Nat := 1298108876444140117248677

theorem tailTrace_3792087 : CollatzResearch.WordTrace tailWord_3792087 prefixEnd_3792087 1298108876444140117248677 := by
  unfold tailWord_3792087
  simp only [CollatzResearch.WordTrace]
  refine ⟨138308775412923910743702515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92205850275282607162468343 138308775412923910743702515)
  ·
    refine ⟨207463163119385866115553773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138308775412923910743702515 207463163119385866115553773)
    ·
      refine ⟨77798686169769699793332665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207463163119385866115553773 77798686169769699793332665)
      ·
        refine ⟨58349014627327274844999499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77798686169769699793332665 58349014627327274844999499)
        ·
          refine ⟨87523521940990912267499249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58349014627327274844999499 87523521940990912267499249)
          ·
            refine ⟨65642641455743184200624437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87523521940990912267499249 65642641455743184200624437)
            ·
              refine ⟨6153997636475923518808541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65642641455743184200624437 6153997636475923518808541)
              ·
                refine ⟨2307749113678471319553203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6153997636475923518808541 2307749113678471319553203)
                ·
                  refine ⟨3461623670517706979329805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307749113678471319553203 3461623670517706979329805)
                  ·
                    refine ⟨1298108876444140117248677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461623670517706979329805 1298108876444140117248677)
                    ·
                      rfl

theorem cell22_3792087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_3792087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792087 prefixEnd_3792087 := by exact prefixLift 3792087
  have htrace : WordTrace (prefixWord ++ tailWord_3792087) baseStart_3792087 baseEnd_3792087 := by
    simpa [prefixWord, tailWord_3792087, baseEnd_3792087] using wordTrace_append hprefix tailTrace_3792087
  have hstable : (prefixWord ++ tailWord_3792087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792087).length < 2 ^ (prefixWord ++ tailWord_3792087).sum := by decide
  have hdescent : baseEnd_3792087 < baseStart_3792087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792104 : List Nat := [2, 1, 4, 1, 2, 1, 5, 2, 1, 3]
def baseStart_3792104 : Nat := 118140960795 + 3792104 * 2 ^ 59
def prefixEnd_3792104 : Nat := 4983230072969 + 3 ^ 40 * 3792104 * 2
def baseEnd_3792104 : Nat := 1298114695891557739573625

theorem tailTrace_3792104 : CollatzResearch.WordTrace tailWord_3792104 prefixEnd_3792104 1298114695891557739573625 := by
  unfold tailWord_3792104
  simp only [CollatzResearch.WordTrace]
  refine ⟨69154697726931161323535683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92206263635908215098047577 69154697726931161323535683)
  ·
    refine ⟨103732046590396741985303525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69154697726931161323535683 103732046590396741985303525)
    ·
      refine ⟨19449758735699389122244411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103732046590396741985303525 19449758735699389122244411)
      ·
        refine ⟨29174638103549083683366617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19449758735699389122244411 29174638103549083683366617)
        ·
          refine ⟨21880978577661812762524963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29174638103549083683366617 21880978577661812762524963)
          ·
            refine ⟨32821467866492719143787445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21880978577661812762524963 32821467866492719143787445)
            ·
              refine ⟨3077012612483692419730073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32821467866492719143787445 3077012612483692419730073)
              ·
                refine ⟨2307759459362769314797555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3077012612483692419730073 2307759459362769314797555)
                ·
                  refine ⟨3461639189044153972196333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307759459362769314797555 3461639189044153972196333)
                  ·
                    refine ⟨1298114695891557739573625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461639189044153972196333 1298114695891557739573625)
                    ·
                      rfl

theorem cell22_3792104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_3792104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792104 prefixEnd_3792104 := by exact prefixLift 3792104
  have htrace : WordTrace (prefixWord ++ tailWord_3792104) baseStart_3792104 baseEnd_3792104 := by
    simpa [prefixWord, tailWord_3792104, baseEnd_3792104] using wordTrace_append hprefix tailTrace_3792104
  have hstable : (prefixWord ++ tailWord_3792104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792104).length < 2 ^ (prefixWord ++ tailWord_3792104).sum := by decide
  have hdescent : baseEnd_3792104 < baseStart_3792104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792113 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 3, 4]
def baseStart_3792113 : Nat := 118140960795 + 3792113 * 2 ^ 59
def prefixEnd_3792113 : Nat := 4983230072969 + 3 ^ 40 * 3792113 * 2
def baseEnd_3792113 : Nat := 1298117776775484716098597

theorem tailTrace_3792113 : CollatzResearch.WordTrace tailWord_3792113 prefixEnd_3792113 1298117776775484716098597 := by
  unfold tailWord_3792113
  simp only [CollatzResearch.WordTrace]
  refine ⟨138309723710829717184148993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92206482473886478122765995 138309723710829717184148993)
  ·
    refine ⟨103732292783122287888111745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138309723710829717184148993 103732292783122287888111745)
    ·
      refine ⟨77799219587341715916083809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103732292783122287888111745 77799219587341715916083809)
      ·
        refine ⟨58349414690506286937062857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77799219587341715916083809 58349414690506286937062857)
        ·
          refine ⟨43762061017879715202797143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58349414690506286937062857 43762061017879715202797143)
          ·
            refine ⟨65643091526819572804195715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43762061017879715202797143 65643091526819572804195715)
            ·
              refine ⟨98464637290229359206293573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65643091526819572804195715 98464637290229359206293573)
              ·
                refine ⟨18462119491918004851180045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98464637290229359206293573 18462119491918004851180045)
                ·
                  refine ⟨6923294809469251819192517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18462119491918004851180045 6923294809469251819192517)
                  ·
                    refine ⟨1298117776775484716098597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6923294809469251819192517 1298117776775484716098597)
                    ·
                      rfl

theorem cell22_3792113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_3792113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792113 prefixEnd_3792113 := by exact prefixLift 3792113
  have htrace : WordTrace (prefixWord ++ tailWord_3792113) baseStart_3792113 baseEnd_3792113 := by
    simpa [prefixWord, tailWord_3792113, baseEnd_3792113] using wordTrace_append hprefix tailTrace_3792113
  have hstable : (prefixWord ++ tailWord_3792113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792113).length < 2 ^ (prefixWord ++ tailWord_3792113).sum := by decide
  have hdescent : baseEnd_3792113 < baseStart_3792113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792145 : List Nat := [1, 2, 2, 1, 1, 4, 2, 5, 4]
def baseStart_3792145 : Nat := 118140960795 + 3792145 * 2 ^ 59
def prefixEnd_3792145 : Nat := 4983230072969 + 3 ^ 40 * 3792145 * 2
def baseEnd_3792145 : Nat := 432709577009815766432833

theorem tailTrace_3792145 : CollatzResearch.WordTrace tailWord_3792145 prefixEnd_3792145 432709577009815766432833 := by
  unfold tailWord_3792145
  simp only [CollatzResearch.WordTrace]
  refine ⟨138310890846713786649313889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92207260564475857766209259 138310890846713786649313889)
  ·
    refine ⟨103733168135035339986985417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138310890846713786649313889 103733168135035339986985417)
    ·
      refine ⟨77799876101276504990239063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103733168135035339986985417 77799876101276504990239063)
      ·
        refine ⟨116699814151914757485358595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77799876101276504990239063 116699814151914757485358595)
        ·
          refine ⟨175049721227872136228037893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116699814151914757485358595 175049721227872136228037893)
          ·
            refine ⟨32821822730226025542757105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175049721227872136228037893 32821822730226025542757105)
            ·
              refine ⟨24616367047669519157067829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32821822730226025542757105 24616367047669519157067829)
              ·
                refine ⟨2307784410719017420975109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24616367047669519157067829 2307784410719017420975109)
                ·
                  refine ⟨432709577009815766432833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2307784410719017420975109 432709577009815766432833)
                  ·
                    rfl

theorem cell22_3792145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 4].length) (baseStart_3792145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792145 prefixEnd_3792145 := by exact prefixLift 3792145
  have htrace : WordTrace (prefixWord ++ tailWord_3792145) baseStart_3792145 baseEnd_3792145 := by
    simpa [prefixWord, tailWord_3792145, baseEnd_3792145] using wordTrace_append hprefix tailTrace_3792145
  have hstable : (prefixWord ++ tailWord_3792145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792145).length < 2 ^ (prefixWord ++ tailWord_3792145).sum := by decide
  have hdescent : baseEnd_3792145 < baseStart_3792145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792177 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 2, 3]
def baseStart_3792177 : Nat := 118140960795 + 3792177 * 2 ^ 59
def prefixEnd_3792177 : Nat := 4983230072969 + 3 ^ 40 * 3792177 * 2
def baseEnd_3792177 : Nat := 1298139685283409882498401

theorem tailTrace_3792177 : CollatzResearch.WordTrace tailWord_3792177 prefixEnd_3792177 1298139685283409882498401 := by
  unfold tailWord_3792177
  simp only [CollatzResearch.WordTrace]
  refine ⟨138312057982597856114478785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92208038655065237409652523 138312057982597856114478785)
  ·
    refine ⟨103734043486948392085859089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138312057982597856114478785 103734043486948392085859089)
    ·
      refine ⟨77800532615211294064394317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103734043486948392085859089 77800532615211294064394317)
      ·
        refine ⟨29175199730704235274147869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77800532615211294064394317 29175199730704235274147869)
        ·
          refine ⟨10940699899014088227805451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29175199730704235274147869 10940699899014088227805451)
          ·
            refine ⟨16411049848521132341708177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10940699899014088227805451 16411049848521132341708177)
            ·
              refine ⟨12308287386390849256281133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16411049848521132341708177 12308287386390849256281133)
              ·
                refine ⟨4615607769896568471105425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12308287386390849256281133 4615607769896568471105425)
                ·
                  refine ⟨3461705827422426353329069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4615607769896568471105425 3461705827422426353329069)
                  ·
                    refine ⟨1298139685283409882498401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461705827422426353329069 1298139685283409882498401)
                    ·
                      rfl

theorem cell22_3792177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_3792177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792177 prefixEnd_3792177 := by exact prefixLift 3792177
  have htrace : WordTrace (prefixWord ++ tailWord_3792177) baseStart_3792177 baseEnd_3792177 := by
    simpa [prefixWord, tailWord_3792177, baseEnd_3792177] using wordTrace_append hprefix tailTrace_3792177
  have hstable : (prefixWord ++ tailWord_3792177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792177).length < 2 ^ (prefixWord ++ tailWord_3792177).sum := by decide
  have hdescent : baseEnd_3792177 < baseStart_3792177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792233 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_3792233 : Nat := 118140960795 + 3792233 * 2 ^ 59
def prefixEnd_3792233 : Nat := 4983230072969 + 3 ^ 40 * 3792233 * 2
def baseEnd_3792233 : Nat := 1298158855227844403098229

theorem tailTrace_3792233 : CollatzResearch.WordTrace tailWord_3792233 prefixEnd_3792233 1298158855227844403098229 := by
  unfold tailWord_3792233
  simp only [CollatzResearch.WordTrace]
  refine ⟨138314100470394977678517353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92209400313596651785678235 138314100470394977678517353)
  ·
    refine ⟨103735575352796233258888015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138314100470394977678517353 103735575352796233258888015)
    ·
      refine ⟨155603363029194349888332023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103735575352796233258888015 155603363029194349888332023)
      ·
        refine ⟨233405044543791524832498035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155603363029194349888332023 233405044543791524832498035)
        ·
          refine ⟨350107566815687287248747053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233405044543791524832498035 350107566815687287248747053)
          ·
            refine ⟨131290337555882732718280145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350107566815687287248747053 131290337555882732718280145)
            ·
              refine ⟨98467753166912049538710109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131290337555882732718280145 98467753166912049538710109)
              ·
                refine ⟨36925407437592018577016291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98467753166912049538710109 36925407437592018577016291)
                ·
                  refine ⟨55388111156388027865524437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36925407437592018577016291 55388111156388027865524437)
                  ·
                    refine ⟨1298158855227844403098229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55388111156388027865524437 1298158855227844403098229)
                    ·
                      rfl

theorem cell22_3792233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_3792233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792233 prefixEnd_3792233 := by exact prefixLift 3792233
  have htrace : WordTrace (prefixWord ++ tailWord_3792233) baseStart_3792233 baseEnd_3792233 := by
    simpa [prefixWord, tailWord_3792233, baseEnd_3792233] using wordTrace_append hprefix tailTrace_3792233
  have hstable : (prefixWord ++ tailWord_3792233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792233).length < 2 ^ (prefixWord ++ tailWord_3792233).sum := by decide
  have hdescent : baseEnd_3792233 < baseStart_3792233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792248 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_3792248 : Nat := 118140960795 + 3792248 * 2 ^ 59
def prefixEnd_3792248 : Nat := 4983230072969 + 3 ^ 40 * 3792248 * 2
def baseEnd_3792248 : Nat := 1298163990034389363973183

theorem tailTrace_3792248 : CollatzResearch.WordTrace tailWord_3792248 prefixEnd_3792248 1298163990034389363973183 := by
  unfold tailWord_3792248
  simp only [CollatzResearch.WordTrace]
  refine ⟨69157323782670317620156699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92209765043560423493542265 69157323782670317620156699)
  ·
    refine ⟨103735985674005476430235049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69157323782670317620156699 103735985674005476430235049)
    ·
      refine ⟨77801989255504107322676287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103735985674005476430235049 77801989255504107322676287)
      ·
        refine ⟨116702983883256160984014431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77801989255504107322676287 116702983883256160984014431)
        ·
          refine ⟨175054475824884241476021647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116702983883256160984014431 175054475824884241476021647)
          ·
            refine ⟨262581713737326362214032471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175054475824884241476021647 262581713737326362214032471)
            ·
              refine ⟨393872570605989543321048707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262581713737326362214032471 393872570605989543321048707)
              ·
                refine ⟨590808855908984314981573061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393872570605989543321048707 590808855908984314981573061)
                ·
                  refine ⟨110776660482934559059044949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 590808855908984314981573061 110776660482934559059044949)
                  ·
                    refine ⟨1298163990034389363973183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110776660482934559059044949 1298163990034389363973183)
                    ·
                      rfl

theorem cell22_3792248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_3792248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792248 prefixEnd_3792248 := by exact prefixLift 3792248
  have htrace : WordTrace (prefixWord ++ tailWord_3792248) baseStart_3792248 baseEnd_3792248 := by
    simpa [prefixWord, tailWord_3792248, baseEnd_3792248] using wordTrace_append hprefix tailTrace_3792248
  have hstable : (prefixWord ++ tailWord_3792248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792248).length < 2 ^ (prefixWord ++ tailWord_3792248).sum := by decide
  have hdescent : baseEnd_3792248 < baseStart_3792248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792316 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 1, 4]
def baseStart_3792316 : Nat := 118140960795 + 3792316 * 2 ^ 59
def prefixEnd_3792316 : Nat := 4983230072969 + 3 ^ 40 * 3792316 * 2
def baseEnd_3792316 : Nat := 1298187267824059853272975

theorem tailTrace_3792316 : CollatzResearch.WordTrace tailWord_3792316 prefixEnd_3792316 1298187267824059853272975 := by
  unfold tailWord_3792316
  simp only [CollatzResearch.WordTrace]
  refine ⟨69158563864547141426894401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92211418486062855235859201 69158563864547141426894401)
  ·
    refine ⟨51868922898410356070170801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69158563864547141426894401 51868922898410356070170801)
    ·
      refine ⟨38901692173807767052628101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51868922898410356070170801 38901692173807767052628101)
      ·
        refine ⟨7294067282588956322367769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38901692173807767052628101 7294067282588956322367769)
        ·
          refine ⟨5470550461941717241775827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7294067282588956322367769 5470550461941717241775827)
          ·
            refine ⟨8205825692912575862663741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5470550461941717241775827 8205825692912575862663741)
            ·
              refine ⟨3077184634842215948498903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8205825692912575862663741 3077184634842215948498903)
              ·
                refine ⟨4615776952263323922748355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3077184634842215948498903 4615776952263323922748355)
                ·
                  refine ⟨6923665428394985884122533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4615776952263323922748355 6923665428394985884122533)
                  ·
                    refine ⟨1298187267824059853272975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6923665428394985884122533 1298187267824059853272975)
                    ·
                      rfl

theorem cell22_3792316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_3792316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792316 prefixEnd_3792316 := by exact prefixLift 3792316
  have htrace : WordTrace (prefixWord ++ tailWord_3792316) baseStart_3792316 baseEnd_3792316 := by
    simpa [prefixWord, tailWord_3792316, baseEnd_3792316] using wordTrace_append hprefix tailTrace_3792316
  have hstable : (prefixWord ++ tailWord_3792316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792316).length < 2 ^ (prefixWord ++ tailWord_3792316).sum := by decide
  have hdescent : baseEnd_3792316 < baseStart_3792316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792391 : List Nat := [1, 1, 4, 3, 2, 1, 2, 4, 1, 3]
def baseStart_3792391 : Nat := 118140960795 + 3792391 * 2 ^ 59
def prefixEnd_3792391 : Nat := 4983230072969 + 3 ^ 40 * 3792391 * 2
def baseEnd_3792391 : Nat := 1298212941856784657647745

theorem tailTrace_3792391 : CollatzResearch.WordTrace tailWord_3792391 prefixEnd_3792391 1298212941856784657647745 := by
  unfold tailWord_3792391
  simp only [CollatzResearch.WordTrace]
  refine ⟨138319863203822570662769027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92213242135881713775179351 138319863203822570662769027)
  ·
    refine ⟨207479794805733855994153541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138319863203822570662769027 207479794805733855994153541)
    ·
      refine ⟨38902461526075097998903789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207479794805733855994153541 38902461526075097998903789)
      ·
        refine ⟨14588423072278161749588921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38902461526075097998903789 14588423072278161749588921)
        ·
          refine ⟨10941317304208621312191691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14588423072278161749588921 10941317304208621312191691)
          ·
            refine ⟨16411975956312931968287537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10941317304208621312191691 16411975956312931968287537)
            ·
              refine ⟨12308981967234698976215653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16411975956312931968287537 12308981967234698976215653)
              ·
                refine ⟨2307934118856506058040435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12308981967234698976215653 2307934118856506058040435)
                ·
                  refine ⟨3461901178284759087060653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307934118856506058040435 3461901178284759087060653)
                  ·
                    refine ⟨1298212941856784657647745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461901178284759087060653 1298212941856784657647745)
                    ·
                      rfl

theorem cell22_3792391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_3792391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792391 prefixEnd_3792391 := by exact prefixLift 3792391
  have htrace : WordTrace (prefixWord ++ tailWord_3792391) baseStart_3792391 baseEnd_3792391 := by
    simpa [prefixWord, tailWord_3792391, baseEnd_3792391] using wordTrace_append hprefix tailTrace_3792391
  have hstable : (prefixWord ++ tailWord_3792391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792391).length < 2 ^ (prefixWord ++ tailWord_3792391).sum := by decide
  have hdescent : baseEnd_3792391 < baseStart_3792391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792462 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_3792462 : Nat := 118140960795 + 3792462 * 2 ^ 59
def prefixEnd_3792462 : Nat := 4983230072969 + 3 ^ 40 * 3792462 * 2
def baseEnd_3792462 : Nat := 1298237246607764139122527

theorem tailTrace_3792462 : CollatzResearch.WordTrace tailWord_3792462 prefixEnd_3792462 1298237246607764139122527 := by
  unfold tailWord_3792462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17290306598320668723575455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92214968524376899859069093 17290306598320668723575455)
  ·
    refine ⟨25935459897481003085363183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17290306598320668723575455 25935459897481003085363183)
    ·
      refine ⟨38903189846221504628044775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25935459897481003085363183 38903189846221504628044775)
      ·
        refine ⟨58354784769332256942067163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38903189846221504628044775 58354784769332256942067163)
        ·
          refine ⟨87532177153998385413100745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58354784769332256942067163 87532177153998385413100745)
          ·
            refine ⟨65649132865498789059825559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87532177153998385413100745 65649132865498789059825559)
            ·
              refine ⟨98473699298248183589738339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65649132865498789059825559 98473699298248183589738339)
              ·
                refine ⟨147710548947372275384607509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98473699298248183589738339 147710548947372275384607509)
                ·
                  refine ⟨6923931981908075408653477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147710548947372275384607509 6923931981908075408653477)
                  ·
                    refine ⟨1298237246607764139122527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6923931981908075408653477 1298237246607764139122527)
                    ·
                      rfl

theorem cell22_3792462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_3792462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792462 prefixEnd_3792462 := by exact prefixLift 3792462
  have htrace : WordTrace (prefixWord ++ tailWord_3792462) baseStart_3792462 baseEnd_3792462 := by
    simpa [prefixWord, tailWord_3792462, baseEnd_3792462] using wordTrace_append hprefix tailTrace_3792462
  have hstable : (prefixWord ++ tailWord_3792462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792462).length < 2 ^ (prefixWord ++ tailWord_3792462).sum := by decide
  have hdescent : baseEnd_3792462 < baseStart_3792462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792464 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 2, 3]
def baseStart_3792464 : Nat := 118140960795 + 3792464 * 2 ^ 59
def prefixEnd_3792464 : Nat := 4983230072969 + 3 ^ 40 * 3792464 * 2
def baseEnd_3792464 : Nat := 1298237931248636800572521

theorem tailTrace_3792464 : CollatzResearch.WordTrace tailWord_3792464 prefixEnd_3792464 1298237931248636800572521 := by
  unfold tailWord_3792464
  simp only [CollatzResearch.WordTrace]
  refine ⟨69161262866279052065088223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92215017155038736086784297 69161262866279052065088223)
  ·
    refine ⟨103741894299418578097632335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69161262866279052065088223 103741894299418578097632335)
    ·
      refine ⟨155612841449127867146448503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103741894299418578097632335 155612841449127867146448503)
      ·
        refine ⟨233419262173691800719672755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155612841449127867146448503 233419262173691800719672755)
        ·
          refine ⟨350128893260537701079509133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233419262173691800719672755 350128893260537701079509133)
          ·
            refine ⟨131298334972701637904815925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350128893260537701079509133 131298334972701637904815925)
            ·
              refine ⟨12309218903690778553576493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131298334972701637904815925 12309218903690778553576493)
              ·
                refine ⟨4615957088884041957591185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12309218903690778553576493 4615957088884041957591185)
                ·
                  refine ⟨3461967816663031468193389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4615957088884041957591185 3461967816663031468193389)
                  ·
                    refine ⟨1298237931248636800572521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461967816663031468193389 1298237931248636800572521)
                    ·
                      rfl

theorem cell22_3792464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2, 3].length) (baseStart_3792464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792464 prefixEnd_3792464 := by exact prefixLift 3792464
  have htrace : WordTrace (prefixWord ++ tailWord_3792464) baseStart_3792464 baseEnd_3792464 := by
    simpa [prefixWord, tailWord_3792464, baseEnd_3792464] using wordTrace_append hprefix tailTrace_3792464
  have hstable : (prefixWord ++ tailWord_3792464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792464).length < 2 ^ (prefixWord ++ tailWord_3792464).sum := by decide
  have hdescent : baseEnd_3792464 < baseStart_3792464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792494 : List Nat := [4, 1, 2, 2, 4, 9]
def baseStart_3792494 : Nat := 118140960795 + 3792494 * 2 ^ 59
def prefixEnd_3792494 : Nat := 4983230072969 + 3 ^ 40 * 3792494 * 2
def baseEnd_3792494 : Nat := 16027755566194157065709

theorem tailTrace_3792494 : CollatzResearch.WordTrace tailWord_3792494 prefixEnd_3792494 16027755566194157065709 := by
  unfold tailWord_3792494
  simp only [CollatzResearch.WordTrace]
  refine ⟨17290452490306177406721067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92215746614966279502512357 17290452490306177406721067)
  ·
    refine ⟨25935678735459266110081601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17290452490306177406721067 25935678735459266110081601)
    ·
      refine ⟨19451759051594449582561201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25935678735459266110081601 19451759051594449582561201)
      ·
        refine ⟨14588819288695837186920901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19451759051594449582561201 14588819288695837186920901)
        ·
          refine ⟨2735403616630469472547669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14588819288695837186920901 2735403616630469472547669)
          ·
            refine ⟨16027755566194157065709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2735403616630469472547669 16027755566194157065709)
            ·
              rfl

theorem cell22_3792494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 9].length) (baseStart_3792494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792494 prefixEnd_3792494 := by exact prefixLift 3792494
  have htrace : WordTrace (prefixWord ++ tailWord_3792494) baseStart_3792494 baseEnd_3792494 := by
    simpa [prefixWord, tailWord_3792494, baseEnd_3792494] using wordTrace_append hprefix tailTrace_3792494
  have hstable : (prefixWord ++ tailWord_3792494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792494).length < 2 ^ (prefixWord ++ tailWord_3792494).sum := by decide
  have hdescent : baseEnd_3792494 < baseStart_3792494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792526 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_3792526 : Nat := 118140960795 + 3792526 * 2 ^ 59
def prefixEnd_3792526 : Nat := 4983230072969 + 3 ^ 40 * 3792526 * 2
def baseEnd_3792526 : Nat := 1298259155115689305522331

theorem tailTrace_3792526 : CollatzResearch.WordTrace tailWord_3792526 prefixEnd_3792526 1298259155115689305522331 := by
  unfold tailWord_3792526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17290598382291686089866679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92216524705555659145955621 17290598382291686089866679)
  ·
    refine ⟨25935897573437529134800019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17290598382291686089866679 25935897573437529134800019)
    ·
      refine ⟨38903846360156293702200029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25935897573437529134800019 38903846360156293702200029)
      ·
        refine ⟨14588942385058610138325011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38903846360156293702200029 14588942385058610138325011)
        ·
          refine ⟨21883413577587915207487517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14588942385058610138325011 21883413577587915207487517)
          ·
            refine ⟨8206280091595468202807819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21883413577587915207487517 8206280091595468202807819)
            ·
              refine ⟨12309420137393202304211729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8206280091595468202807819 12309420137393202304211729)
              ·
                refine ⟨9232065103044901728158797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12309420137393202304211729 9232065103044901728158797)
                ·
                  refine ⟨3462024413641838148059549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9232065103044901728158797 3462024413641838148059549)
                  ·
                    refine ⟨1298259155115689305522331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3462024413641838148059549 1298259155115689305522331)
                    ·
                      rfl

theorem cell22_3792526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_3792526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792526 prefixEnd_3792526 := by exact prefixLift 3792526
  have htrace : WordTrace (prefixWord ++ tailWord_3792526) baseStart_3792526 baseEnd_3792526 := by
    simpa [prefixWord, tailWord_3792526, baseEnd_3792526] using wordTrace_append hprefix tailTrace_3792526
  have hstable : (prefixWord ++ tailWord_3792526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792526).length < 2 ^ (prefixWord ++ tailWord_3792526).sum := by decide
  have hdescent : baseEnd_3792526 < baseStart_3792526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792599 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 6, 3]
def baseStart_3792599 : Nat := 118140960795 + 3792599 * 2 ^ 59
def prefixEnd_3792599 : Nat := 4983230072969 + 3 ^ 40 * 3792599 * 2
def baseEnd_3792599 : Nat := 1298284144507541448447107

theorem tailTrace_3792599 : CollatzResearch.WordTrace tailWord_3792599 prefixEnd_3792599 1298284144507541448447107 := by
  unfold tailWord_3792599
  simp only [CollatzResearch.WordTrace]
  refine ⟨138327449587069022186340851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92218299724712681457560567 138327449587069022186340851)
  ·
    refine ⟨207491174380603533279511277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138327449587069022186340851 207491174380603533279511277)
    ·
      refine ⟨77809190392726324979816729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207491174380603533279511277 77809190392726324979816729)
      ·
        refine ⟨58356892794544743734862547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77809190392726324979816729 58356892794544743734862547)
        ·
          refine ⟨87535339191817115602293821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58356892794544743734862547 87535339191817115602293821)
          ·
            refine ⟨32825752196931418350860183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87535339191817115602293821 32825752196931418350860183)
            ·
              refine ⟨49238628295397127526290275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32825752196931418350860183 49238628295397127526290275)
              ·
                refine ⟨73857942443095691289435413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49238628295397127526290275 73857942443095691289435413)
                ·
                  refine ⟨3462091052020110529192285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73857942443095691289435413 3462091052020110529192285)
                  ·
                    refine ⟨1298284144507541448447107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3462091052020110529192285 1298284144507541448447107)
                    ·
                      rfl

theorem cell22_3792599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_3792599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792599 prefixEnd_3792599 := by exact prefixLift 3792599
  have htrace : WordTrace (prefixWord ++ tailWord_3792599) baseStart_3792599 baseEnd_3792599 := by
    simpa [prefixWord, tailWord_3792599, baseEnd_3792599] using wordTrace_append hprefix tailTrace_3792599
  have hstable : (prefixWord ++ tailWord_3792599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792599).length < 2 ^ (prefixWord ++ tailWord_3792599).sum := by decide
  have hdescent : baseEnd_3792599 < baseStart_3792599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792601 : List Nat := [1, 2, 1, 2, 3, 3, 3, 3, 4]
def baseStart_3792601 : Nat := 118140960795 + 3792601 * 2 ^ 59
def prefixEnd_3792601 : Nat := 4983230072969 + 3 ^ 40 * 3792601 * 2
def baseEnd_3792601 : Nat := 432761609716138036632367

theorem tailTrace_3792601 : CollatzResearch.WordTrace tailWord_3792601 prefixEnd_3792601 432761609716138036632367 := by
  unfold tailWord_3792601
  simp only [CollatzResearch.WordTrace]
  refine ⟨138327522533061776527913657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92218348355374517685275771 138327522533061776527913657)
  ·
    refine ⟨103745641899796332395935243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138327522533061776527913657 103745641899796332395935243)
    ·
      refine ⟨155618462849694498593902865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103745641899796332395935243 155618462849694498593902865)
      ·
        refine ⟨116713847137270873945427149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155618462849694498593902865 116713847137270873945427149)
        ·
          refine ⟨43767692676476577729535181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116713847137270873945427149 43767692676476577729535181)
          ·
            refine ⟨16412884753678716648575693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43767692676476577729535181 16412884753678716648575693)
            ·
              refine ⟨6154831782629518743215885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16412884753678716648575693 6154831782629518743215885)
              ·
                refine ⟨2308061918486069528705957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6154831782629518743215885 2308061918486069528705957)
                ·
                  refine ⟨432761609716138036632367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2308061918486069528705957 432761609716138036632367)
                  ·
                    rfl

theorem cell22_3792601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 4].length) (baseStart_3792601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792601 prefixEnd_3792601 := by exact prefixLift 3792601
  have htrace : WordTrace (prefixWord ++ tailWord_3792601) baseStart_3792601 baseEnd_3792601 := by
    simpa [prefixWord, tailWord_3792601, baseEnd_3792601] using wordTrace_append hprefix tailTrace_3792601
  have hstable : (prefixWord ++ tailWord_3792601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792601).length < 2 ^ (prefixWord ++ tailWord_3792601).sum := by decide
  have hdescent : baseEnd_3792601 < baseStart_3792601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792616 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 4, 3]
def baseStart_3792616 : Nat := 118140960795 + 3792616 * 2 ^ 59
def prefixEnd_3792616 : Nat := 4983230072969 + 3 ^ 40 * 3792616 * 2
def baseEnd_3792616 : Nat := 1298289963954959070772055

theorem tailTrace_3792616 : CollatzResearch.WordTrace tailWord_3792616 prefixEnd_3792616 1298289963954959070772055 := by
  unfold tailWord_3792616
  simp only [CollatzResearch.WordTrace]
  refine ⟨69164034814003717044854851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92218713085338289393139801 69164034814003717044854851)
  ·
    refine ⟨103746052221005575567282277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69164034814003717044854851 103746052221005575567282277)
    ·
      refine ⟨19452384791438545418865427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103746052221005575567282277 19452384791438545418865427)
      ·
        refine ⟨29178577187157818128298141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19452384791438545418865427 29178577187157818128298141)
        ·
          refine ⟨10941966445184181798111803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29178577187157818128298141 10941966445184181798111803)
          ·
            refine ⟨16412949667776272697167705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10941966445184181798111803 16412949667776272697167705)
            ·
              refine ⟨12309712250832204522875779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16412949667776272697167705 12309712250832204522875779)
              ·
                refine ⟨18464568376248306784313669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12309712250832204522875779 18464568376248306784313669)
                ·
                  refine ⟨3462106570546557522058813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18464568376248306784313669 3462106570546557522058813)
                  ·
                    refine ⟨1298289963954959070772055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3462106570546557522058813 1298289963954959070772055)
                    ·
                      rfl

theorem cell22_3792616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_3792616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792616 prefixEnd_3792616 := by exact prefixLift 3792616
  have htrace : WordTrace (prefixWord ++ tailWord_3792616) baseStart_3792616 baseEnd_3792616 := by
    simpa [prefixWord, tailWord_3792616, baseEnd_3792616] using wordTrace_append hprefix tailTrace_3792616
  have hstable : (prefixWord ++ tailWord_3792616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792616).length < 2 ^ (prefixWord ++ tailWord_3792616).sum := by decide
  have hdescent : baseEnd_3792616 < baseStart_3792616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792689 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_3792689 : Nat := 118140960795 + 3792689 * 2 ^ 59
def prefixEnd_3792689 : Nat := 4983230072969 + 3 ^ 40 * 3792689 * 2
def baseEnd_3792689 : Nat := 1298314953346811213696831

theorem tailTrace_3792689 : CollatzResearch.WordTrace tailWord_3792689 prefixEnd_3792689 1298314953346811213696831 := by
  unfold tailWord_3792689
  simp only [CollatzResearch.WordTrace]
  refine ⟨138330732156742967557117121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92220488104495311704744747 138330732156742967557117121)
  ·
    refine ⟨103748049117557225667837841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138330732156742967557117121 103748049117557225667837841)
    ·
      refine ⟨77811036838167919250878381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103748049117557225667837841 77811036838167919250878381)
      ·
        refine ⟨29179138814312969719079393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77811036838167919250878381 29179138814312969719079393)
        ·
          refine ⟨21884354110734727289309545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29179138814312969719079393 21884354110734727289309545)
          ·
            refine ⟨16413265583051045466982159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21884354110734727289309545 16413265583051045466982159)
            ·
              refine ⟨24619898374576568200473239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16413265583051045466982159 24619898374576568200473239)
              ·
                refine ⟨36929847561864852300709859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24619898374576568200473239 36929847561864852300709859)
                ·
                  refine ⟨55394771342797278451064789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36929847561864852300709859 55394771342797278451064789)
                  ·
                    refine ⟨1298314953346811213696831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55394771342797278451064789 1298314953346811213696831)
                    ·
                      rfl

theorem cell22_3792689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_3792689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792689 prefixEnd_3792689 := by exact prefixLift 3792689
  have htrace : WordTrace (prefixWord ++ tailWord_3792689) baseStart_3792689 baseEnd_3792689 := by
    simpa [prefixWord, tailWord_3792689, baseEnd_3792689] using wordTrace_append hprefix tailTrace_3792689
  have hstable : (prefixWord ++ tailWord_3792689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792689).length < 2 ^ (prefixWord ++ tailWord_3792689).sum := by decide
  have hdescent : baseEnd_3792689 < baseStart_3792689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792736 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 6]
def baseStart_3792736 : Nat := 118140960795 + 3792736 * 2 ^ 59
def prefixEnd_3792736 : Nat := 4983230072969 + 3 ^ 40 * 3792736 * 2
def baseEnd_3792736 : Nat := 432777014135772919257229

theorem tailTrace_3792736 : CollatzResearch.WordTrace tailWord_3792736 prefixEnd_3792736 432777014135772919257229 := by
  unfold tailWord_3792736
  simp only [CollatzResearch.WordTrace]
  refine ⟨69166223193786347292039031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92221630925048463056052041 69166223193786347292039031)
  ·
    refine ⟨103749334790679520938058547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69166223193786347292039031 103749334790679520938058547)
    ·
      refine ⟨155624002186019281407087821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103749334790679520938058547 155624002186019281407087821)
      ·
        refine ⟨58359000819757230527657933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155624002186019281407087821 58359000819757230527657933)
        ·
          refine ⟨21884625307408961447871725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58359000819757230527657933 21884625307408961447871725)
          ·
            refine ⟨8206734490278360542951897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21884625307408961447871725 8206734490278360542951897)
            ·
              refine ⟨6155050867708770407213923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8206734490278360542951897 6155050867708770407213923)
              ·
                refine ⟨9232576301563155610820885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6155050867708770407213923 9232576301563155610820885)
                ·
                  refine ⟨432777014135772919257229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9232576301563155610820885 432777014135772919257229)
                  ·
                    rfl

theorem cell22_3792736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_3792736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792736 prefixEnd_3792736 := by exact prefixLift 3792736
  have htrace : WordTrace (prefixWord ++ tailWord_3792736) baseStart_3792736 baseEnd_3792736 := by
    simpa [prefixWord, tailWord_3792736, baseEnd_3792736] using wordTrace_append hprefix tailTrace_3792736
  have hstable : (prefixWord ++ tailWord_3792736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792736).length < 2 ^ (prefixWord ++ tailWord_3792736).sum := by decide
  have hdescent : baseEnd_3792736 < baseStart_3792736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792809 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 9]
def baseStart_3792809 : Nat := 118140960795 + 3792809 * 2 ^ 59
def prefixEnd_3792809 : Nat := 4983230072969 + 3 ^ 40 * 3792809 * 2
def baseEnd_3792809 : Nat := 432785343933056966898821

theorem tailTrace_3792809 : CollatzResearch.WordTrace tailWord_3792809 prefixEnd_3792809 432785343933056966898821 := by
  unfold tailWord_3792809
  simp only [CollatzResearch.WordTrace]
  refine ⟨138335108916308228051485481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92223405944205485367656987 138335108916308228051485481)
  ·
    refine ⟨103751331687231171038614111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138335108916308228051485481 103751331687231171038614111)
    ·
      refine ⟨155626997530846756557921167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103751331687231171038614111 155626997530846756557921167)
      ·
        refine ⟨233440496296270134836881751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155626997530846756557921167 233440496296270134836881751)
        ·
          refine ⟨350160744444405202255322627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233440496296270134836881751 350160744444405202255322627)
          ·
            refine ⟨525241116666607803382983941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350160744444405202255322627 525241116666607803382983941)
            ·
              refine ⟨98482709374988963134309489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 525241116666607803382983941 98482709374988963134309489)
              ·
                refine ⟨73862032031241722350732117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98482709374988963134309489 73862032031241722350732117)
                ·
                  refine ⟨432785343933056966898821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73862032031241722350732117 432785343933056966898821)
                  ·
                    rfl

theorem cell22_3792809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_3792809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792809 prefixEnd_3792809 := by exact prefixLift 3792809
  have htrace : WordTrace (prefixWord ++ tailWord_3792809) baseStart_3792809 baseEnd_3792809 := by
    simpa [prefixWord, tailWord_3792809, baseEnd_3792809] using wordTrace_append hprefix tailTrace_3792809
  have hstable : (prefixWord ++ tailWord_3792809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792809).length < 2 ^ (prefixWord ++ tailWord_3792809).sum := by decide
  have hdescent : baseEnd_3792809 < baseStart_3792809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792856 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 5, 4]
def baseStart_3792856 : Nat := 118140960795 + 3792856 * 2 ^ 59
def prefixEnd_3792856 : Nat := 4983230072969 + 3 ^ 40 * 3792856 * 2
def baseEnd_3792856 : Nat := 1298372120859678444771319

theorem tailTrace_3792856 : CollatzResearch.WordTrace tailWord_3792856 prefixEnd_3792856 1298372120859678444771319 := by
  unfold tailWord_3792856
  simp only [CollatzResearch.WordTrace]
  refine ⟨69168411573568977539223211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92224548764758636718964281 69168411573568977539223211)
  ·
    refine ⟨103752617360353466308834817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69168411573568977539223211 103752617360353466308834817)
    ·
      refine ⟨77814463020265099731626113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103752617360353466308834817 77814463020265099731626113)
      ·
        refine ⟨58360847265198824798719585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77814463020265099731626113 58360847265198824798719585)
        ·
          refine ⟨43770635448899118599039689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58360847265198824798719585 43770635448899118599039689)
          ·
            refine ⟨32827976586674338949279767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43770635448899118599039689 32827976586674338949279767)
            ·
              refine ⟨49241964880011508423919651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32827976586674338949279767 49241964880011508423919651)
              ·
                refine ⟨73862947320017262635879477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49241964880011508423919651 73862947320017262635879477)
                ·
                  refine ⟨6924651311251618372113701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73862947320017262635879477 6924651311251618372113701)
                  ·
                    refine ⟨1298372120859678444771319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6924651311251618372113701 1298372120859678444771319)
                    ·
                      rfl

theorem cell22_3792856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_3792856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792856 prefixEnd_3792856 := by exact prefixLift 3792856
  have htrace : WordTrace (prefixWord ++ tailWord_3792856) baseStart_3792856 baseEnd_3792856 := by
    simpa [prefixWord, tailWord_3792856, baseEnd_3792856] using wordTrace_append hprefix tailTrace_3792856
  have hstable : (prefixWord ++ tailWord_3792856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792856).length < 2 ^ (prefixWord ++ tailWord_3792856).sum := by decide
  have hdescent : baseEnd_3792856 < baseStart_3792856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792858 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_3792858 : Nat := 118140960795 + 3792858 * 2 ^ 59
def prefixEnd_3792858 : Nat := 4983230072969 + 3 ^ 40 * 3792858 * 2
def baseEnd_3792858 : Nat := 1298372805500551106221313

theorem tailTrace_3792858 : CollatzResearch.WordTrace tailWord_3792858 prefixEnd_3792858 1298372805500551106221313 := by
  unfold tailWord_3792858
  simp only [CollatzResearch.WordTrace]
  refine ⟨34584224023282677355004807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92224597395420472946679485 34584224023282677355004807)
  ·
    refine ⟨51876336034924016032507211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34584224023282677355004807 51876336034924016032507211)
    ·
      refine ⟨77814504052386024048760817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51876336034924016032507211 77814504052386024048760817)
      ·
        refine ⟨58360878039289518036570613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77814504052386024048760817 58360878039289518036570613)
        ·
          refine ⟨5471332316183392315928495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58360878039289518036570613 5471332316183392315928495)
          ·
            refine ⟨8206998474275088473892743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471332316183392315928495 8206998474275088473892743)
            ·
              refine ⟨12310497711412632710839115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8206998474275088473892743 12310497711412632710839115)
              ·
                refine ⟨18465746567118949066258673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12310497711412632710839115 18465746567118949066258673)
                ·
                  refine ⟨13849309925339211799694005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18465746567118949066258673 13849309925339211799694005)
                  ·
                    refine ⟨1298372805500551106221313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13849309925339211799694005 1298372805500551106221313)
                    ·
                      rfl

theorem cell22_3792858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_3792858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792858 prefixEnd_3792858 := by exact prefixLift 3792858
  have htrace : WordTrace (prefixWord ++ tailWord_3792858) baseStart_3792858 baseEnd_3792858 := by
    simpa [prefixWord, tailWord_3792858, baseEnd_3792858] using wordTrace_append hprefix tailTrace_3792858
  have hstable : (prefixWord ++ tailWord_3792858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792858).length < 2 ^ (prefixWord ++ tailWord_3792858).sum := by decide
  have hdescent : baseEnd_3792858 < baseStart_3792858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792888 : List Nat := [2, 1, 2, 1, 1, 3, 3, 5, 4]
def baseStart_3792888 : Nat := 118140960795 + 3792888 * 2 ^ 59
def prefixEnd_3792888 : Nat := 4983230072969 + 3 ^ 40 * 3792888 * 2
def baseEnd_3792888 : Nat := 432794358371213675990407

theorem tailTrace_3792888 : CollatzResearch.WordTrace tailWord_3792888 prefixEnd_3792888 432794358371213675990407 := by
  unfold tailWord_3792888
  simp only [CollatzResearch.WordTrace]
  refine ⟨69168995141511012271805659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92225326855348016362407545 69168995141511012271805659)
  ·
    refine ⟨103753492712266518407708489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69168995141511012271805659 103753492712266518407708489)
    ·
      refine ⟨77815119534199888805781367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103753492712266518407708489 77815119534199888805781367)
      ·
        refine ⟨116722679301299833208672051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77815119534199888805781367 116722679301299833208672051)
        ·
          refine ⟨175084018951949749813008077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116722679301299833208672051 175084018951949749813008077)
          ·
            refine ⟨65656507106981156179878029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175084018951949749813008077 65656507106981156179878029)
            ·
              refine ⟨24621190165117933567454261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65656507106981156179878029 24621190165117933567454261)
              ·
                refine ⟨2308236577979806271948837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24621190165117933567454261 2308236577979806271948837)
                ·
                  refine ⟨432794358371213675990407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2308236577979806271948837 432794358371213675990407)
                  ·
                    rfl

theorem cell22_3792888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 5, 4].length) (baseStart_3792888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792888 prefixEnd_3792888 := by exact prefixLift 3792888
  have htrace : WordTrace (prefixWord ++ tailWord_3792888) baseStart_3792888 baseEnd_3792888 := by
    simpa [prefixWord, tailWord_3792888, baseEnd_3792888] using wordTrace_append hprefix tailTrace_3792888
  have hstable : (prefixWord ++ tailWord_3792888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792888).length < 2 ^ (prefixWord ++ tailWord_3792888).sum := by decide
  have hdescent : baseEnd_3792888 < baseStart_3792888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792931 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 2, 7]
def baseStart_3792931 : Nat := 118140960795 + 3792931 * 2 ^ 59
def prefixEnd_3792931 : Nat := 4983230072969 + 3 ^ 40 * 3792931 * 2
def baseEnd_3792931 : Nat := 1298397794892403249146089

theorem tailTrace_3792931 : CollatzResearch.WordTrace tailWord_3792931 prefixEnd_3792931 1298397794892403249146089 := by
  unfold tailWord_3792931
  simp only [CollatzResearch.WordTrace]
  refine ⟨138339558621866242887426647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92226372414577495258284431 138339558621866242887426647)
  ·
    refine ⟨207509337932799364331139971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138339558621866242887426647 207509337932799364331139971)
    ·
      refine ⟨311264006899199046496709957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207509337932799364331139971 311264006899199046496709957)
      ·
        refine ⟨58362001293599821218133117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311264006899199046496709957 58362001293599821218133117)
        ·
          refine ⟨21885750485099932956799919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58362001293599821218133117 21885750485099932956799919)
          ·
            refine ⟨32828625727649899435199879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21885750485099932956799919 32828625727649899435199879)
            ·
              refine ⟨49242938591474849152799819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32828625727649899435199879 49242938591474849152799819)
              ·
                refine ⟨73864407887212273729199729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49242938591474849152799819 73864407887212273729199729)
                ·
                  refine ⟨55398305915409205296899797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73864407887212273729199729 55398305915409205296899797)
                  ·
                    refine ⟨1298397794892403249146089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55398305915409205296899797 1298397794892403249146089)
                    ·
                      rfl

theorem cell22_3792931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_3792931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792931 prefixEnd_3792931 := by exact prefixLift 3792931
  have htrace : WordTrace (prefixWord ++ tailWord_3792931) baseStart_3792931 baseEnd_3792931 := by
    simpa [prefixWord, tailWord_3792931, baseEnd_3792931] using wordTrace_append hprefix tailTrace_3792931
  have hstable : (prefixWord ++ tailWord_3792931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792931).length < 2 ^ (prefixWord ++ tailWord_3792931).sum := by decide
  have hdescent : baseEnd_3792931 < baseStart_3792931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3792933 : List Nat := [1, 3, 1, 2, 2, 3, 4, 6]
def baseStart_3792933 : Nat := 118140960795 + 3792933 * 2 ^ 59
def prefixEnd_3792933 : Nat := 4983230072969 + 3 ^ 40 * 3792933 * 2
def baseEnd_3792933 : Nat := 144266497725919545621787

theorem tailTrace_3792933 : CollatzResearch.WordTrace tailWord_3792933 prefixEnd_3792933 144266497725919545621787 := by
  unfold tailWord_3792933
  simp only [CollatzResearch.WordTrace]
  refine ⟨138339631567858997228999453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92226421045239331485999635 138339631567858997228999453)
  ·
    refine ⟨51877361837947123960874795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138339631567858997228999453 51877361837947123960874795)
    ·
      refine ⟨77816042756920685941312193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51877361837947123960874795 77816042756920685941312193)
      ·
        refine ⟨58362032067690514455984145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77816042756920685941312193 58362032067690514455984145)
        ·
          refine ⟨43771524050767885841988109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58362032067690514455984145 43771524050767885841988109)
          ·
            refine ⟨16414321519037957190745541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43771524050767885841988109 16414321519037957190745541)
            ·
              refine ⟨3077685284819616973264789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16414321519037957190745541 3077685284819616973264789)
              ·
                refine ⟨144266497725919545621787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3077685284819616973264789 144266497725919545621787)
                ·
                  rfl

theorem cell22_3792933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 6].length) (baseStart_3792933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3792933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3792933 prefixEnd_3792933 := by exact prefixLift 3792933
  have htrace : WordTrace (prefixWord ++ tailWord_3792933) baseStart_3792933 baseEnd_3792933 := by
    simpa [prefixWord, tailWord_3792933, baseEnd_3792933] using wordTrace_append hprefix tailTrace_3792933
  have hstable : (prefixWord ++ tailWord_3792933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3792933).length < 2 ^ (prefixWord ++ tailWord_3792933).sum := by decide
  have hdescent : baseEnd_3792933 < baseStart_3792933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3792933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793055 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 1, 5]
def baseStart_3793055 : Nat := 118140960795 + 3793055 * 2 ^ 59
def prefixEnd_3793055 : Nat := 4983230072969 + 3 ^ 40 * 3793055 * 2
def baseEnd_3793055 : Nat := 1298440242626508259045709

theorem tailTrace_3793055 : CollatzResearch.WordTrace tailWord_3793055 prefixEnd_3793055 1298440242626508259045709 := by
  unfold tailWord_3793055
  simp only [CollatzResearch.WordTrace]
  refine ⟨138344081273417012064940619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92229387515611341376627079 138344081273417012064940619)
  ·
    refine ⟨207516121910125518097410929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138344081273417012064940619 207516121910125518097410929)
    ·
      refine ⟨155637091432594138573058197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207516121910125518097410929 155637091432594138573058197)
      ·
        refine ⟨7295488660902850245612103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155637091432594138573058197 7295488660902850245612103)
        ·
          refine ⟨10943232991354275368418155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7295488660902850245612103 10943232991354275368418155)
          ·
            refine ⟨16414849487031413052627233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10943232991354275368418155 16414849487031413052627233)
            ·
              refine ⟨12311137115273559789470425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16414849487031413052627233 12311137115273559789470425)
              ·
                refine ⟨9233352836455169842102819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12311137115273559789470425 9233352836455169842102819)
                ·
                  refine ⟨13850029254682754763154229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9233352836455169842102819 13850029254682754763154229)
                  ·
                    refine ⟨1298440242626508259045709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13850029254682754763154229 1298440242626508259045709)
                    ·
                      rfl

theorem cell22_3793055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_3793055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793055 prefixEnd_3793055 := by exact prefixLift 3793055
  have htrace : WordTrace (prefixWord ++ tailWord_3793055) baseStart_3793055 baseEnd_3793055 := by
    simpa [prefixWord, tailWord_3793055, baseEnd_3793055] using wordTrace_append hprefix tailTrace_3793055
  have hstable : (prefixWord ++ tailWord_3793055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793055).length < 2 ^ (prefixWord ++ tailWord_3793055).sum := by decide
  have hdescent : baseEnd_3793055 < baseStart_3793055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793057 : List Nat := [1, 2, 3, 3, 1, 3, 2, 3, 4]
def baseStart_3793057 : Nat := 118140960795 + 3793057 * 2 ^ 59
def prefixEnd_3793057 : Nat := 4983230072969 + 3 ^ 40 * 3793057 * 2
def baseEnd_3793057 : Nat := 432813642422460306831901

theorem tailTrace_3793057 : CollatzResearch.WordTrace tailWord_3793057 prefixEnd_3793057 432813642422460306831901 := by
  unfold tailWord_3793057
  simp only [CollatzResearch.WordTrace]
  refine ⟨138344154219409766406513425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92229436146273177604342283 138344154219409766406513425)
  ·
    refine ⟨103758115664557324804885069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138344154219409766406513425 103758115664557324804885069)
    ·
      refine ⟨38909293374208996801831901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103758115664557324804885069 38909293374208996801831901)
      ·
        refine ⟨14590985015328373800686963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38909293374208996801831901 14590985015328373800686963)
        ·
          refine ⟨21886477522992560701030445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14590985015328373800686963 21886477522992560701030445)
          ·
            refine ⟨8207429071122210262886417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21886477522992560701030445 8207429071122210262886417)
            ·
              refine ⟨6155571803341657697164813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8207429071122210262886417 6155571803341657697164813)
              ·
                refine ⟨2308339426253121636436805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6155571803341657697164813 2308339426253121636436805)
                ·
                  refine ⟨432813642422460306831901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2308339426253121636436805 432813642422460306831901)
                  ·
                    rfl

theorem cell22_3793057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 4].length) (baseStart_3793057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793057 prefixEnd_3793057 := by exact prefixLift 3793057
  have htrace : WordTrace (prefixWord ++ tailWord_3793057) baseStart_3793057 baseEnd_3793057 := by
    simpa [prefixWord, tailWord_3793057, baseEnd_3793057] using wordTrace_append hprefix tailTrace_3793057
  have hstable : (prefixWord ++ tailWord_3793057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793057).length < 2 ^ (prefixWord ++ tailWord_3793057).sum := by decide
  have hdescent : baseEnd_3793057 < baseStart_3793057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793089 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3793089 : Nat := 118140960795 + 3793089 * 2 ^ 59
def prefixEnd_3793089 : Nat := 4983230072969 + 3 ^ 40 * 3793089 * 2
def baseEnd_3793089 : Nat := 1298451881521343503695605

theorem tailTrace_3793089 : CollatzResearch.WordTrace tailWord_3793089 prefixEnd_3793089 1298451881521343503695605 := by
  unfold tailWord_3793089
  simp only [CollatzResearch.WordTrace]
  refine ⟨138345321355293835871678321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92230214236862557247785547 138345321355293835871678321)
  ·
    refine ⟨103758991016470376903758741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138345321355293835871678321 103758991016470376903758741)
    ·
      refine ⟨4863702703897048917363691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103758991016470376903758741 4863702703897048917363691)
      ·
        refine ⟨7295554055845573376045537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863702703897048917363691 7295554055845573376045537)
        ·
          refine ⟨5471665541884180032034153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7295554055845573376045537 5471665541884180032034153)
          ·
            refine ⟨4103749156413135024025615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5471665541884180032034153 4103749156413135024025615)
            ·
              refine ⟨6155623734619702536038423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4103749156413135024025615 6155623734619702536038423)
              ·
                refine ⟨9233435601929553804057635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6155623734619702536038423 9233435601929553804057635)
                ·
                  refine ⟨13850153402894330706086453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9233435601929553804057635 13850153402894330706086453)
                  ·
                    refine ⟨1298451881521343503695605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13850153402894330706086453 1298451881521343503695605)
                    ·
                      rfl

theorem cell22_3793089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3793089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793089 prefixEnd_3793089 := by exact prefixLift 3793089
  have htrace : WordTrace (prefixWord ++ tailWord_3793089) baseStart_3793089 baseEnd_3793089 := by
    simpa [prefixWord, tailWord_3793089, baseEnd_3793089] using wordTrace_append hprefix tailTrace_3793089
  have hstable : (prefixWord ++ tailWord_3793089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793089).length < 2 ^ (prefixWord ++ tailWord_3793089).sum := by decide
  have hdescent : baseEnd_3793089 < baseStart_3793089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793102 : List Nat := [4, 1, 1, 1, 4, 3, 2, 6]
def baseStart_3793102 : Nat := 118140960795 + 3793102 * 2 ^ 59
def prefixEnd_3793102 : Nat := 4983230072969 + 3 ^ 40 * 3793102 * 2
def baseEnd_3793102 : Nat := 144272925743001755902285

theorem tailTrace_3793102 : CollatzResearch.WordTrace tailWord_3793102 prefixEnd_3793102 144272925743001755902285 := by
  unfold tailWord_3793102
  simp only [CollatzResearch.WordTrace]
  refine ⟨17293224438030842386487695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92230530336164492727934373 17293224438030842386487695)
  ·
    refine ⟨25939836657046263579731543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17293224438030842386487695 25939836657046263579731543)
    ·
      refine ⟨38909754985569395369597315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25939836657046263579731543 38909754985569395369597315)
      ·
        refine ⟨58364632478354093054395973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38909754985569395369597315 58364632478354093054395973)
        ·
          refine ⟨10943368589691392447699245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58364632478354093054395973 10943368589691392447699245)
          ·
            refine ⟨4103763221134272167887217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10943368589691392447699245 4103763221134272167887217)
            ·
              refine ⟨3077822415850704125915413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4103763221134272167887217 3077822415850704125915413)
              ·
                refine ⟨144272925743001755902285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3077822415850704125915413 144272925743001755902285)
                ·
                  rfl

theorem cell22_3793102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_3793102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793102 prefixEnd_3793102 := by exact prefixLift 3793102
  have htrace : WordTrace (prefixWord ++ tailWord_3793102) baseStart_3793102 baseEnd_3793102 := by
    simpa [prefixWord, tailWord_3793102, baseEnd_3793102] using wordTrace_append hprefix tailTrace_3793102
  have hstable : (prefixWord ++ tailWord_3793102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793102).length < 2 ^ (prefixWord ++ tailWord_3793102).sum := by decide
  have hdescent : baseEnd_3793102 < baseStart_3793102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793113 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 7]
def baseStart_3793113 : Nat := 118140960795 + 3793113 * 2 ^ 59
def prefixEnd_3793113 : Nat := 4983230072969 + 3 ^ 40 * 3793113 * 2
def baseEnd_3793113 : Nat := 432820032403938480365177

theorem tailTrace_3793113 : CollatzResearch.WordTrace tailWord_3793113 prefixEnd_3793113 432820032403938480365177 := by
  unfold tailWord_3793113
  simp only [CollatzResearch.WordTrace]
  refine ⟨138346196707206887970551993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92230797804804591980367995 138346196707206887970551993)
  ·
    refine ⟨103759647530405165977913995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138346196707206887970551993 103759647530405165977913995)
    ·
      refine ⟨155639471295607748966870993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103759647530405165977913995 155639471295607748966870993)
      ·
        refine ⟨116729603471705811725153245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155639471295607748966870993 116729603471705811725153245)
        ·
          refine ⟨43773601301889679396932467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116729603471705811725153245 43773601301889679396932467)
          ·
            refine ⟨65660401952834519095398701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43773601301889679396932467 65660401952834519095398701)
            ·
              refine ⟨24622650732312944660774513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65660401952834519095398701 24622650732312944660774513)
              ·
                refine ⟨18466988049234708495580885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24622650732312944660774513 18466988049234708495580885)
                ·
                  refine ⟨432820032403938480365177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18466988049234708495580885 432820032403938480365177)
                  ·
                    rfl

theorem cell22_3793113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_3793113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793113 prefixEnd_3793113 := by exact prefixLift 3793113
  have htrace : WordTrace (prefixWord ++ tailWord_3793113) baseStart_3793113 baseEnd_3793113 := by
    simpa [prefixWord, tailWord_3793113, baseEnd_3793113] using wordTrace_append hprefix tailTrace_3793113
  have hstable : (prefixWord ++ tailWord_3793113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793113).length < 2 ^ (prefixWord ++ tailWord_3793113).sum := by decide
  have hdescent : baseEnd_3793113 < baseStart_3793113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793130 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_3793130 : Nat := 118140960795 + 3793130 * 2 ^ 59
def prefixEnd_3793130 : Nat := 4983230072969 + 3 ^ 40 * 3793130 * 2
def baseEnd_3793130 : Nat := 432821972219744354473493

theorem tailTrace_3793130 : CollatzResearch.WordTrace tailWord_3793130 prefixEnd_3793130 432821972219744354473493 := by
  unfold tailWord_3793130
  simp only [CollatzResearch.WordTrace]
  refine ⟨34586704187036324968480211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92231211165430199915947229 34586704187036324968480211)
  ·
    refine ⟨51880056280554487452720317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34586704187036324968480211 51880056280554487452720317)
    ·
      refine ⟨19455021105207932794770119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51880056280554487452720317 19455021105207932794770119)
      ·
        refine ⟨29182531657811899192155179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19455021105207932794770119 29182531657811899192155179)
        ·
          refine ⟨43773797486717848788232769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29182531657811899192155179 43773797486717848788232769)
          ·
            refine ⟨32830348115038386591174577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43773797486717848788232769 32830348115038386591174577)
            ·
              refine ⟨24622761086278789943380933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32830348115038386591174577 24622761086278789943380933)
              ·
                refine ⟨4616767703677273114383925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24622761086278789943380933 4616767703677273114383925)
                ·
                  refine ⟨432821972219744354473493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4616767703677273114383925 432821972219744354473493)
                  ·
                    rfl

theorem cell22_3793130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_3793130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793130 prefixEnd_3793130 := by exact prefixLift 3793130
  have htrace : WordTrace (prefixWord ++ tailWord_3793130) baseStart_3793130 baseEnd_3793130 := by
    simpa [prefixWord, tailWord_3793130, baseEnd_3793130] using wordTrace_append hprefix tailTrace_3793130
  have hstable : (prefixWord ++ tailWord_3793130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793130).length < 2 ^ (prefixWord ++ tailWord_3793130).sum := by decide
  have hdescent : baseEnd_3793130 < baseStart_3793130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793205 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3793205 : Nat := 118140960795 + 3793205 * 2 ^ 59
def prefixEnd_3793205 : Nat := 4983230072969 + 3 ^ 40 * 3793205 * 2
def baseEnd_3793205 : Nat := 1298491590691957867795249

theorem tailTrace_3793205 : CollatzResearch.WordTrace tailWord_3793205 prefixEnd_3793205 1298491590691957867795249 := by
  unfold tailWord_3793205
  simp only [CollatzResearch.WordTrace]
  refine ⟨138349552222873587682901069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92233034815249058455267379 138349552222873587682901069)
  ·
    refine ⟨51881082083577595381087901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138349552222873587682901069 51881082083577595381087901)
    ·
      refine ⟨19455405781341598267907963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51881082083577595381087901 19455405781341598267907963)
      ·
        refine ⟨29183108672012397401861945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19455405781341598267907963 29183108672012397401861945)
        ·
          refine ⟨21887331504009298051396459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29183108672012397401861945 21887331504009298051396459)
          ·
            refine ⟨32830997256013947077094689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21887331504009298051396459 32830997256013947077094689)
            ·
              refine ⟨24623247942010460307821017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32830997256013947077094689 24623247942010460307821017)
              ·
                refine ⟨18467435956507845230865763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24623247942010460307821017 18467435956507845230865763)
                ·
                  refine ⟨27701153934761767846298645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18467435956507845230865763 27701153934761767846298645)
                  ·
                    refine ⟨1298491590691957867795249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27701153934761767846298645 1298491590691957867795249)
                    ·
                      rfl

theorem cell22_3793205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3793205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793205 prefixEnd_3793205 := by exact prefixLift 3793205
  have htrace : WordTrace (prefixWord ++ tailWord_3793205) baseStart_3793205 baseEnd_3793205 := by
    simpa [prefixWord, tailWord_3793205, baseEnd_3793205] using wordTrace_append hprefix tailTrace_3793205
  have hstable : (prefixWord ++ tailWord_3793205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793205).length < 2 ^ (prefixWord ++ tailWord_3793205).sum := by decide
  have hdescent : baseEnd_3793205 < baseStart_3793205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793269 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3793269 : Nat := 118140960795 + 3793269 * 2 ^ 59
def prefixEnd_3793269 : Nat := 4983230072969 + 3 ^ 40 * 3793269 * 2
def baseEnd_3793269 : Nat := 1298513499199883034195053

theorem tailTrace_3793269 : CollatzResearch.WordTrace tailWord_3793269 prefixEnd_3793269 1298513499199883034195053 := by
  unfold tailWord_3793269
  simp only [CollatzResearch.WordTrace]
  refine ⟨138351886494641726613230861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92234590996427817742153907 138351886494641726613230861)
  ·
    refine ⟨51881957435490647479961573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138351886494641726613230861 51881957435490647479961573)
    ·
      refine ⟨9727867019154496402492795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51881957435490647479961573 9727867019154496402492795)
      ·
        refine ⟨14591800528731744603739193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9727867019154496402492795 14591800528731744603739193)
        ·
          refine ⟨10943850396548808452804395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14591800528731744603739193 10943850396548808452804395)
          ·
            refine ⟨16415775594823212679206593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10943850396548808452804395 16415775594823212679206593)
            ·
              refine ⟨12311831696117409509404945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16415775594823212679206593 12311831696117409509404945)
              ·
                refine ⟨9233873772088057132053709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12311831696117409509404945 9233873772088057132053709)
                ·
                  refine ⟨3462702664533021424520141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9233873772088057132053709 3462702664533021424520141)
                  ·
                    refine ⟨1298513499199883034195053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3462702664533021424520141 1298513499199883034195053)
                    ·
                      rfl

theorem cell22_3793269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3793269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793269 prefixEnd_3793269 := by exact prefixLift 3793269
  have htrace : WordTrace (prefixWord ++ tailWord_3793269) baseStart_3793269 baseEnd_3793269 := by
    simpa [prefixWord, tailWord_3793269, baseEnd_3793269] using wordTrace_append hprefix tailTrace_3793269
  have hstable : (prefixWord ++ tailWord_3793269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793269).length < 2 ^ (prefixWord ++ tailWord_3793269).sum := by decide
  have hdescent : baseEnd_3793269 < baseStart_3793269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793329 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 1, 4]
def baseStart_3793329 : Nat := 118140960795 + 3793329 * 2 ^ 59
def prefixEnd_3793329 : Nat := 4983230072969 + 3 ^ 40 * 3793329 * 2
def baseEnd_3793329 : Nat := 1298534038426062877694869

theorem tailTrace_3793329 : CollatzResearch.WordTrace tailWord_3793329 prefixEnd_3793329 1298534038426062877694869 := by
  unfold tailWord_3793329
  simp only [CollatzResearch.WordTrace]
  refine ⟨138354074874424356860415041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92236049916282904573610027 138354074874424356860415041)
  ·
    refine ⟨103765556155818267645311281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138354074874424356860415041 103765556155818267645311281)
    ·
      refine ⟨77824167116863700733983461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103765556155818267645311281 77824167116863700733983461)
      ·
        refine ⟨14592031334411943887621899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77824167116863700733983461 14592031334411943887621899)
        ·
          refine ⟨21888047001617915831432849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14592031334411943887621899 21888047001617915831432849)
          ·
            refine ⟨16416035251213436873574637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21888047001617915831432849 16416035251213436873574637)
            ·
              refine ⟨6156013219205038827590489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16416035251213436873574637 6156013219205038827590489)
              ·
                refine ⟨4617009914403779120692867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6156013219205038827590489 4617009914403779120692867)
                ·
                  refine ⟨6925514871605668681039301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4617009914403779120692867 6925514871605668681039301)
                  ·
                    refine ⟨1298534038426062877694869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6925514871605668681039301 1298534038426062877694869)
                    ·
                      rfl

theorem cell22_3793329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_3793329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793329 prefixEnd_3793329 := by exact prefixLift 3793329
  have htrace : WordTrace (prefixWord ++ tailWord_3793329) baseStart_3793329 baseEnd_3793329 := by
    simpa [prefixWord, tailWord_3793329, baseEnd_3793329] using wordTrace_append hprefix tailTrace_3793329
  have hstable : (prefixWord ++ tailWord_3793329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793329).length < 2 ^ (prefixWord ++ tailWord_3793329).sum := by decide
  have hdescent : baseEnd_3793329 < baseStart_3793329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793342 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3793342 : Nat := 118140960795 + 3793342 * 2 ^ 59
def prefixEnd_3793342 : Nat := 4983230072969 + 3 ^ 40 * 3793342 * 2
def baseEnd_3793342 : Nat := 1298538488591735177119829

theorem tailTrace_3793342 : CollatzResearch.WordTrace tailWord_3793342 prefixEnd_3793342 1298538488591735177119829 := by
  unfold tailWord_3793342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17294318627922157510079785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92236366015584840053758853 17294318627922157510079785)
  ·
    refine ⟨12970738970941618132559839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17294318627922157510079785 12970738970941618132559839)
    ·
      refine ⟨19456108456412427198839759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12970738970941618132559839 19456108456412427198839759)
      ·
        refine ⟨29184162684618640798259639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19456108456412427198839759 29184162684618640798259639)
        ·
          refine ⟨43776244026927961197389459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29184162684618640798259639 43776244026927961197389459)
          ·
            refine ⟨65664366040391941796084189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43776244026927961197389459 65664366040391941796084189)
            ·
              refine ⟨24624137265146978173531571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65664366040391941796084189 24624137265146978173531571)
              ·
                refine ⟨36936205897720467260297357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24624137265146978173531571 36936205897720467260297357)
                ·
                  refine ⟨13851077211645175222611509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36936205897720467260297357 13851077211645175222611509)
                  ·
                    refine ⟨1298538488591735177119829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13851077211645175222611509 1298538488591735177119829)
                    ·
                      rfl

theorem cell22_3793342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3793342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793342 prefixEnd_3793342 := by exact prefixLift 3793342
  have htrace : WordTrace (prefixWord ++ tailWord_3793342) baseStart_3793342 baseEnd_3793342 := by
    simpa [prefixWord, tailWord_3793342, baseEnd_3793342] using wordTrace_append hprefix tailTrace_3793342
  have hstable : (prefixWord ++ tailWord_3793342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793342).length < 2 ^ (prefixWord ++ tailWord_3793342).sum := by decide
  have hdescent : baseEnd_3793342 < baseStart_3793342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793410 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_3793410 : Nat := 118140960795 + 3793410 * 2 ^ 59
def prefixEnd_3793410 : Nat := 4983230072969 + 3 ^ 40 * 3793410 * 2
def baseEnd_3793410 : Nat := 1298561766381405666419621

theorem tailTrace_3793410 : CollatzResearch.WordTrace tailWord_3793410 prefixEnd_3793410 1298561766381405666419621 := by
  unfold tailWord_3793410
  simp only [CollatzResearch.WordTrace]
  refine ⟨34589257296782726923528421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92238019458087271796075789 34589257296782726923528421)
  ·
    refine ⟨6485485743146761298161579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34589257296782726923528421 6485485743146761298161579)
    ·
      refine ⟨9728228614720141947242369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6485485743146761298161579 9728228614720141947242369)
      ·
        refine ⟨7296171461040106460431777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9728228614720141947242369 7296171461040106460431777)
        ·
          refine ⟨5472128595780079845323833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7296171461040106460431777 5472128595780079845323833)
          ·
            refine ⟨4104096446835059883992875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5472128595780079845323833 4104096446835059883992875)
            ·
              refine ⟨6156144670252589825989313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104096446835059883992875 6156144670252589825989313)
              ·
                refine ⟨4617108502689442369491985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6156144670252589825989313 4617108502689442369491985)
                ·
                  refine ⟨3462831377017081777118989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4617108502689442369491985 3462831377017081777118989)
                  ·
                    refine ⟨1298561766381405666419621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3462831377017081777118989 1298561766381405666419621)
                    ·
                      rfl

theorem cell22_3793410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_3793410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793410 prefixEnd_3793410 := by exact prefixLift 3793410
  have htrace : WordTrace (prefixWord ++ tailWord_3793410) baseStart_3793410 baseEnd_3793410 := by
    simpa [prefixWord, tailWord_3793410, baseEnd_3793410] using wordTrace_append hprefix tailTrace_3793410
  have hstable : (prefixWord ++ tailWord_3793410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793410).length < 2 ^ (prefixWord ++ tailWord_3793410).sum := by decide
  have hdescent : baseEnd_3793410 < baseStart_3793410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793417 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 5]
def baseStart_3793417 : Nat := 118140960795 + 3793417 * 2 ^ 59
def prefixEnd_3793417 : Nat := 4983230072969 + 3 ^ 40 * 3793417 * 2
def baseEnd_3793417 : Nat := 432854720874819993831533

theorem tailTrace_3793417 : CollatzResearch.WordTrace tailWord_3793417 prefixEnd_3793417 432854720874819993831533 := by
  unfold tailWord_3793417
  simp only [CollatzResearch.WordTrace]
  refine ⟨138357284498105547889618505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92238189665403698593079003 138357284498105547889618505)
  ·
    refine ⟨103767963373579160917213879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138357284498105547889618505 103767963373579160917213879)
    ·
      refine ⟨155651945060368741375820819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103767963373579160917213879 155651945060368741375820819)
      ·
        refine ⟨233477917590553112063731229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155651945060368741375820819 233477917590553112063731229)
        ·
          refine ⟨87554219096457417023899211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233477917590553112063731229 87554219096457417023899211)
          ·
            refine ⟨131331328644686125535848817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87554219096457417023899211 131331328644686125535848817)
            ·
              refine ⟨98498496483514594151886613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131331328644686125535848817 98498496483514594151886613)
              ·
                refine ⟨4617117022664746600869685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98498496483514594151886613 4617117022664746600869685)
                ·
                  refine ⟨432854720874819993831533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4617117022664746600869685 432854720874819993831533)
                  ·
                    rfl

theorem cell22_3793417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_3793417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793417 prefixEnd_3793417 := by exact prefixLift 3793417
  have htrace : WordTrace (prefixWord ++ tailWord_3793417) baseStart_3793417 baseEnd_3793417 := by
    simpa [prefixWord, tailWord_3793417, baseEnd_3793417] using wordTrace_append hprefix tailTrace_3793417
  have hstable : (prefixWord ++ tailWord_3793417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793417).length < 2 ^ (prefixWord ++ tailWord_3793417).sum := by decide
  have hdescent : baseEnd_3793417 < baseStart_3793417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793464 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 1, 4]
def baseStart_3793464 : Nat := 118140960795 + 3793464 * 2 ^ 59
def prefixEnd_3793464 : Nat := 4983230072969 + 3 ^ 40 * 3793464 * 2
def baseEnd_3793464 : Nat := 1298580251684967525569455

theorem tailTrace_3793464 : CollatzResearch.WordTrace tailWord_3793464 prefixEnd_3793464 1298580251684967525569455 := by
  unfold tailWord_3793464
  simp only [CollatzResearch.WordTrace]
  refine ⟨69179499364467637458289723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92239332485956849944386297 69179499364467637458289723)
  ·
    refine ⟨103769249046701456187434585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69179499364467637458289723 103769249046701456187434585)
    ·
      refine ⟨77826936785026092140575939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103769249046701456187434585 77826936785026092140575939)
      ·
        refine ⟨116740405177539138210863909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77826936785026092140575939 116740405177539138210863909)
        ·
          refine ⟨21888825970788588414536983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116740405177539138210863909 21888825970788588414536983)
          ·
            refine ⟨32833238956182882621805475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21888825970788588414536983 32833238956182882621805475)
            ·
              refine ⟨49249858434274323932708213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32833238956182882621805475 49249858434274323932708213)
              ·
                refine ⟨4617174228213217868691395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49249858434274323932708213 4617174228213217868691395)
                ·
                  refine ⟨6925761342319826803037093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4617174228213217868691395 6925761342319826803037093)
                  ·
                    refine ⟨1298580251684967525569455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6925761342319826803037093 1298580251684967525569455)
                    ·
                      rfl

theorem cell22_3793464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_3793464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793464 prefixEnd_3793464 := by exact prefixLift 3793464
  have htrace : WordTrace (prefixWord ++ tailWord_3793464) baseStart_3793464 baseEnd_3793464 := by
    simpa [prefixWord, tailWord_3793464, baseEnd_3793464] using wordTrace_append hprefix tailTrace_3793464
  have hstable : (prefixWord ++ tailWord_3793464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793464).length < 2 ^ (prefixWord ++ tailWord_3793464).sum := by decide
  have hdescent : baseEnd_3793464 < baseStart_3793464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793479 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 6]
def baseStart_3793479 : Nat := 118140960795 + 3793479 * 2 ^ 59
def prefixEnd_3793479 : Nat := 4983230072969 + 3 ^ 40 * 3793479 * 2
def baseEnd_3793479 : Nat := 432861795497170828814803

theorem tailTrace_3793479 : CollatzResearch.WordTrace tailWord_3793479 prefixEnd_3793479 432861795497170828814803 := by
  unfold tailWord_3793479
  simp only [CollatzResearch.WordTrace]
  refine ⟨138359545823880932478375491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92239697215920621652250327 138359545823880932478375491)
  ·
    refine ⟨207539318735821398717563237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138359545823880932478375491 207539318735821398717563237)
    ·
      refine ⟨38913622262966512259543107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207539318735821398717563237 38913622262966512259543107)
      ·
        refine ⟨58370433394449768389314661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38913622262966512259543107 58370433394449768389314661)
        ·
          refine ⟨10944456261459331572996499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58370433394449768389314661 10944456261459331572996499)
          ·
            refine ⟨16416684392188997359494749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10944456261459331572996499 16416684392188997359494749)
            ·
              refine ⟨6156256647070874009810531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16416684392188997359494749 6156256647070874009810531)
              ·
                refine ⟨9234384970606311014715797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156256647070874009810531 9234384970606311014715797)
                ·
                  refine ⟨432861795497170828814803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9234384970606311014715797 432861795497170828814803)
                  ·
                    rfl

theorem cell22_3793479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 6].length) (baseStart_3793479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793479 prefixEnd_3793479 := by exact prefixLift 3793479
  have htrace : WordTrace (prefixWord ++ tailWord_3793479) baseStart_3793479 baseEnd_3793479 := by
    simpa [prefixWord, tailWord_3793479, baseEnd_3793479] using wordTrace_append hprefix tailTrace_3793479
  have hstable : (prefixWord ++ tailWord_3793479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793479).length < 2 ^ (prefixWord ++ tailWord_3793479).sum := by decide
  have hdescent : baseEnd_3793479 < baseStart_3793479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793507 : List Nat := [1, 1, 1, 5, 1, 2, 1, 10]
def baseStart_3793507 : Nat := 118140960795 + 3793507 * 2 ^ 59
def prefixEnd_3793507 : Nat := 4983230072969 + 3 ^ 40 * 3793507 * 2
def baseEnd_3793507 : Nat := 144288330162636638527147

theorem tailTrace_3793507 : CollatzResearch.WordTrace tailWord_3793507 prefixEnd_3793507 144288330162636638527147 := by
  unfold tailWord_3793507
  simp only [CollatzResearch.WordTrace]
  refine ⟨138360567067779493260394775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92240378045186328840263183 138360567067779493260394775)
  ·
    refine ⟨207540850601669239890592163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138360567067779493260394775 207540850601669239890592163)
    ·
      refine ⟨311311275902503859835888245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207540850601669239890592163 311311275902503859835888245)
      ·
        refine ⟨29185432115859736859614523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311311275902503859835888245 29185432115859736859614523)
        ·
          refine ⟨43778148173789605289421785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29185432115859736859614523 43778148173789605289421785)
          ·
            refine ⟨32833611130342203967066339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43778148173789605289421785 32833611130342203967066339)
            ·
              refine ⟨49250416695513305950599509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32833611130342203967066339 49250416695513305950599509)
              ·
                refine ⟨144288330162636638527147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49250416695513305950599509 144288330162636638527147)
                ·
                  rfl

theorem cell22_3793507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 10].length) (baseStart_3793507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793507 prefixEnd_3793507 := by exact prefixLift 3793507
  have htrace : WordTrace (prefixWord ++ tailWord_3793507) baseStart_3793507 baseEnd_3793507 := by
    simpa [prefixWord, tailWord_3793507, baseEnd_3793507] using wordTrace_append hprefix tailTrace_3793507
  have hstable : (prefixWord ++ tailWord_3793507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793507).length < 2 ^ (prefixWord ++ tailWord_3793507).sum := by decide
  have hdescent : baseEnd_3793507 < baseStart_3793507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793552 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 11]
def baseStart_3793552 : Nat := 118140960795 + 3793552 * 2 ^ 59
def prefixEnd_3793552 : Nat := 4983230072969 + 3 ^ 40 * 3793552 * 2
def baseEnd_3793552 : Nat := 432870125294454876456395

theorem tailTrace_3793552 : CollatzResearch.WordTrace tailWord_3793552 prefixEnd_3793552 432870125294454876456395 := by
  unfold tailWord_3793552
  simp only [CollatzResearch.WordTrace]
  refine ⟨69181104176308232972891455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92241472235077643963855273 69181104176308232972891455)
  ·
    refine ⟨103771656264462349459337183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69181104176308232972891455 103771656264462349459337183)
    ·
      refine ⟨155657484396693524189005775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103771656264462349459337183 155657484396693524189005775)
      ·
        refine ⟨233486226595040286283508663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155657484396693524189005775 233486226595040286283508663)
        ·
          refine ⟨350229339892560429425262995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233486226595040286283508663 350229339892560429425262995)
          ·
            refine ⟨525344009838840644137894493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350229339892560429425262995 525344009838840644137894493)
            ·
              refine ⟨197004003689565241551710435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 525344009838840644137894493 197004003689565241551710435)
              ·
                refine ⟨295506005534347862327565653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197004003689565241551710435 295506005534347862327565653)
                ·
                  refine ⟨432870125294454876456395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 295506005534347862327565653 432870125294454876456395)
                  ·
                    rfl

theorem cell22_3793552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_3793552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793552 prefixEnd_3793552 := by exact prefixLift 3793552
  have htrace : WordTrace (prefixWord ++ tailWord_3793552) baseStart_3793552 baseEnd_3793552 := by
    simpa [prefixWord, tailWord_3793552, baseEnd_3793552] using wordTrace_append hprefix tailTrace_3793552
  have hstable : (prefixWord ++ tailWord_3793552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793552).length < 2 ^ (prefixWord ++ tailWord_3793552).sum := by decide
  have hdescent : baseEnd_3793552 < baseStart_3793552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793648 : List Nat := [2, 1, 1, 1, 3, 1, 7, 2, 4]
def baseStart_3793648 : Nat := 118140960795 + 3793648 * 2 ^ 59
def prefixEnd_3793648 : Nat := 4983230072969 + 3 ^ 40 * 3793648 * 2
def baseEnd_3793648 : Nat := 432881079548417459656297

theorem tailTrace_3793648 : CollatzResearch.WordTrace tailWord_3793648 prefixEnd_3793648 432881079548417459656297 := by
  unfold tailWord_3793648
  simp only [CollatzResearch.WordTrace]
  refine ⟨69182854880134337170638799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92243806506845782894185065 69182854880134337170638799)
  ·
    refine ⟨103774282320201505755958199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69182854880134337170638799 103774282320201505755958199)
    ·
      refine ⟨155661423480302258633937299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103774282320201505755958199 155661423480302258633937299)
      ·
        refine ⟨233492135220453387950905949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155661423480302258633937299 233492135220453387950905949)
        ·
          refine ⟨87559550707670020481589731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233492135220453387950905949 87559550707670020481589731)
          ·
            refine ⟨131339326061505030722384597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87559550707670020481589731 131339326061505030722384597)
            ·
              refine ⟨3078265454566524157555889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 131339326061505030722384597 3078265454566524157555889)
              ·
                refine ⟨2308699090924893118166917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3078265454566524157555889 2308699090924893118166917)
                ·
                  refine ⟨432881079548417459656297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2308699090924893118166917 432881079548417459656297)
                  ·
                    rfl

theorem cell22_3793648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 4].length) (baseStart_3793648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793648 prefixEnd_3793648 := by exact prefixLift 3793648
  have htrace : WordTrace (prefixWord ++ tailWord_3793648) baseStart_3793648 baseEnd_3793648 := by
    simpa [prefixWord, tailWord_3793648, baseEnd_3793648] using wordTrace_append hprefix tailTrace_3793648
  have hstable : (prefixWord ++ tailWord_3793648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793648).length < 2 ^ (prefixWord ++ tailWord_3793648).sum := by decide
  have hdescent : baseEnd_3793648 < baseStart_3793648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793693 : List Nat := [1, 4, 2, 4, 2, 9]
def baseStart_3793693 : Nat := 118140960795 + 3793693 * 2 ^ 59
def prefixEnd_3793693 : Nat := 4983230072969 + 3 ^ 40 * 3793693 * 2
def baseEnd_3793693 : Nat := 16032822753887497056713

theorem tailTrace_3793693 : CollatzResearch.WordTrace tailWord_3793693 prefixEnd_3793693 16032822753887497056713 := by
  unfold tailWord_3793693
  simp only [CollatzResearch.WordTrace]
  refine ⟨138367351045105647026665733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92244900696737098017777155 138367351045105647026665733)
  ·
    refine ⟨25943878320957308817499825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138367351045105647026665733 25943878320957308817499825)
    ·
      refine ⟨19457908740717981613124869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25943878320957308817499825 19457908740717981613124869)
      ·
        refine ⟨3648357888884621552460913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19457908740717981613124869 3648357888884621552460913)
        ·
          refine ⟨2736268416663466164345685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3648357888884621552460913 2736268416663466164345685)
          ·
            refine ⟨16032822753887497056713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2736268416663466164345685 16032822753887497056713)
            ·
              rfl

theorem cell22_3793693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 9].length) (baseStart_3793693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793693 prefixEnd_3793693 := by exact prefixLift 3793693
  have htrace : WordTrace (prefixWord ++ tailWord_3793693) baseStart_3793693 baseEnd_3793693 := by
    simpa [prefixWord, tailWord_3793693, baseEnd_3793693] using wordTrace_append hprefix tailTrace_3793693
  have hstable : (prefixWord ++ tailWord_3793693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793693).length < 2 ^ (prefixWord ++ tailWord_3793693).sum := by decide
  have hdescent : baseEnd_3793693 < baseStart_3793693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793725 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_3793725 : Nat := 118140960795 + 3793725 * 2 ^ 59
def prefixEnd_3793725 : Nat := 4983230072969 + 3 ^ 40 * 3793725 * 2
def baseEnd_3793725 : Nat := 1298669597318849844793655

theorem tailTrace_3793725 : CollatzResearch.WordTrace tailWord_3793725 prefixEnd_3793725 1298669597318849844793655 := by
  unfold tailWord_3793725
  simp only [CollatzResearch.WordTrace]
  refine ⟨138368518180989716491830629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92245678787326477661220419 138368518180989716491830629)
  ·
    refine ⟨25944097158935571842218243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138368518180989716491830629 25944097158935571842218243)
    ·
      refine ⟨38916145738403357763327365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25944097158935571842218243 38916145738403357763327365)
      ·
        refine ⟨7296777325950629580623881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38916145738403357763327365 7296777325950629580623881)
        ·
          refine ⟨5472582994462972185467911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7296777325950629580623881 5472582994462972185467911)
          ·
            refine ⟨8208874491694458278201867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5472582994462972185467911 8208874491694458278201867)
            ·
              refine ⟨12313311737541687417302801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8208874491694458278201867 12313311737541687417302801)
              ·
                refine ⟨9234983803156265562977101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12313311737541687417302801 9234983803156265562977101)
                ·
                  refine ⟨3463118926183599586116413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9234983803156265562977101 3463118926183599586116413)
                  ·
                    refine ⟨1298669597318849844793655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3463118926183599586116413 1298669597318849844793655)
                    ·
                      rfl

theorem cell22_3793725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_3793725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793725 prefixEnd_3793725 := by exact prefixLift 3793725
  have htrace : WordTrace (prefixWord ++ tailWord_3793725) baseStart_3793725 baseEnd_3793725 := by
    simpa [prefixWord, tailWord_3793725, baseEnd_3793725] using wordTrace_append hprefix tailTrace_3793725
  have hstable : (prefixWord ++ tailWord_3793725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793725).length < 2 ^ (prefixWord ++ tailWord_3793725).sum := by decide
  have hdescent : baseEnd_3793725 < baseStart_3793725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793800 : List Nat := [2, 1, 3, 3, 2, 1, 3, 3, 4]
def baseStart_3793800 : Nat := 118140960795 + 3793800 * 2 ^ 59
def prefixEnd_3793800 : Nat := 4983230072969 + 3 ^ 40 * 3793800 * 2
def baseEnd_3793800 : Nat := 432898423783858216389475

theorem tailTrace_3793800 : CollatzResearch.WordTrace tailWord_3793800 prefixEnd_3793800 432898423783858216389475 := by
  unfold tailWord_3793800
  simp only [CollatzResearch.WordTrace]
  refine ⟨69185626827859002150405427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92247502437145336200540569 69185626827859002150405427)
  ·
    refine ⟨103778440241788503225608141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69185626827859002150405427 103778440241788503225608141)
    ·
      refine ⟨38916915090670688709603053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103778440241788503225608141 38916915090670688709603053)
      ·
        refine ⟨14593843159001508266101145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38916915090670688709603053 14593843159001508266101145)
        ·
          refine ⟨10945382369251131199575859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14593843159001508266101145 10945382369251131199575859)
          ·
            refine ⟨16418073553876696799363789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10945382369251131199575859 16418073553876696799363789)
            ·
              refine ⟨6156777582703761299761421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16418073553876696799363789 6156777582703761299761421)
              ·
                refine ⟨2308791593513910487410533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6156777582703761299761421 2308791593513910487410533)
                ·
                  refine ⟨432898423783858216389475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2308791593513910487410533 432898423783858216389475)
                  ·
                    rfl

theorem cell22_3793800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 3, 4].length) (baseStart_3793800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793800 prefixEnd_3793800 := by exact prefixLift 3793800
  have htrace : WordTrace (prefixWord ++ tailWord_3793800) baseStart_3793800 baseEnd_3793800 := by
    simpa [prefixWord, tailWord_3793800, baseEnd_3793800] using wordTrace_append hprefix tailTrace_3793800
  have hstable : (prefixWord ++ tailWord_3793800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793800).length < 2 ^ (prefixWord ++ tailWord_3793800).sum := by decide
  have hdescent : baseEnd_3793800 < baseStart_3793800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793813 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3793813 : Nat := 118140960795 + 3793813 * 2 ^ 59
def prefixEnd_3793813 : Nat := 4983230072969 + 3 ^ 40 * 3793813 * 2
def baseEnd_3793813 : Nat := 1298699721517246948593385

theorem tailTrace_3793813 : CollatzResearch.WordTrace tailWord_3793813 prefixEnd_3793813 1298699721517246948593385 := by
  unfold tailWord_3793813
  simp only [CollatzResearch.WordTrace]
  refine ⟨138371727804670907521034093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92247818536447271680689395 138371727804670907521034093)
  ·
    refine ⟨51889397926751590320387785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138371727804670907521034093 51889397926751590320387785)
    ·
      refine ⟨38917048445063692740290839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51889397926751590320387785 38917048445063692740290839)
      ·
        refine ⟨58375572667595539110436259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38917048445063692740290839 58375572667595539110436259)
        ·
          refine ⟨87563359001393308665654389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58375572667595539110436259 87563359001393308665654389)
          ·
            refine ⟨8209064906380622687405099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87563359001393308665654389 8209064906380622687405099)
            ·
              refine ⟨12313597359570934031107649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209064906380622687405099 12313597359570934031107649)
              ·
                refine ⟨9235198019678200523330737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12313597359570934031107649 9235198019678200523330737)
                ·
                  refine ⟨6926398514758650392498053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9235198019678200523330737 6926398514758650392498053)
                  ·
                    refine ⟨1298699721517246948593385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6926398514758650392498053 1298699721517246948593385)
                    ·
                      rfl

theorem cell22_3793813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3793813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793813 prefixEnd_3793813 := by exact prefixLift 3793813
  have htrace : WordTrace (prefixWord ++ tailWord_3793813) baseStart_3793813 baseEnd_3793813 := by
    simpa [prefixWord, tailWord_3793813, baseEnd_3793813] using wordTrace_append hprefix tailTrace_3793813
  have hstable : (prefixWord ++ tailWord_3793813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793813).length < 2 ^ (prefixWord ++ tailWord_3793813).sum := by decide
  have hdescent : baseEnd_3793813 < baseStart_3793813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793862 : List Nat := [6, 1, 3, 1, 11]
def baseStart_3793862 : Nat := 118140960795 + 3793862 * 2 ^ 59
def prefixEnd_3793862 : Nat := 4983230072969 + 3 ^ 40 * 3793862 * 2
def baseEnd_3793862 : Nat := 5344512326002580881145

theorem tailTrace_3793862 : CollatzResearch.WordTrace tailWord_3793862 prefixEnd_3793862 5344512326002580881145 := by
  unfold tailWord_3793862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324172343171668402798995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92249009987662259259711893 4324172343171668402798995)
  ·
    refine ⟨6486258514757502604198493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4324172343171668402798995 6486258514757502604198493)
    ·
      refine ⟨2432346943034063476574435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6486258514757502604198493 2432346943034063476574435)
      ·
        refine ⟨3648520414551095214861653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432346943034063476574435 3648520414551095214861653)
        ·
          refine ⟨5344512326002580881145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3648520414551095214861653 5344512326002580881145)
          ·
            rfl

theorem cell22_3793862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 11].length) (baseStart_3793862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793862 prefixEnd_3793862 := by exact prefixLift 3793862
  have htrace : WordTrace (prefixWord ++ tailWord_3793862) baseStart_3793862 baseEnd_3793862 := by
    simpa [prefixWord, tailWord_3793862, baseEnd_3793862] using wordTrace_append hprefix tailTrace_3793862
  have hstable : (prefixWord ++ tailWord_3793862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793862).length < 2 ^ (prefixWord ++ tailWord_3793862).sum := by decide
  have hdescent : baseEnd_3793862 < baseStart_3793862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793873 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 5]
def baseStart_3793873 : Nat := 118140960795 + 3793873 * 2 ^ 59
def prefixEnd_3793873 : Nat := 4983230072969 + 3 ^ 40 * 3793873 * 2
def baseEnd_3793873 : Nat := 432906753581142264031067

theorem tailTrace_3793873 : CollatzResearch.WordTrace tailWord_3793873 prefixEnd_3793873 432906753581142264031067 := by
  unfold tailWord_3793873
  simp only [CollatzResearch.WordTrace]
  refine ⟨138373916184453537768218273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92249277456302358512145515 138373916184453537768218273)
  ·
    refine ⟨103780437138340153326163705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138373916184453537768218273 103780437138340153326163705)
    ·
      refine ⟨77835327853755114994622779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103780437138340153326163705 77835327853755114994622779)
      ·
        refine ⟨116752991780632672491934169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77835327853755114994622779 116752991780632672491934169)
        ·
          refine ⟨87564743835474504368950627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116752991780632672491934169 87564743835474504368950627)
          ·
            refine ⟨131347115753211756553425941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87564743835474504368950627 131347115753211756553425941)
            ·
              refine ⟨6156896050931801088441841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131347115753211756553425941 6156896050931801088441841)
              ·
                refine ⟨4617672038198850816331381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6156896050931801088441841 4617672038198850816331381)
                ·
                  refine ⟨432906753581142264031067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4617672038198850816331381 432906753581142264031067)
                  ·
                    rfl

theorem cell22_3793873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_3793873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793873 prefixEnd_3793873 := by exact prefixLift 3793873
  have htrace : WordTrace (prefixWord ++ tailWord_3793873) baseStart_3793873 baseEnd_3793873 := by
    simpa [prefixWord, tailWord_3793873, baseEnd_3793873] using wordTrace_append hprefix tailTrace_3793873
  have hstable : (prefixWord ++ tailWord_3793873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793873).length < 2 ^ (prefixWord ++ tailWord_3793873).sum := by decide
  have hdescent : baseEnd_3793873 < baseStart_3793873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793903 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 3, 4]
def baseStart_3793903 : Nat := 118140960795 + 3793903 * 2 ^ 59
def prefixEnd_3793903 : Nat := 4983230072969 + 3 ^ 40 * 3793903 * 2
def baseEnd_3793903 : Nat := 1298730530356516713843109

theorem tailTrace_3793903 : CollatzResearch.WordTrace tailWord_3793903 prefixEnd_3793903 1298730530356516713843109 := by
  unfold tailWord_3793903
  simp only [CollatzResearch.WordTrace]
  refine ⟨138375010374344852891810363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92250006916229901927873575 138375010374344852891810363)
  ·
    refine ⟨207562515561517279337715545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138375010374344852891810363 207562515561517279337715545)
    ·
      refine ⟨155671886671137959503286659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207562515561517279337715545 155671886671137959503286659)
      ·
        refine ⟨233507830006706939254929989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155671886671137959503286659 233507830006706939254929989)
        ·
          refine ⟨43782718126257551110299373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233507830006706939254929989 43782718126257551110299373)
          ·
            refine ⟨16418519297346581666362265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43782718126257551110299373 16418519297346581666362265)
            ·
              refine ⟨12313889473009936249771699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16418519297346581666362265 12313889473009936249771699)
              ·
                refine ⟨18470834209514904374657549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12313889473009936249771699 18470834209514904374657549)
                ·
                  refine ⟨6926562828568089140496581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18470834209514904374657549 6926562828568089140496581)
                  ·
                    refine ⟨1298730530356516713843109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6926562828568089140496581 1298730530356516713843109)
                    ·
                      rfl

theorem cell22_3793903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_3793903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793903 prefixEnd_3793903 := by exact prefixLift 3793903
  have htrace : WordTrace (prefixWord ++ tailWord_3793903) baseStart_3793903 baseEnd_3793903 := by
    simpa [prefixWord, tailWord_3793903, baseEnd_3793903] using wordTrace_append hprefix tailTrace_3793903
  have hstable : (prefixWord ++ tailWord_3793903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793903).length < 2 ^ (prefixWord ++ tailWord_3793903).sum := by decide
  have hdescent : baseEnd_3793903 < baseStart_3793903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3793982 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3793982 : Nat := 118140960795 + 3793982 * 2 ^ 59
def prefixEnd_3793982 : Nat := 4983230072969 + 3 ^ 40 * 3793982 * 2
def baseEnd_3793982 : Nat := 1298757573670986841117867

theorem tailTrace_3793982 : CollatzResearch.WordTrace tailWord_3793982 prefixEnd_3793982 1298757573670986841117867 := by
  unfold tailWord_3793982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17297236467632331172992025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92251927827372432922624133 17297236467632331172992025)
  ·
    refine ⟨12972927350724248379744019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17297236467632331172992025 12972927350724248379744019)
    ·
      refine ⟨19459391026086372569616029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12972927350724248379744019 19459391026086372569616029)
      ·
        refine ⟨7297271634782389713606011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19459391026086372569616029 7297271634782389713606011)
        ·
          refine ⟨10945907452173584570409017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7297271634782389713606011 10945907452173584570409017)
          ·
            refine ⟨8209430589130188427806763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10945907452173584570409017 8209430589130188427806763)
            ·
              refine ⟨12314145883695282641710145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209430589130188427806763 12314145883695282641710145)
              ·
                refine ⟨9235609412771461981282609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12314145883695282641710145 9235609412771461981282609)
                ·
                  refine ⟨6926707059578596485961957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9235609412771461981282609 6926707059578596485961957)
                  ·
                    refine ⟨1298757573670986841117867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6926707059578596485961957 1298757573670986841117867)
                    ·
                      rfl

theorem cell22_3793982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3793982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3793982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3793982 prefixEnd_3793982 := by exact prefixLift 3793982
  have htrace : WordTrace (prefixWord ++ tailWord_3793982) baseStart_3793982 baseEnd_3793982 := by
    simpa [prefixWord, tailWord_3793982, baseEnd_3793982] using wordTrace_append hprefix tailTrace_3793982
  have hstable : (prefixWord ++ tailWord_3793982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3793982).length < 2 ^ (prefixWord ++ tailWord_3793982).sum := by decide
  have hdescent : baseEnd_3793982 < baseStart_3793982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3793982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794085 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_3794085 : Nat := 118140960795 + 3794085 * 2 ^ 59
def prefixEnd_3794085 : Nat := 4983230072969 + 3 ^ 40 * 3794085 * 2
def baseEnd_3794085 : Nat := 1298792832675928905792551

theorem tailTrace_3794085 : CollatzResearch.WordTrace tailWord_3794085 prefixEnd_3794085 1298792832675928905792551 := by
  unfold tailWord_3794085
  simp only [CollatzResearch.WordTrace]
  refine ⟨138381648459685497974935709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92254432306456998649957139 138381648459685497974935709)
  ·
    refine ⟨51893118172382061740600891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138381648459685497974935709 51893118172382061740600891)
    ·
      refine ⟨77839677258573092610901337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51893118172382061740600891 77839677258573092610901337)
      ·
        refine ⟨58379757943929819458176003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77839677258573092610901337 58379757943929819458176003)
        ·
          refine ⟨87569636915894729187264005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58379757943929819458176003 87569636915894729187264005)
          ·
            refine ⟨16419306921730261722612001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87569636915894729187264005 16419306921730261722612001)
            ·
              refine ⟨12314480191297696291959001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16419306921730261722612001 12314480191297696291959001)
              ·
                refine ⟨9235860143473272218969251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12314480191297696291959001 9235860143473272218969251)
                ·
                  refine ⟨13853790215209908328453877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9235860143473272218969251 13853790215209908328453877)
                  ·
                    refine ⟨1298792832675928905792551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13853790215209908328453877 1298792832675928905792551)
                    ·
                      rfl

theorem cell22_3794085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_3794085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794085 prefixEnd_3794085 := by exact prefixLift 3794085
  have htrace : WordTrace (prefixWord ++ tailWord_3794085) baseStart_3794085 baseEnd_3794085 := by
    simpa [prefixWord, tailWord_3794085, baseEnd_3794085] using wordTrace_append hprefix tailTrace_3794085
  have hstable : (prefixWord ++ tailWord_3794085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794085).length < 2 ^ (prefixWord ++ tailWord_3794085).sum := by decide
  have hdescent : baseEnd_3794085 < baseStart_3794085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794130 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_3794130 : Nat := 118140960795 + 3794130 * 2 ^ 59
def prefixEnd_3794130 : Nat := 4983230072969 + 3 ^ 40 * 3794130 * 2
def baseEnd_3794130 : Nat := 1298808237095563788417413

theorem tailTrace_3794130 : CollatzResearch.WordTrace tailWord_3794130 prefixEnd_3794130 1298808237095563788417413 := by
  unfold tailWord_3794130
  simp only [CollatzResearch.WordTrace]
  refine ⟨34595822436130617665080961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92255526496348313773549229 34595822436130617665080961)
  ·
    refine ⟨25946866827097963248810721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34595822436130617665080961 25946866827097963248810721)
    ·
      refine ⟨19460150120323472436608041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25946866827097963248810721 19460150120323472436608041)
      ·
        refine ⟨14595112590242604327456031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19460150120323472436608041 14595112590242604327456031)
        ·
          refine ⟨21892668885363906491184047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14595112590242604327456031 21892668885363906491184047)
          ·
            refine ⟨32839003328045859736776071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21892668885363906491184047 32839003328045859736776071)
            ·
              refine ⟨49258504992068789605164107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32839003328045859736776071 49258504992068789605164107)
              ·
                refine ⟨73887757488103184407746161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49258504992068789605164107 73887757488103184407746161)
                ·
                  refine ⟨55415818116077388305809621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73887757488103184407746161 55415818116077388305809621)
                  ·
                    refine ⟨1298808237095563788417413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55415818116077388305809621 1298808237095563788417413)
                    ·
                      rfl

theorem cell22_3794130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_3794130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794130 prefixEnd_3794130 := by exact prefixLift 3794130
  have htrace : WordTrace (prefixWord ++ tailWord_3794130) baseStart_3794130 baseEnd_3794130 := by
    simpa [prefixWord, tailWord_3794130, baseEnd_3794130] using wordTrace_append hprefix tailTrace_3794130
  have hstable : (prefixWord ++ tailWord_3794130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794130).length < 2 ^ (prefixWord ++ tailWord_3794130).sum := by decide
  have hdescent : baseEnd_3794130 < baseStart_3794130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794177 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 5]
def baseStart_3794177 : Nat := 118140960795 + 3794177 * 2 ^ 59
def prefixEnd_3794177 : Nat := 4983230072969 + 3 ^ 40 * 3794177 * 2
def baseEnd_3794177 : Nat := 432941442052023777497423

theorem tailTrace_3794177 : CollatzResearch.WordTrace tailWord_3794177 prefixEnd_3794177 432941442052023777497423 := by
  unfold tailWord_3794177
  simp only [CollatzResearch.WordTrace]
  refine ⟨138385003975352197687284785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92256669316901465124856523 138385003975352197687284785)
  ·
    refine ⟨103788752981514148265463589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138385003975352197687284785 103788752981514148265463589)
    ·
      refine ⟨19460391184033902799774423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103788752981514148265463589 19460391184033902799774423)
      ·
        refine ⟨29190586776050854199661635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19460391184033902799774423 29190586776050854199661635)
        ·
          refine ⟨43785880164076281299492453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29190586776050854199661635 43785880164076281299492453)
          ·
            refine ⟨8209852530764302743654835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43785880164076281299492453 8209852530764302743654835)
            ·
              refine ⟨12314778796146454115482253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209852530764302743654835 12314778796146454115482253)
              ·
                refine ⟨4618042048554920293305845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12314778796146454115482253 4618042048554920293305845)
                ·
                  refine ⟨432941442052023777497423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4618042048554920293305845 432941442052023777497423)
                  ·
                    rfl

theorem cell22_3794177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_3794177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794177 prefixEnd_3794177 := by exact prefixLift 3794177
  have htrace : WordTrace (prefixWord ++ tailWord_3794177) baseStart_3794177 baseEnd_3794177 := by
    simpa [prefixWord, tailWord_3794177, baseEnd_3794177] using wordTrace_append hprefix tailTrace_3794177
  have hstable : (prefixWord ++ tailWord_3794177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794177).length < 2 ^ (prefixWord ++ tailWord_3794177).sum := by decide
  have hdescent : baseEnd_3794177 < baseStart_3794177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794220 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_3794220 : Nat := 118140960795 + 3794220 * 2 ^ 59
def prefixEnd_3794220 : Nat := 4983230072969 + 3 ^ 40 * 3794220 * 2
def baseEnd_3794220 : Nat := 1298839045934833553667137

theorem tailTrace_3794220 : CollatzResearch.WordTrace tailWord_3794220 prefixEnd_3794220 1298839045934833553667137 := by
  unfold tailWord_3794220
  simp only [CollatzResearch.WordTrace]
  refine ⟨69193286157098208015550057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92257714876130944020733409 69193286157098208015550057)
  ·
    refine ⟨51894964617823656011662543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69193286157098208015550057 51894964617823656011662543)
    ·
      refine ⟨77842446926735484017493815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51894964617823656011662543 77842446926735484017493815)
      ·
        refine ⟨116763670390103226026240723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77842446926735484017493815 116763670390103226026240723)
        ·
          refine ⟨175145505585154839039361085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116763670390103226026240723 175145505585154839039361085)
          ·
            refine ⟨65679564594433064639760407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175145505585154839039361085 65679564594433064639760407)
            ·
              refine ⟨98519346891649596959640611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65679564594433064639760407 98519346891649596959640611)
              ·
                refine ⟨147779020337474395439460917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98519346891649596959640611 147779020337474395439460917)
                ·
                  refine ⟨13854283156638224572449461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147779020337474395439460917 13854283156638224572449461)
                  ·
                    refine ⟨1298839045934833553667137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13854283156638224572449461 1298839045934833553667137)
                    ·
                      rfl

theorem cell22_3794220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_3794220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794220 prefixEnd_3794220 := by exact prefixLift 3794220
  have htrace : WordTrace (prefixWord ++ tailWord_3794220) baseStart_3794220 baseEnd_3794220 := by
    simpa [prefixWord, tailWord_3794220, baseEnd_3794220] using wordTrace_append hprefix tailTrace_3794220
  have hstable : (prefixWord ++ tailWord_3794220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794220).length < 2 ^ (prefixWord ++ tailWord_3794220).sum := by decide
  have hdescent : baseEnd_3794220 < baseStart_3794220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794250 : List Nat := [3, 1, 2, 1, 1, 1, 1, 12]
def baseStart_3794250 : Nat := 118140960795 + 3794250 * 2 ^ 59
def prefixEnd_3794250 : Nat := 4983230072969 + 3 ^ 40 * 3794250 * 2
def baseEnd_3794250 : Nat := 144316590616435941713005

theorem tailTrace_3794250 : CollatzResearch.WordTrace tailWord_3794250 prefixEnd_3794250 144316590616435941713005 := by
  unfold tailWord_3794250
  simp only [CollatzResearch.WordTrace]
  refine ⟨34596916626021932788673051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92258444336058487436461469 34596916626021932788673051)
  ·
    refine ⟨51895374939032899183009577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34596916626021932788673051 51895374939032899183009577)
    ·
      refine ⟨38921531204274674387257183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51895374939032899183009577 38921531204274674387257183)
      ·
        refine ⟨58382296806412011580885775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38921531204274674387257183 58382296806412011580885775)
        ·
          refine ⟨87573445209618017371328663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58382296806412011580885775 87573445209618017371328663)
          ·
            refine ⟨131360167814427026056992995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87573445209618017371328663 131360167814427026056992995)
            ·
              refine ⟨197040251721640539085489493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131360167814427026056992995 197040251721640539085489493)
              ·
                refine ⟨144316590616435941713005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 197040251721640539085489493 144316590616435941713005)
                ·
                  rfl

theorem cell22_3794250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_3794250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794250 prefixEnd_3794250 := by exact prefixLift 3794250
  have htrace : WordTrace (prefixWord ++ tailWord_3794250) baseStart_3794250 baseEnd_3794250 := by
    simpa [prefixWord, tailWord_3794250, baseEnd_3794250] using wordTrace_append hprefix tailTrace_3794250
  have hstable : (prefixWord ++ tailWord_3794250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794250).length < 2 ^ (prefixWord ++ tailWord_3794250).sum := by decide
  have hdescent : baseEnd_3794250 < baseStart_3794250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794252 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_3794252 : Nat := 118140960795 + 3794252 * 2 ^ 59
def prefixEnd_3794252 : Nat := 4983230072969 + 3 ^ 40 * 3794252 * 2
def baseEnd_3794252 : Nat := 1298850000188796136867039

theorem tailTrace_3794252 : CollatzResearch.WordTrace tailWord_3794252 prefixEnd_3794252 1298850000188796136867039 := by
  unfold tailWord_3794252
  simp only [CollatzResearch.WordTrace]
  refine ⟨69193869725040242748132505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92258492966720323664176673 69193869725040242748132505)
  ·
    refine ⟨51895402293780182061099379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69193869725040242748132505 51895402293780182061099379)
    ·
      refine ⟨77843103440670273091649069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51895402293780182061099379 77843103440670273091649069)
      ·
        refine ⟨29191163790251352409368401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77843103440670273091649069 29191163790251352409368401)
        ·
          refine ⟨21893372842688514307026301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29191163790251352409368401 21893372842688514307026301)
          ·
            refine ⟨8210014816008192865134863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21893372842688514307026301 8210014816008192865134863)
            ·
              refine ⟨12315022224012289297702295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8210014816008192865134863 12315022224012289297702295)
              ·
                refine ⟨18472533336018433946553443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12315022224012289297702295 18472533336018433946553443)
                ·
                  refine ⟨27708800004027650919830165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18472533336018433946553443 27708800004027650919830165)
                  ·
                    refine ⟨1298850000188796136867039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27708800004027650919830165 1298850000188796136867039)
                    ·
                      rfl

theorem cell22_3794252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_3794252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794252 prefixEnd_3794252 := by exact prefixLift 3794252
  have htrace : WordTrace (prefixWord ++ tailWord_3794252) baseStart_3794252 baseEnd_3794252 := by
    simpa [prefixWord, tailWord_3794252, baseEnd_3794252] using wordTrace_append hprefix tailTrace_3794252
  have hstable : (prefixWord ++ tailWord_3794252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794252).length < 2 ^ (prefixWord ++ tailWord_3794252).sum := by decide
  have hdescent : baseEnd_3794252 < baseStart_3794252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794262 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_3794262 : Nat := 118140960795 + 3794262 * 2 ^ 59
def prefixEnd_3794262 : Nat := 4983230072969 + 3 ^ 40 * 3794262 * 2
def baseEnd_3794262 : Nat := 432951141131053148039003

theorem tailTrace_3794262 : CollatzResearch.WordTrace tailWord_3794262 prefixEnd_3794262 432951141131053148039003 := by
  unfold tailWord_3794262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8649256511252766075258065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92258736120029504802752693 8649256511252766075258065)
  ·
    refine ⟨6486942383439574556443549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8649256511252766075258065 6486942383439574556443549)
    ·
      refine ⟨2432603393789840458666331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6486942383439574556443549 2432603393789840458666331)
      ·
        refine ⟨3648905090684760687999497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432603393789840458666331 3648905090684760687999497)
        ·
          refine ⟨2736678818013570515999623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3648905090684760687999497 2736678818013570515999623)
          ·
            refine ⟨4105018227020355773999435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736678818013570515999623 4105018227020355773999435)
            ·
              refine ⟨6157527340530533660999153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105018227020355773999435 6157527340530533660999153)
              ·
                refine ⟨4618145505397900245749365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6157527340530533660999153 4618145505397900245749365)
                ·
                  refine ⟨432951141131053148039003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4618145505397900245749365 432951141131053148039003)
                  ·
                    rfl

theorem cell22_3794262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_3794262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794262 prefixEnd_3794262 := by exact prefixLift 3794262
  have htrace : WordTrace (prefixWord ++ tailWord_3794262) baseStart_3794262 baseEnd_3794262 := by
    simpa [prefixWord, tailWord_3794262, baseEnd_3794262] using wordTrace_append hprefix tailTrace_3794262
  have hstable : (prefixWord ++ tailWord_3794262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794262).length < 2 ^ (prefixWord ++ tailWord_3794262).sum := by decide
  have hdescent : baseEnd_3794262 < baseStart_3794262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794312 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 7]
def baseStart_3794312 : Nat := 118140960795 + 3794312 * 2 ^ 59
def prefixEnd_3794312 : Nat := 4983230072969 + 3 ^ 40 * 3794312 * 2
def baseEnd_3794312 : Nat := 432956846471658660122285

theorem tailTrace_3794312 : CollatzResearch.WordTrace tailWord_3794312 prefixEnd_3794312 432956846471658660122285 := by
  unfold tailWord_3794312
  simp only [CollatzResearch.WordTrace]
  refine ⟨69194963914931557871724595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92259951886575410495632793 69194963914931557871724595)
  ·
    refine ⟨103792445872397336807586893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69194963914931557871724595 103792445872397336807586893)
    ·
      refine ⟨38922167202149001302845085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103792445872397336807586893 38922167202149001302845085)
      ·
        refine ⟨14595812700805875488566907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38922167202149001302845085 14595812700805875488566907)
        ·
          refine ⟨21893719051208813232850361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14595812700805875488566907 21893719051208813232850361)
          ·
            refine ⟨16420289288406609924637771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21893719051208813232850361 16420289288406609924637771)
            ·
              refine ⟨24630433932609914886956657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16420289288406609924637771 24630433932609914886956657)
              ·
                refine ⟨18472825449457436165217493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24630433932609914886956657 18472825449457436165217493)
                ·
                  refine ⟨432956846471658660122285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18472825449457436165217493 432956846471658660122285)
                  ·
                    rfl

theorem cell22_3794312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_3794312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794312 prefixEnd_3794312 := by exact prefixLift 3794312
  have htrace : WordTrace (prefixWord ++ tailWord_3794312) baseStart_3794312 baseEnd_3794312 := by
    simpa [prefixWord, tailWord_3794312, baseEnd_3794312] using wordTrace_append hprefix tailTrace_3794312
  have hstable : (prefixWord ++ tailWord_3794312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794312).length < 2 ^ (prefixWord ++ tailWord_3794312).sum := by decide
  have hdescent : baseEnd_3794312 < baseStart_3794312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794376 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 1, 4]
def baseStart_3794376 : Nat := 118140960795 + 3794376 * 2 ^ 59
def prefixEnd_3794376 : Nat := 4983230072969 + 3 ^ 40 * 3794376 * 2
def baseEnd_3794376 : Nat := 1298892447922901146766659

theorem tailTrace_3794376 : CollatzResearch.WordTrace tailWord_3794376 prefixEnd_3794376 1298892447922901146766659 := by
  unfold tailWord_3794376
  simp only [CollatzResearch.WordTrace]
  refine ⟨69196131050815627336889491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92261508067754169782519321 69196131050815627336889491)
  ·
    refine ⟨103794196576223441005334237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69196131050815627336889491 103794196576223441005334237)
    ·
      refine ⟨38922823716083790377000339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103794196576223441005334237 38922823716083790377000339)
      ·
        refine ⟨58384235574125685565500509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38922823716083790377000339 58384235574125685565500509)
        ·
          refine ⟨21894088340297132087062691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58384235574125685565500509 21894088340297132087062691)
          ·
            refine ⟨32841132510445698130594037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21894088340297132087062691 32841132510445698130594037)
            ·
              refine ⟨3078856172854284199743191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32841132510445698130594037 3078856172854284199743191)
              ·
                refine ⟨4618284259281426299614787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3078856172854284199743191 4618284259281426299614787)
                ·
                  refine ⟨6927426388922139449422181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618284259281426299614787 6927426388922139449422181)
                  ·
                    refine ⟨1298892447922901146766659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6927426388922139449422181 1298892447922901146766659)
                    ·
                      rfl

theorem cell22_3794376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_3794376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794376 prefixEnd_3794376 := by exact prefixLift 3794376
  have htrace : WordTrace (prefixWord ++ tailWord_3794376) baseStart_3794376 baseEnd_3794376 := by
    simpa [prefixWord, tailWord_3794376, baseEnd_3794376] using wordTrace_append hprefix tailTrace_3794376
  have hstable : (prefixWord ++ tailWord_3794376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794376).length < 2 ^ (prefixWord ++ tailWord_3794376).sum := by decide
  have hdescent : baseEnd_3794376 < baseStart_3794376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794421 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3794421 : Nat := 118140960795 + 3794421 * 2 ^ 59
def prefixEnd_3794421 : Nat := 4983230072969 + 3 ^ 40 * 3794421 * 2
def baseEnd_3794421 : Nat := 1298907852342536029391521

theorem tailTrace_3794421 : CollatzResearch.WordTrace tailWord_3794421 prefixEnd_3794421 1298907852342536029391521 := by
  unfold tailWord_3794421
  simp only [CollatzResearch.WordTrace]
  refine ⟨138393903386468227359167117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92262602257645484906111411 138393903386468227359167117)
  ·
    refine ⟨51897713769925585259687669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138393903386468227359167117 51897713769925585259687669)
    ·
      refine ⟨4865410665930523618095719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51897713769925585259687669 4865410665930523618095719)
      ·
        refine ⟨7298115998895785427143579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865410665930523618095719 7298115998895785427143579)
        ·
          refine ⟨10947173998343678140715369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7298115998895785427143579 10947173998343678140715369)
          ·
            refine ⟨8210380498757758605536527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10947173998343678140715369 8210380498757758605536527)
            ·
              refine ⟨12315570748136637908304791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8210380498757758605536527 12315570748136637908304791)
              ·
                refine ⟨18473356122204956862457187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12315570748136637908304791 18473356122204956862457187)
                ·
                  refine ⟨27710034183307435293685781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18473356122204956862457187 27710034183307435293685781)
                  ·
                    refine ⟨1298907852342536029391521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27710034183307435293685781 1298907852342536029391521)
                    ·
                      rfl

theorem cell22_3794421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3794421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794421 prefixEnd_3794421 := by exact prefixLift 3794421
  have htrace : WordTrace (prefixWord ++ tailWord_3794421) baseStart_3794421 baseEnd_3794421 := by
    simpa [prefixWord, tailWord_3794421, baseEnd_3794421] using wordTrace_append hprefix tailTrace_3794421
  have hstable : (prefixWord ++ tailWord_3794421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794421).length < 2 ^ (prefixWord ++ tailWord_3794421).sum := by decide
  have hdescent : baseEnd_3794421 < baseStart_3794421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794451 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 3, 3]
def baseStart_3794451 : Nat := 118140960795 + 3794451 * 2 ^ 59
def prefixEnd_3794451 : Nat := 4983230072969 + 3 ^ 40 * 3794451 * 2
def baseEnd_3794451 : Nat := 1298918121955625951141429

theorem tailTrace_3794451 : CollatzResearch.WordTrace tailWord_3794451 prefixEnd_3794451 1298918121955625951141429 := by
  unfold tailWord_3794451
  simp only [CollatzResearch.WordTrace]
  refine ⟨138394997576359542482759207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92263331717573028321839471 138394997576359542482759207)
  ·
    refine ⟨207592496364539313724138811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138394997576359542482759207 207592496364539313724138811)
    ·
      refine ⟨311388744546808970586208217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207592496364539313724138811 311388744546808970586208217)
      ·
        refine ⟨233541558410106727939656163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311388744546808970586208217 233541558410106727939656163)
        ·
          refine ⟨350312337615160091909484245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233541558410106727939656163 350312337615160091909484245)
          ·
            refine ⟨8210445412855314654128537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 350312337615160091909484245 8210445412855314654128537)
            ·
              refine ⟨6157834059641485990596403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8210445412855314654128537 6157834059641485990596403)
              ·
                refine ⟨9236751089462228985894605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157834059641485990596403 9236751089462228985894605)
                ·
                  refine ⟨3463781658548335869710477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9236751089462228985894605 3463781658548335869710477)
                  ·
                    refine ⟨1298918121955625951141429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3463781658548335869710477 1298918121955625951141429)
                    ·
                      rfl

theorem cell22_3794451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 3].length) (baseStart_3794451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794451 prefixEnd_3794451 := by exact prefixLift 3794451
  have htrace : WordTrace (prefixWord ++ tailWord_3794451) baseStart_3794451 baseEnd_3794451 := by
    simpa [prefixWord, tailWord_3794451, baseEnd_3794451] using wordTrace_append hprefix tailTrace_3794451
  have hstable : (prefixWord ++ tailWord_3794451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794451).length < 2 ^ (prefixWord ++ tailWord_3794451).sum := by decide
  have hdescent : baseEnd_3794451 < baseStart_3794451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794485 : List Nat := [1, 3, 3, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3794485 : Nat := 118140960795 + 3794485 * 2 ^ 59
def prefixEnd_3794485 : Nat := 4983230072969 + 3 ^ 40 * 3794485 * 2
def baseEnd_3794485 : Nat := 1298929760850461195791325

theorem tailTrace_3794485 : CollatzResearch.WordTrace tailWord_3794485 prefixEnd_3794485 1298929760850461195791325 := by
  unfold tailWord_3794485
  simp only [CollatzResearch.WordTrace]
  refine ⟨138396237658236366289496909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92264158438824244192997939 138396237658236366289496909)
  ·
    refine ⟨51898589121838637358561341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138396237658236366289496909 51898589121838637358561341)
    ·
      refine ⟨19461970920689489009460503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51898589121838637358561341 19461970920689489009460503)
      ·
        refine ⟨29192956381034233514190755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19461970920689489009460503 29192956381034233514190755)
        ·
          refine ⟨43789434571551350271286133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29192956381034233514190755 43789434571551350271286133)
          ·
            refine ⟨4105259491082939087933075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43789434571551350271286133 4105259491082939087933075)
            ·
              refine ⟨6157889236624408631899613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105259491082939087933075 6157889236624408631899613)
              ·
                refine ⟨2309208463734153236962355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6157889236624408631899613 2309208463734153236962355)
                ·
                  refine ⟨3463812695601229855443533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309208463734153236962355 3463812695601229855443533)
                  ·
                    refine ⟨1298929760850461195791325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3463812695601229855443533 1298929760850461195791325)
                    ·
                      rfl

theorem cell22_3794485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3794485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794485 prefixEnd_3794485 := by exact prefixLift 3794485
  have htrace : WordTrace (prefixWord ++ tailWord_3794485) baseStart_3794485 baseEnd_3794485 := by
    simpa [prefixWord, tailWord_3794485, baseEnd_3794485] using wordTrace_append hprefix tailTrace_3794485
  have hstable : (prefixWord ++ tailWord_3794485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794485).length < 2 ^ (prefixWord ++ tailWord_3794485).sum := by decide
  have hdescent : baseEnd_3794485 < baseStart_3794485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794502 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_3794502 : Nat := 118140960795 + 3794502 * 2 ^ 59
def prefixEnd_3794502 : Nat := 4983230072969 + 3 ^ 40 * 3794502 * 2
def baseEnd_3794502 : Nat := 1298935580297878818116273

theorem tailTrace_3794502 : CollatzResearch.WordTrace tailWord_3794502 prefixEnd_3794502 1298935580297878818116273 := by
  unfold tailWord_3794502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324901803099211818527055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92264571799449852128577173 4324901803099211818527055)
  ·
    refine ⟨6487352704648817727790583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4324901803099211818527055 6487352704648817727790583)
    ·
      refine ⟨9731029056973226591685875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6487352704648817727790583 9731029056973226591685875)
      ·
        refine ⟨14596543585459839887528813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9731029056973226591685875 14596543585459839887528813)
        ·
          refine ⟨5473703844547439957823305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14596543585459839887528813 5473703844547439957823305)
          ·
            refine ⟨4105277883410579968367479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5473703844547439957823305 4105277883410579968367479)
            ·
              refine ⟨6157916825115869952551219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105277883410579968367479 6157916825115869952551219)
              ·
                refine ⟨9236875237673804928826829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157916825115869952551219 9236875237673804928826829)
                ·
                  refine ⟨3463828214127676848310061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9236875237673804928826829 3463828214127676848310061)
                  ·
                    refine ⟨1298935580297878818116273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3463828214127676848310061 1298935580297878818116273)
                    ·
                      rfl

theorem cell22_3794502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_3794502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794502 prefixEnd_3794502 := by exact prefixLift 3794502
  have htrace : WordTrace (prefixWord ++ tailWord_3794502) baseStart_3794502 baseEnd_3794502 := by
    simpa [prefixWord, tailWord_3794502, baseEnd_3794502] using wordTrace_append hprefix tailTrace_3794502
  have hstable : (prefixWord ++ tailWord_3794502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794502).length < 2 ^ (prefixWord ++ tailWord_3794502).sum := by decide
  have hdescent : baseEnd_3794502 < baseStart_3794502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794588 : List Nat := [2, 2, 3, 2, 3, 1, 3, 6]
def baseStart_3794588 : Nat := 118140960795 + 3794588 * 2 ^ 59
def prefixEnd_3794588 : Nat := 4983230072969 + 3 ^ 40 * 3794588 * 2
def baseEnd_3794588 : Nat := 144329446650600362274001

theorem tailTrace_3794588 : CollatzResearch.WordTrace tailWord_3794588 prefixEnd_3794588 144329446650600362274001 := by
  unfold tailWord_3794588
  simp only [CollatzResearch.WordTrace]
  refine ⟨69199997188431607440248209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92266662917908809920330945 69199997188431607440248209)
  ·
    refine ⟨51899997891323705580186157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69199997188431607440248209 51899997891323705580186157)
    ·
      refine ⟨19462499209246389592569809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51899997891323705580186157 19462499209246389592569809)
      ·
        refine ⟨14596874406934792194427357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19462499209246389592569809 14596874406934792194427357)
        ·
          refine ⟨5473827902600547072910259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14596874406934792194427357 5473827902600547072910259)
          ·
            refine ⟨8210741853900820609365389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473827902600547072910259 8210741853900820609365389)
            ·
              refine ⟨3079028195212807728512021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8210741853900820609365389 3079028195212807728512021)
              ·
                refine ⟨144329446650600362274001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3079028195212807728512021 144329446650600362274001)
                ·
                  rfl

theorem cell22_3794588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 6].length) (baseStart_3794588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794588 prefixEnd_3794588 := by exact prefixLift 3794588
  have htrace : WordTrace (prefixWord ++ tailWord_3794588) baseStart_3794588 baseEnd_3794588 := by
    simpa [prefixWord, tailWord_3794588, baseEnd_3794588] using wordTrace_append hprefix tailTrace_3794588
  have hstable : (prefixWord ++ tailWord_3794588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794588).length < 2 ^ (prefixWord ++ tailWord_3794588).sum := by decide
  have hdescent : baseEnd_3794588 < baseStart_3794588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794590 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3794590 : Nat := 118140960795 + 3794590 * 2 ^ 59
def prefixEnd_3794590 : Nat := 4983230072969 + 3 ^ 40 * 3794590 * 2
def baseEnd_3794590 : Nat := 1298965704496275921916003

theorem tailTrace_3794590 : CollatzResearch.WordTrace tailWord_3794590 prefixEnd_3794590 1298965704496275921916003 := by
  unfold tailWord_3794590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17300008415356996152758653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92266711548570646148046149 17300008415356996152758653)
  ·
    refine ⟨6487503155758873557284495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17300008415356996152758653 6487503155758873557284495)
    ·
      refine ⟨9731254733638310335926743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6487503155758873557284495 9731254733638310335926743)
      ·
        refine ⟨14596882100457465503890115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9731254733638310335926743 14596882100457465503890115)
        ·
          refine ⟨21895323150686198255835173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14596882100457465503890115 21895323150686198255835173)
          ·
            refine ⟨4105373090753662172969095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21895323150686198255835173 4105373090753662172969095)
            ·
              refine ⟨6158059636130493259453643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105373090753662172969095 6158059636130493259453643)
              ·
                refine ⟨9237089454195739889180465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6158059636130493259453643 9237089454195739889180465)
                ·
                  refine ⟨6927817090646804916885349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9237089454195739889180465 6927817090646804916885349)
                  ·
                    refine ⟨1298965704496275921916003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6927817090646804916885349 1298965704496275921916003)
                    ·
                      rfl

theorem cell22_3794590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3794590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794590 prefixEnd_3794590 := by exact prefixLift 3794590
  have htrace : WordTrace (prefixWord ++ tailWord_3794590) baseStart_3794590 baseEnd_3794590 := by
    simpa [prefixWord, tailWord_3794590, baseEnd_3794590] using wordTrace_append hprefix tailTrace_3794590
  have hstable : (prefixWord ++ tailWord_3794590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794590).length < 2 ^ (prefixWord ++ tailWord_3794590).sum := by decide
  have hdescent : baseEnd_3794590 < baseStart_3794590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794620 : List Nat := [2, 2, 2, 3, 1, 2, 2, 4, 1, 3]
def baseStart_3794620 : Nat := 118140960795 + 3794620 * 2 ^ 59
def prefixEnd_3794620 : Nat := 4983230072969 + 3 ^ 40 * 3794620 * 2
def baseEnd_3794620 : Nat := 1298975974109365843665911

theorem tailTrace_3794620 : CollatzResearch.WordTrace tailWord_3794620 prefixEnd_3794620 1298975974109365843665911 := by
  unfold tailWord_3794620
  simp only [CollatzResearch.WordTrace]
  refine ⟨69200580756373642172830657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92267441008498189563774209 69200580756373642172830657)
  ·
    refine ⟨51900435567280231629622993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69200580756373642172830657 51900435567280231629622993)
    ·
      refine ⟨38925326675460173722217245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51900435567280231629622993 38925326675460173722217245)
      ·
        refine ⟨14596997503297565145831467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38925326675460173722217245 14596997503297565145831467)
        ·
          refine ⟨21895496254946347718747201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14596997503297565145831467 21895496254946347718747201)
          ·
            refine ⟨16421622191209760789060401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21895496254946347718747201 16421622191209760789060401)
            ·
              refine ⟨12316216643407320591795301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16421622191209760789060401 12316216643407320591795301)
              ·
                refine ⟨2309290620638872610961619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12316216643407320591795301 2309290620638872610961619)
                ·
                  refine ⟨3463935930958308916442429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309290620638872610961619 3463935930958308916442429)
                  ·
                    refine ⟨1298975974109365843665911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3463935930958308916442429 1298975974109365843665911)
                    ·
                      rfl

theorem cell22_3794620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_3794620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794620 prefixEnd_3794620 := by exact prefixLift 3794620
  have htrace : WordTrace (prefixWord ++ tailWord_3794620) baseStart_3794620 baseEnd_3794620 := by
    simpa [prefixWord, tailWord_3794620, baseEnd_3794620] using wordTrace_append hprefix tailTrace_3794620
  have hstable : (prefixWord ++ tailWord_3794620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794620).length < 2 ^ (prefixWord ++ tailWord_3794620).sum := by decide
  have hdescent : baseEnd_3794620 < baseStart_3794620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794626 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3794626 : Nat := 118140960795 + 3794626 * 2 ^ 59
def prefixEnd_3794626 : Nat := 4983230072969 + 3 ^ 40 * 3794626 * 2
def baseEnd_3794626 : Nat := 1298978028031983828015893

theorem tailTrace_3794626 : CollatzResearch.WordTrace tailWord_3794626 prefixEnd_3794626 1298978028031983828015893 := by
  unfold tailWord_3794626
  simp only [CollatzResearch.WordTrace]
  refine ⟨34600345087681386842594933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92267586900483698246919821 34600345087681386842594933)
  ·
    refine ⟨3243782351970130016493275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34600345087681386842594933 3243782351970130016493275)
    ·
      refine ⟨4865673527955195024739913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3243782351970130016493275 4865673527955195024739913)
      ·
        refine ⟨3649255145966396268554935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4865673527955195024739913 3649255145966396268554935)
        ·
          refine ⟨5473882718949594402832403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649255145966396268554935 5473882718949594402832403)
          ·
            refine ⟨8210824078424391604248605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473882718949594402832403 8210824078424391604248605)
            ·
              refine ⟨3079059029409146851593227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8210824078424391604248605 3079059029409146851593227)
              ·
                refine ⟨4618588544113720277389841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079059029409146851593227 4618588544113720277389841)
                ·
                  refine ⟨3463941408085290208042381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4618588544113720277389841 3463941408085290208042381)
                  ·
                    refine ⟨1298978028031983828015893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3463941408085290208042381 1298978028031983828015893)
                    ·
                      rfl

theorem cell22_3794626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3794626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794626 prefixEnd_3794626 := by exact prefixLift 3794626
  have htrace : WordTrace (prefixWord ++ tailWord_3794626) baseStart_3794626 baseEnd_3794626 := by
    simpa [prefixWord, tailWord_3794626, baseEnd_3794626] using wordTrace_append hprefix tailTrace_3794626
  have hstable : (prefixWord ++ tailWord_3794626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794626).length < 2 ^ (prefixWord ++ tailWord_3794626).sum := by decide
  have hdescent : baseEnd_3794626 < baseStart_3794626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794678 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_3794678 : Nat := 118140960795 + 3794678 * 2 ^ 59
def prefixEnd_3794678 : Nat := 4983230072969 + 3 ^ 40 * 3794678 * 2
def baseEnd_3794678 : Nat := 432998609564891008571911

theorem tailTrace_3794678 : CollatzResearch.WordTrace tailWord_3794678 prefixEnd_3794678 432998609564891008571911 := by
  unfold tailWord_3794678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650204809158572515704543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92268851297691440167515125 8650204809158572515704543)
  ·
    refine ⟨12975307213737858773556815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8650204809158572515704543 12975307213737858773556815)
    ·
      refine ⟨19462960820606788160335223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12975307213737858773556815 19462960820606788160335223)
      ·
        refine ⟨29194441230910182240502835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19462960820606788160335223 29194441230910182240502835)
        ·
          refine ⟨43791661846365273360754253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29194441230910182240502835 43791661846365273360754253)
          ·
            refine ⟨16421873192386977510282845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43791661846365273360754253 16421873192386977510282845)
            ·
              refine ⟨6158202447145116566356067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16421873192386977510282845 6158202447145116566356067)
              ·
                refine ⟨9237303670717674849534101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6158202447145116566356067 9237303670717674849534101)
                ·
                  refine ⟨432998609564891008571911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9237303670717674849534101 432998609564891008571911)
                  ·
                    rfl

theorem cell22_3794678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_3794678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794678 prefixEnd_3794678 := by exact prefixLift 3794678
  have htrace : WordTrace (prefixWord ++ tailWord_3794678) baseStart_3794678 baseEnd_3794678 := by
    simpa [prefixWord, tailWord_3794678, baseEnd_3794678] using wordTrace_append hprefix tailTrace_3794678
  have hstable : (prefixWord ++ tailWord_3794678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794678).length < 2 ^ (prefixWord ++ tailWord_3794678).sum := by decide
  have hdescent : baseEnd_3794678 < baseStart_3794678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794740 : List Nat := [2, 5, 1, 1, 2, 3, 1, 7]
def baseStart_3794740 : Nat := 118140960795 + 3794740 * 2 ^ 59
def prefixEnd_3794740 : Nat := 4983230072969 + 3 ^ 40 * 3794740 * 2
def baseEnd_3794740 : Nat := 144335228062413947851727

theorem tailTrace_3794740 : CollatzResearch.WordTrace tailWord_3794740 prefixEnd_3794740 144335228062413947851727 := by
  unfold tailWord_3794740
  simp only [CollatzResearch.WordTrace]
  refine ⟨69202769136156272420014837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92270358848208363226686449 69202769136156272420014837)
  ·
    refine ⟨6487759606514650539376391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69202769136156272420014837 6487759606514650539376391)
    ·
      refine ⟨9731639409771975809064587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6487759606514650539376391 9731639409771975809064587)
      ·
        refine ⟨14597459114657963713596881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9731639409771975809064587 14597459114657963713596881)
        ·
          refine ⟨10948094335993472785197661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14597459114657963713596881 10948094335993472785197661)
          ·
            refine ⟨4105535375997552294449123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10948094335993472785197661 4105535375997552294449123)
            ·
              refine ⟨6158303063996328441673685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105535375997552294449123 6158303063996328441673685)
              ·
                refine ⟨144335228062413947851727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6158303063996328441673685 144335228062413947851727)
                ·
                  rfl

theorem cell22_3794740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 7].length) (baseStart_3794740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794740 prefixEnd_3794740 := by exact prefixLift 3794740
  have htrace : WordTrace (prefixWord ++ tailWord_3794740) baseStart_3794740 baseEnd_3794740 := by
    simpa [prefixWord, tailWord_3794740, baseEnd_3794740] using wordTrace_append hprefix tailTrace_3794740
  have hstable : (prefixWord ++ tailWord_3794740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794740).length < 2 ^ (prefixWord ++ tailWord_3794740).sum := by decide
  have hdescent : baseEnd_3794740 < baseStart_3794740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794772 : List Nat := [2, 4, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_3794772 : Nat := 118140960795 + 3794772 * 2 ^ 59
def prefixEnd_3794772 : Nat := 4983230072969 + 3 ^ 40 * 3794772 * 2
def baseEnd_3794772 : Nat := 1299028006815688113865445

theorem tailTrace_3794772 : CollatzResearch.WordTrace tailWord_3794772 prefixEnd_3794772 1299028006815688113865445 := by
  unfold tailWord_3794772
  simp only [CollatzResearch.WordTrace]
  refine ⟨69203352704098307152597285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92271136938797742870129713 69203352704098307152597285)
  ·
    refine ⟨12975628632018432591111991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69203352704098307152597285 12975628632018432591111991)
    ·
      refine ⟨19463442948027648886667987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12975628632018432591111991 19463442948027648886667987)
      ·
        refine ⟨29195164422041473330001981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19463442948027648886667987 29195164422041473330001981)
        ·
          refine ⟨10948186658265552498750743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29195164422041473330001981 10948186658265552498750743)
          ·
            refine ⟨16422279987398328748126115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10948186658265552498750743 16422279987398328748126115)
            ·
              refine ⟨24633419981097493122189173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16422279987398328748126115 24633419981097493122189173)
              ·
                refine ⟨2309383123227889980205235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24633419981097493122189173 2309383123227889980205235)
                ·
                  refine ⟨3464074684841834970307853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309383123227889980205235 3464074684841834970307853)
                  ·
                    refine ⟨1299028006815688113865445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464074684841834970307853 1299028006815688113865445)
                    ·
                      rfl

theorem cell22_3794772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_3794772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794772 prefixEnd_3794772 := by exact prefixLift 3794772
  have htrace : WordTrace (prefixWord ++ tailWord_3794772) baseStart_3794772 baseEnd_3794772 := by
    simpa [prefixWord, tailWord_3794772, baseEnd_3794772] using wordTrace_append hprefix tailTrace_3794772
  have hstable : (prefixWord ++ tailWord_3794772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794772).length < 2 ^ (prefixWord ++ tailWord_3794772).sum := by decide
  have hdescent : baseEnd_3794772 < baseStart_3794772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794841 : List Nat := [1, 2, 1, 2, 1, 3, 12]
def baseStart_3794841 : Nat := 118140960795 + 3794841 * 2 ^ 59
def prefixEnd_3794841 : Nat := 4983230072969 + 3 ^ 40 * 3794841 * 2
def baseEnd_3794841 : Nat := 48113023219473886440379

theorem tailTrace_3794841 : CollatzResearch.WordTrace tailWord_3794841 prefixEnd_3794841 48113023219473886440379 := by
  unfold tailWord_3794841
  simp only [CollatzResearch.WordTrace]
  refine ⟨138409222044946639089456377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92272814696631092726304251 138409222044946639089456377)
  ·
    refine ⟨103806916533709979317092283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138409222044946639089456377 103806916533709979317092283)
    ·
      refine ⟨155710374800564968975638425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103806916533709979317092283 155710374800564968975638425)
      ·
        refine ⟨116782781100423726731728819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155710374800564968975638425 116782781100423726731728819)
        ·
          refine ⟨175174171650635590097593229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116782781100423726731728819 175174171650635590097593229)
          ·
            refine ⟨65690314368988346286597461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175174171650635590097593229 65690314368988346286597461)
            ·
              refine ⟨48113023219473886440379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 65690314368988346286597461 48113023219473886440379)
              ·
                rfl

theorem cell22_3794841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 12].length) (baseStart_3794841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794841 prefixEnd_3794841 := by exact prefixLift 3794841
  have htrace : WordTrace (prefixWord ++ tailWord_3794841) baseStart_3794841 baseEnd_3794841 := by
    simpa [prefixWord, tailWord_3794841, baseEnd_3794841] using wordTrace_append hprefix tailTrace_3794841
  have hstable : (prefixWord ++ tailWord_3794841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794841).length < 2 ^ (prefixWord ++ tailWord_3794841).sum := by decide
  have hdescent : baseEnd_3794841 < baseStart_3794841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794845 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 4, 3]
def baseStart_3794845 : Nat := 118140960795 + 3794845 * 2 ^ 59
def prefixEnd_3794845 : Nat := 4983230072969 + 3 ^ 40 * 3794845 * 2
def baseEnd_3794845 : Nat := 1299052996207540256790221

theorem tailTrace_3794845 : CollatzResearch.WordTrace tailWord_3794845 prefixEnd_3794845 1299052996207540256790221 := by
  unfold tailWord_3794845
  simp only [CollatzResearch.WordTrace]
  refine ⟨138409367936932147772601989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92272911957954765181734659 138409367936932147772601989)
  ·
    refine ⟨25951756488174777707362873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138409367936932147772601989 25951756488174777707362873)
    ·
      refine ⟨19463817366131083280522155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25951756488174777707362873 19463817366131083280522155)
      ·
        refine ⟨29195726049196624920783233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19463817366131083280522155 29195726049196624920783233)
        ·
          refine ⟨21896794536897468690587425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29195726049196624920783233 21896794536897468690587425)
          ·
            refine ⟨16422595902673101517940569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21896794536897468690587425 16422595902673101517940569)
            ·
              refine ⟨12316946927004826138455427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16422595902673101517940569 12316946927004826138455427)
              ·
                refine ⟨18475420390507239207683141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12316946927004826138455427 18475420390507239207683141)
                ·
                  refine ⟨3464141323220107351440589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18475420390507239207683141 3464141323220107351440589)
                  ·
                    refine ⟨1299052996207540256790221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464141323220107351440589 1299052996207540256790221)
                    ·
                      rfl

theorem cell22_3794845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_3794845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794845 prefixEnd_3794845 := by exact prefixLift 3794845
  have htrace : WordTrace (prefixWord ++ tailWord_3794845) baseStart_3794845 baseEnd_3794845 := by
    simpa [prefixWord, tailWord_3794845, baseEnd_3794845] using wordTrace_append hprefix tailTrace_3794845
  have hstable : (prefixWord ++ tailWord_3794845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794845).length < 2 ^ (prefixWord ++ tailWord_3794845).sum := by decide
  have hdescent : baseEnd_3794845 < baseStart_3794845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794847 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 6]
def baseStart_3794847 : Nat := 118140960795 + 3794847 * 2 ^ 59
def prefixEnd_3794847 : Nat := 4983230072969 + 3 ^ 40 * 3794847 * 2
def baseEnd_3794847 : Nat := 433017893616137639413405

theorem tailTrace_3794847 : CollatzResearch.WordTrace tailWord_3794847 prefixEnd_3794847 433017893616137639413405 := by
  unfold tailWord_3794847
  simp only [CollatzResearch.WordTrace]
  refine ⟨138409440882924902114174795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92272960588616601409449863 138409440882924902114174795)
  ·
    refine ⟨207614161324387353171262193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138409440882924902114174795 207614161324387353171262193)
    ·
      refine ⟨155710620993290514878446645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207614161324387353171262193 155710620993290514878446645)
      ·
        refine ⟨14597870718120985769854373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155710620993290514878446645 14597870718120985769854373)
        ·
          refine ⟨2737100759647684831847695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14597870718120985769854373 2737100759647684831847695)
          ·
            refine ⟨4105651139471527247771543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737100759647684831847695 4105651139471527247771543)
            ·
              refine ⟨6158476709207290871657315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105651139471527247771543 6158476709207290871657315)
              ·
                refine ⟨9237715063810936307485973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6158476709207290871657315 9237715063810936307485973)
                ·
                  refine ⟨433017893616137639413405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9237715063810936307485973 433017893616137639413405)
                  ·
                    rfl

theorem cell22_3794847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 6].length) (baseStart_3794847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794847 prefixEnd_3794847 := by exact prefixLift 3794847
  have htrace : WordTrace (prefixWord ++ tailWord_3794847) baseStart_3794847 baseEnd_3794847 := by
    simpa [prefixWord, tailWord_3794847, baseEnd_3794847] using wordTrace_append hprefix tailTrace_3794847
  have hstable : (prefixWord ++ tailWord_3794847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794847).length < 2 ^ (prefixWord ++ tailWord_3794847).sum := by decide
  have hdescent : baseEnd_3794847 < baseStart_3794847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794954 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 5]
def baseStart_3794954 : Nat := 118140960795 + 3794954 * 2 ^ 59
def prefixEnd_3794954 : Nat := 4983230072969 + 3 ^ 40 * 3794954 * 2
def baseEnd_3794954 : Nat := 433030103045033435271629

theorem tailTrace_3794954 : CollatzResearch.WordTrace tailWord_3794954 prefixEnd_3794954 433030103045033435271629 := by
  unfold tailWord_3794954
  simp only [CollatzResearch.WordTrace]
  refine ⟨34603335873384314847079979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92275562329024839592213277 34603335873384314847079979)
  ·
    refine ⟨51905003810076472270619969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34603335873384314847079979 51905003810076472270619969)
    ·
      refine ⟨38928752857557354202964977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51905003810076472270619969 38928752857557354202964977)
      ·
        refine ⟨29196564643168015652223733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38928752857557354202964977 29196564643168015652223733)
        ·
          refine ⟨2737177935297001467395975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29196564643168015652223733 2737177935297001467395975)
          ·
            refine ⟨4105766902945502201093963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737177935297001467395975 4105766902945502201093963)
            ·
              refine ⟨6158650354418253301640945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105766902945502201093963 6158650354418253301640945)
              ·
                refine ⟨4618987765813689976230709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6158650354418253301640945 4618987765813689976230709)
                ·
                  refine ⟨433030103045033435271629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4618987765813689976230709 433030103045033435271629)
                  ·
                    rfl

theorem cell22_3794954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_3794954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794954 prefixEnd_3794954 := by exact prefixLift 3794954
  have htrace : WordTrace (prefixWord ++ tailWord_3794954) baseStart_3794954 baseEnd_3794954 := by
    simpa [prefixWord, tailWord_3794954, baseEnd_3794954] using wordTrace_append hprefix tailTrace_3794954
  have hstable : (prefixWord ++ tailWord_3794954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794954).length < 2 ^ (prefixWord ++ tailWord_3794954).sum := by decide
  have hdescent : baseEnd_3794954 < baseStart_3794954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3794963 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 3, 5]
def baseStart_3794963 : Nat := 118140960795 + 3794963 * 2 ^ 59
def prefixEnd_3794963 : Nat := 4983230072969 + 3 ^ 40 * 3794963 * 2
def baseEnd_3794963 : Nat := 1299093390019027282339859

theorem tailTrace_3794963 : CollatzResearch.WordTrace tailWord_3794963 prefixEnd_3794963 1299093390019027282339859 := by
  unfold tailWord_3794963
  simp only [CollatzResearch.WordTrace]
  refine ⟨138413671750504653925397543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92275781167003102616931695 138413671750504653925397543)
  ·
    refine ⟨207620507625756980888096315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138413671750504653925397543 207620507625756980888096315)
    ·
      refine ⟨311430761438635471332144473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207620507625756980888096315 311430761438635471332144473)
      ·
        refine ⟨233573071078976603499108355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311430761438635471332144473 233573071078976603499108355)
        ·
          refine ⟨350359606618464905248662533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233573071078976603499108355 350359606618464905248662533)
          ·
            refine ⟨65692426240962169734124225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350359606618464905248662533 65692426240962169734124225)
            ·
              refine ⟨49269319680721627300593169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65692426240962169734124225 49269319680721627300593169)
              ·
                refine ⟨36951989760541220475444877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49269319680721627300593169 36951989760541220475444877)
                ·
                  refine ⟨13856996160202957678291829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36951989760541220475444877 13856996160202957678291829)
                  ·
                    refine ⟨1299093390019027282339859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13856996160202957678291829 1299093390019027282339859)
                    ·
                      rfl

theorem cell22_3794963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_3794963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3794963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3794963 prefixEnd_3794963 := by exact prefixLift 3794963
  have htrace : WordTrace (prefixWord ++ tailWord_3794963) baseStart_3794963 baseEnd_3794963 := by
    simpa [prefixWord, tailWord_3794963, baseEnd_3794963] using wordTrace_append hprefix tailTrace_3794963
  have hstable : (prefixWord ++ tailWord_3794963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3794963).length < 2 ^ (prefixWord ++ tailWord_3794963).sum := by decide
  have hdescent : baseEnd_3794963 < baseStart_3794963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3794963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795014 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_3795014 : Nat := 118140960795 + 3795014 * 2 ^ 59
def prefixEnd_3795014 : Nat := 4983230072969 + 3 ^ 40 * 3795014 * 2
def baseEnd_3795014 : Nat := 1299110848361280149314703

theorem tailTrace_3795014 : CollatzResearch.WordTrace tailWord_3795014 prefixEnd_3795014 1299110848361280149314703 := by
  unfold tailWord_3795014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325485371041246551109503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92277021248879926423669397 4325485371041246551109503)
  ·
    refine ⟨6488228056561869826664255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4325485371041246551109503 6488228056561869826664255)
    ·
      refine ⟨9732342084842804739996383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6488228056561869826664255 9732342084842804739996383)
      ·
        refine ⟨14598513127264207109994575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9732342084842804739996383 14598513127264207109994575)
        ·
          refine ⟨21897769690896310664991863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14598513127264207109994575 21897769690896310664991863)
          ·
            refine ⟨32846654536344465997487795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21897769690896310664991863 32846654536344465997487795)
            ·
              refine ⟨49269981804516698996231693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32846654536344465997487795 49269981804516698996231693)
              ·
                refine ⟨18476243176693762123586885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49269981804516698996231693 18476243176693762123586885)
                ·
                  refine ⟨3464295595630080398172541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18476243176693762123586885 3464295595630080398172541)
                  ·
                    refine ⟨1299110848361280149314703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464295595630080398172541 1299110848361280149314703)
                    ·
                      rfl

theorem cell22_3795014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_3795014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795014 prefixEnd_3795014 := by exact prefixLift 3795014
  have htrace : WordTrace (prefixWord ++ tailWord_3795014) baseStart_3795014 baseEnd_3795014 := by
    simpa [prefixWord, tailWord_3795014, baseEnd_3795014] using wordTrace_append hprefix tailTrace_3795014
  have hstable : (prefixWord ++ tailWord_3795014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795014).length < 2 ^ (prefixWord ++ tailWord_3795014).sum := by decide
  have hdescent : baseEnd_3795014 < baseStart_3795014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795023 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 1, 8]
def baseStart_3795023 : Nat := 118140960795 + 3795023 * 2 ^ 59
def prefixEnd_3795023 : Nat := 4983230072969 + 3 ^ 40 * 3795023 * 2
def baseEnd_3795023 : Nat := 1299113929245207125839675

theorem tailTrace_3795023 : CollatzResearch.WordTrace tailWord_3795023 prefixEnd_3795023 1299113929245207125839675 := by
  unfold tailWord_3795023
  simp only [CollatzResearch.WordTrace]
  refine ⟨138415860130287284172581723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92277240086858189448387815 138415860130287284172581723)
  ·
    refine ⟨207623790195430926258872585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138415860130287284172581723 207623790195430926258872585)
    ·
      refine ⟨155717842646573194694154439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207623790195430926258872585 155717842646573194694154439)
      ·
        refine ⟨233576763969859792041231659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155717842646573194694154439 233576763969859792041231659)
        ·
          refine ⟨350365145954789688061847489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233576763969859792041231659 350365145954789688061847489)
          ·
            refine ⟨262773859466092266046385617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350365145954789688061847489 262773859466092266046385617)
            ·
              refine ⟨197080394599569199534789213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262773859466092266046385617 197080394599569199534789213)
              ·
                refine ⟨73905147974838449825545955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197080394599569199534789213 73905147974838449825545955)
                ·
                  refine ⟨110857721962257674738318933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73905147974838449825545955 110857721962257674738318933)
                  ·
                    refine ⟨1299113929245207125839675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110857721962257674738318933 1299113929245207125839675)
                    ·
                      rfl

theorem cell22_3795023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_3795023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795023 prefixEnd_3795023 := by exact prefixLift 3795023
  have htrace : WordTrace (prefixWord ++ tailWord_3795023) baseStart_3795023 baseEnd_3795023 := by
    simpa [prefixWord, tailWord_3795023, baseEnd_3795023] using wordTrace_append hprefix tailTrace_3795023
  have hstable : (prefixWord ++ tailWord_3795023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795023).length < 2 ^ (prefixWord ++ tailWord_3795023).sum := by decide
  have hdescent : baseEnd_3795023 < baseStart_3795023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795134 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_3795134 : Nat := 118140960795 + 3795134 * 2 ^ 59
def prefixEnd_3795134 : Nat := 4983230072969 + 3 ^ 40 * 3795134 * 2
def baseEnd_3795134 : Nat := 433050642271213278771445

theorem tailTrace_3795134 : CollatzResearch.WordTrace tailWord_3795134 prefixEnd_3795134 433050642271213278771445 := by
  unfold tailWord_3795134
  simp only [CollatzResearch.WordTrace]
  refine ⟨17302488579110643766234057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92279939088590100086581637 17302488579110643766234057)
  ·
    refine ⟨12976866434332982824675543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17302488579110643766234057 12976866434332982824675543)
    ·
      refine ⟨19465299651499474237013315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12976866434332982824675543 19465299651499474237013315)
      ·
        refine ⟨29197949477249211355519973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19465299651499474237013315 29197949477249211355519973)
        ·
          refine ⟨5474615526984227129159995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29197949477249211355519973 5474615526984227129159995)
          ·
            refine ⟨8211923290476340693739993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474615526984227129159995 8211923290476340693739993)
            ·
              refine ⟨6158942467857255520304995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8211923290476340693739993 6158942467857255520304995)
              ·
                refine ⟨9238413701785883280457493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6158942467857255520304995 9238413701785883280457493)
                ·
                  refine ⟨433050642271213278771445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9238413701785883280457493 433050642271213278771445)
                  ·
                    rfl

theorem cell22_3795134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_3795134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795134 prefixEnd_3795134 := by exact prefixLift 3795134
  have htrace : WordTrace (prefixWord ++ tailWord_3795134) baseStart_3795134 baseEnd_3795134 := by
    simpa [prefixWord, tailWord_3795134, baseEnd_3795134] using wordTrace_append hprefix tailTrace_3795134
  have hstable : (prefixWord ++ tailWord_3795134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795134).length < 2 ^ (prefixWord ++ tailWord_3795134).sum := by decide
  have hdescent : baseEnd_3795134 < baseStart_3795134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795162 : List Nat := [3, 1, 1, 2, 2, 1, 6, 6]
def baseStart_3795162 : Nat := 118140960795 + 3795162 * 2 ^ 59
def prefixEnd_3795162 : Nat := 4983230072969 + 3 ^ 40 * 3795162 * 2
def baseEnd_3795162 : Nat := 144351279087317455179361

theorem tailTrace_3795162 : CollatzResearch.WordTrace tailWord_3795162 prefixEnd_3795162 144351279087317455179361 := by
  unfold tailWord_3795162
  simp only [CollatzResearch.WordTrace]
  refine ⟨34605232469195927727972935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92280619917855807274594493 34605232469195927727972935)
  ·
    refine ⟨51907848703793891591959403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34605232469195927727972935 51907848703793891591959403)
    ·
      refine ⟨77861773055690837387939105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51907848703793891591959403 77861773055690837387939105)
      ·
        refine ⟨58396329791768128040954329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77861773055690837387939105 58396329791768128040954329)
        ·
          refine ⟨43797247343826096030715747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58396329791768128040954329 43797247343826096030715747)
          ·
            refine ⟨65695871015739144046073621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43797247343826096030715747 65695871015739144046073621)
            ·
              refine ⟨3079493953862772377159701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65695871015739144046073621 3079493953862772377159701)
              ·
                refine ⟨144351279087317455179361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3079493953862772377159701 144351279087317455179361)
                ·
                  rfl

theorem cell22_3795162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_3795162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795162 prefixEnd_3795162 := by exact prefixLift 3795162
  have htrace : WordTrace (prefixWord ++ tailWord_3795162) baseStart_3795162 baseEnd_3795162 := by
    simpa [prefixWord, tailWord_3795162, baseEnd_3795162] using wordTrace_append hprefix tailTrace_3795162
  have hstable : (prefixWord ++ tailWord_3795162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795162).length < 2 ^ (prefixWord ++ tailWord_3795162).sum := by decide
  have hdescent : baseEnd_3795162 < baseStart_3795162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795194 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 3, 3]
def baseStart_3795194 : Nat := 118140960795 + 3795194 * 2 ^ 59
def prefixEnd_3795194 : Nat := 4983230072969 + 3 ^ 40 * 3795194 * 2
def baseEnd_3795194 : Nat := 1299172466039819679814151

theorem tailTrace_3795194 : CollatzResearch.WordTrace tailWord_3795194 prefixEnd_3795194 1299172466039819679814151 := by
  unfold tailWord_3795194
  simp only [CollatzResearch.WordTrace]
  refine ⟨34605524253166945094264159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92281398008445186918037757 34605524253166945094264159)
  ·
    refine ⟨51908286379750417641396239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34605524253166945094264159 51908286379750417641396239)
    ·
      refine ⟨77862429569625626462094359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51908286379750417641396239 77862429569625626462094359)
      ·
        refine ⟨116793644354438439693141539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77862429569625626462094359 116793644354438439693141539)
        ·
          refine ⟨175190466531657659539712309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116793644354438439693141539 175190466531657659539712309)
          ·
            refine ⟨16424106237342905581848029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175190466531657659539712309 16424106237342905581848029)
            ·
              refine ⟨6159039839003589593193011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16424106237342905581848029 6159039839003589593193011)
              ·
                refine ⟨9238559758505384389789517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6159039839003589593193011 9238559758505384389789517)
                ·
                  refine ⟨3464459909439519146171069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9238559758505384389789517 3464459909439519146171069)
                  ·
                    refine ⟨1299172466039819679814151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464459909439519146171069 1299172466039819679814151)
                    ·
                      rfl

theorem cell22_3795194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_3795194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795194 prefixEnd_3795194 := by exact prefixLift 3795194
  have htrace : WordTrace (prefixWord ++ tailWord_3795194) baseStart_3795194 baseEnd_3795194 := by
    simpa [prefixWord, tailWord_3795194, baseEnd_3795194] using wordTrace_append hprefix tailTrace_3795194
  have hstable : (prefixWord ++ tailWord_3795194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795194).length < 2 ^ (prefixWord ++ tailWord_3795194).sum := by decide
  have hdescent : baseEnd_3795194 < baseStart_3795194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795245 : List Nat := [1, 5, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3795245 : Nat := 118140960795 + 3795245 * 2 ^ 59
def prefixEnd_3795245 : Nat := 4983230072969 + 3 ^ 40 * 3795245 * 2
def baseEnd_3795245 : Nat := 1299189924382072546788995

theorem tailTrace_3795245 : CollatzResearch.WordTrace tailWord_3795245 prefixEnd_3795245 1299189924382072546788995 := by
  unfold tailWord_3795245
  simp only [CollatzResearch.WordTrace]
  refine ⟨138423957135483016087163189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92282638090322010724775459 138423957135483016087163189)
  ·
    refine ⟨12977245981451532758171549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138423957135483016087163189 12977245981451532758171549)
    ·
      refine ⟨4866467243044324784314331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12977245981451532758171549 4866467243044324784314331)
      ·
        refine ⟨7299700864566487176471497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4866467243044324784314331 7299700864566487176471497)
        ·
          refine ⟨5474775648424865382353623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7299700864566487176471497 5474775648424865382353623)
          ·
            refine ⟨8212163472637298073530435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474775648424865382353623 8212163472637298073530435)
            ·
              refine ⟨12318245208955947110295653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8212163472637298073530435 12318245208955947110295653)
              ·
                refine ⟨2309670976679240083180435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12318245208955947110295653 2309670976679240083180435)
                ·
                  refine ⟨3464506465018860124770653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309670976679240083180435 3464506465018860124770653)
                  ·
                    refine ⟨1299189924382072546788995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464506465018860124770653 1299189924382072546788995)
                    ·
                      rfl

theorem cell22_3795245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3795245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795245 prefixEnd_3795245 := by exact prefixLift 3795245
  have htrace : WordTrace (prefixWord ++ tailWord_3795245) baseStart_3795245 baseEnd_3795245 := by
    simpa [prefixWord, tailWord_3795245, baseEnd_3795245] using wordTrace_append hprefix tailTrace_3795245
  have hstable : (prefixWord ++ tailWord_3795245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795245).length < 2 ^ (prefixWord ++ tailWord_3795245).sum := by decide
  have hdescent : baseEnd_3795245 < baseStart_3795245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795267 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 1, 5]
def baseStart_3795267 : Nat := 118140960795 + 3795267 * 2 ^ 59
def prefixEnd_3795267 : Nat := 4983230072969 + 3 ^ 40 * 3795267 * 2
def baseEnd_3795267 : Nat := 1299197455431671822738927

theorem tailTrace_3795267 : CollatzResearch.WordTrace tailWord_3795267 prefixEnd_3795267 1299197455431671822738927 := by
  unfold tailWord_3795267
  simp only [CollatzResearch.WordTrace]
  refine ⟨138424759541403313844464055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92283173027602209229642703 138424759541403313844464055)
  ·
    refine ⟨207637139312104970766696083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138424759541403313844464055 207637139312104970766696083)
    ·
      refine ⟨311455708968157456150044125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207637139312104970766696083 311455708968157456150044125)
      ·
        refine ⟨116795890863059046056266547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311455708968157456150044125 116795890863059046056266547)
        ·
          refine ⟨175193836294588569084399821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116795890863059046056266547 175193836294588569084399821)
          ·
            refine ⟨65697688610470713406649933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175193836294588569084399821 65697688610470713406649933)
            ·
              refine ⟨24636633228926517527493725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65697688610470713406649933 24636633228926517527493725)
              ·
                refine ⟨9238737460847444072810147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24636633228926517527493725 9238737460847444072810147)
                ·
                  refine ⟨13858106191271166109215221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9238737460847444072810147 13858106191271166109215221)
                  ·
                    refine ⟨1299197455431671822738927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13858106191271166109215221 1299197455431671822738927)
                    ·
                      rfl

theorem cell22_3795267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 5].length) (baseStart_3795267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795267 prefixEnd_3795267 := by exact prefixLift 3795267
  have htrace : WordTrace (prefixWord ++ tailWord_3795267) baseStart_3795267 baseEnd_3795267 := by
    simpa [prefixWord, tailWord_3795267, baseEnd_3795267] using wordTrace_append hprefix tailTrace_3795267
  have hstable : (prefixWord ++ tailWord_3795267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795267).length < 2 ^ (prefixWord ++ tailWord_3795267).sum := by decide
  have hdescent : baseEnd_3795267 < baseStart_3795267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795284 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_3795284 : Nat := 118140960795 + 3795284 * 2 ^ 59
def prefixEnd_3795284 : Nat := 4983230072969 + 3 ^ 40 * 3795284 * 2
def baseEnd_3795284 : Nat := 1299203274879089445063875

theorem tailTrace_3795284 : CollatzResearch.WordTrace tailWord_3795284 prefixEnd_3795284 1299203274879089445063875 := by
  unfold tailWord_3795284
  simp only [CollatzResearch.WordTrace]
  refine ⟨69212689791170862873916453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92283586388227817165221937 69212689791170862873916453)
  ·
    refine ⟨12977379335844536788859335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69212689791170862873916453 12977379335844536788859335)
    ·
      refine ⟨19466069003766805183289003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12977379335844536788859335 19466069003766805183289003)
      ·
        refine ⟨29199103505650207774933505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19466069003766805183289003 29199103505650207774933505)
        ·
          refine ⟨21899327629237655831200129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29199103505650207774933505 21899327629237655831200129)
          ·
            refine ⟨16424495721928241873400097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21899327629237655831200129 16424495721928241873400097)
            ·
              refine ⟨12318371791446181405050073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16424495721928241873400097 12318371791446181405050073)
              ·
                refine ⟨9238778843584636053787555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12318371791446181405050073 9238778843584636053787555)
                ·
                  refine ⟨13858168265376954080681333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9238778843584636053787555 13858168265376954080681333)
                  ·
                    refine ⟨1299203274879089445063875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13858168265376954080681333 1299203274879089445063875)
                    ·
                      rfl

theorem cell22_3795284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_3795284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795284 prefixEnd_3795284 := by exact prefixLift 3795284
  have htrace : WordTrace (prefixWord ++ tailWord_3795284) baseStart_3795284 baseEnd_3795284 := by
    simpa [prefixWord, tailWord_3795284, baseEnd_3795284] using wordTrace_append hprefix tailTrace_3795284
  have hstable : (prefixWord ++ tailWord_3795284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795284).length < 2 ^ (prefixWord ++ tailWord_3795284).sum := by decide
  have hdescent : baseEnd_3795284 < baseStart_3795284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795301 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 2, 3]
def baseStart_3795301 : Nat := 118140960795 + 3795301 * 2 ^ 59
def prefixEnd_3795301 : Nat := 4983230072969 + 3 ^ 40 * 3795301 * 2
def baseEnd_3795301 : Nat := 1299209094326507067388823

theorem tailTrace_3795301 : CollatzResearch.WordTrace tailWord_3795301 prefixEnd_3795301 1299209094326507067388823 := by
  unfold tailWord_3795301
  simp only [CollatzResearch.WordTrace]
  refine ⟨138425999623280137651201757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92283999748853425100801171 138425999623280137651201757)
  ·
    refine ⟨51909749858730051619200659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138425999623280137651201757 51909749858730051619200659)
    ·
      refine ⟨77864624788095077428800989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51909749858730051619200659 77864624788095077428800989)
      ·
        refine ⟨29199234295535654035800371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77864624788095077428800989 29199234295535654035800371)
        ·
          refine ⟨43798851443303481053700557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29199234295535654035800371 43798851443303481053700557)
          ·
            refine ⟨16424569291238805395137709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43798851443303481053700557 16424569291238805395137709)
            ·
              refine ⟨6159213484214552023176641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16424569291238805395137709 6159213484214552023176641)
              ·
                refine ⟨4619410113160914017382481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6159213484214552023176641 4619410113160914017382481)
                ·
                  refine ⟨3464557584870685513036861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4619410113160914017382481 3464557584870685513036861)
                  ·
                    refine ⟨1299209094326507067388823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464557584870685513036861 1299209094326507067388823)
                    ·
                      rfl

theorem cell22_3795301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_3795301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795301 prefixEnd_3795301 := by exact prefixLift 3795301
  have htrace : WordTrace (prefixWord ++ tailWord_3795301) baseStart_3795301 baseEnd_3795301 := by
    simpa [prefixWord, tailWord_3795301, baseEnd_3795301] using wordTrace_append hprefix tailTrace_3795301
  have hstable : (prefixWord ++ tailWord_3795301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795301).length < 2 ^ (prefixWord ++ tailWord_3795301).sum := by decide
  have hdescent : baseEnd_3795301 < baseStart_3795301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795331 : List Nat := [1, 1, 1, 3, 6, 2, 2, 6]
def baseStart_3795331 : Nat := 118140960795 + 3795331 * 2 ^ 59
def prefixEnd_3795331 : Nat := 4983230072969 + 3 ^ 40 * 3795331 * 2
def baseEnd_3795331 : Nat := 144357707104399665459859

theorem tailTrace_3795331 : CollatzResearch.WordTrace tailWord_3795331 prefixEnd_3795331 144357707104399665459859 := by
  unfold tailWord_3795331
  simp only [CollatzResearch.WordTrace]
  refine ⟨138427093813171452774793847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92284729208780968516529231 138427093813171452774793847)
  ·
    refine ⟨207640640719757179162190771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138427093813171452774793847 207640640719757179162190771)
    ·
      refine ⟨311460961079635768743286157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207640640719757179162190771 311460961079635768743286157)
      ·
        refine ⟨116797860404863413278732309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311460961079635768743286157 116797860404863413278732309)
        ·
          refine ⟨5474899706477972497440577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116797860404863413278732309 5474899706477972497440577)
          ·
            refine ⟨4106174779858479373080433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5474899706477972497440577 4106174779858479373080433)
            ·
              refine ⟨3079631084893859529810325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4106174779858479373080433 3079631084893859529810325)
              ·
                refine ⟨144357707104399665459859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3079631084893859529810325 144357707104399665459859)
                ·
                  rfl

theorem cell22_3795331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 6].length) (baseStart_3795331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795331 prefixEnd_3795331 := by exact prefixLift 3795331
  have htrace : WordTrace (prefixWord ++ tailWord_3795331) baseStart_3795331 baseEnd_3795331 := by
    simpa [prefixWord, tailWord_3795331, baseEnd_3795331] using wordTrace_append hprefix tailTrace_3795331
  have hstable : (prefixWord ++ tailWord_3795331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795331).length < 2 ^ (prefixWord ++ tailWord_3795331).sum := by decide
  have hdescent : baseEnd_3795331 < baseStart_3795331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795359 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 5]
def baseStart_3795359 : Nat := 118140960795 + 3795359 * 2 ^ 59
def prefixEnd_3795359 : Nat := 4983230072969 + 3 ^ 40 * 3795359 * 2
def baseEnd_3795359 : Nat := 433076316303938083146215

theorem tailTrace_3795359 : CollatzResearch.WordTrace tailWord_3795359 prefixEnd_3795359 433076316303938083146215 := by
  unfold tailWord_3795359
  simp only [CollatzResearch.WordTrace]
  refine ⟨138428115057070013556813131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92285410038046675704542087 138428115057070013556813131)
  ·
    refine ⟨207642172585605020335219697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138428115057070013556813131 207642172585605020335219697)
    ·
      refine ⟨155731629439203765251414773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207642172585605020335219697 155731629439203765251414773)
      ·
        refine ⟨14599840259925352992320135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155731629439203765251414773 14599840259925352992320135)
        ·
          refine ⟨21899760389888029488480203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14599840259925352992320135 21899760389888029488480203)
          ·
            refine ⟨32849640584832044232720305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21899760389888029488480203 32849640584832044232720305)
            ·
              refine ⟨24637230438624033174540229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32849640584832044232720305 24637230438624033174540229)
              ·
                refine ⟨4619480707242006220226293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24637230438624033174540229 4619480707242006220226293)
                ·
                  refine ⟨433076316303938083146215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4619480707242006220226293 433076316303938083146215)
                  ·
                    rfl

theorem cell22_3795359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 5].length) (baseStart_3795359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795359 prefixEnd_3795359 := by exact prefixLift 3795359
  have htrace : WordTrace (prefixWord ++ tailWord_3795359) baseStart_3795359 baseEnd_3795359 := by
    simpa [prefixWord, tailWord_3795359, baseEnd_3795359] using wordTrace_append hprefix tailTrace_3795359
  have hstable : (prefixWord ++ tailWord_3795359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795359).length < 2 ^ (prefixWord ++ tailWord_3795359).sum := by decide
  have hdescent : baseEnd_3795359 < baseStart_3795359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795372 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_3795372 : Nat := 118140960795 + 3795372 * 2 ^ 59
def prefixEnd_3795372 : Nat := 4983230072969 + 3 ^ 40 * 3795372 * 2
def baseEnd_3795372 : Nat := 1299233399077486548863605

theorem tailTrace_3795372 : CollatzResearch.WordTrace tailWord_3795372 prefixEnd_3795372 1299233399077486548863605 := by
  unfold tailWord_3795372
  simp only [CollatzResearch.WordTrace]
  refine ⟨69214294603011458388518185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92285726137348611184690913 69214294603011458388518185)
  ·
    refine ⟨51910720952258593791388639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69214294603011458388518185 51910720952258593791388639)
    ·
      refine ⟨77866081428387890687082959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51910720952258593791388639 77866081428387890687082959)
      ·
        refine ⟨116799122142581836030624439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77866081428387890687082959 116799122142581836030624439)
        ·
          refine ⟨175198683213872754045936659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116799122142581836030624439 175198683213872754045936659)
          ·
            refine ⟨262798024820809131068904989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175198683213872754045936659 262798024820809131068904989)
            ·
              refine ⟨98549259307803424150839371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262798024820809131068904989 98549259307803424150839371)
              ·
                refine ⟨147823888961705136226259057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98549259307803424150839371 147823888961705136226259057)
                ·
                  refine ⟨110867916721278852169694293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147823888961705136226259057 110867916721278852169694293)
                  ·
                    refine ⟨1299233399077486548863605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110867916721278852169694293 1299233399077486548863605)
                    ·
                      rfl

theorem cell22_3795372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_3795372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795372 prefixEnd_3795372 := by exact prefixLift 3795372
  have htrace : WordTrace (prefixWord ++ tailWord_3795372) baseStart_3795372 baseEnd_3795372 := by
    simpa [prefixWord, tailWord_3795372, baseEnd_3795372] using wordTrace_append hprefix tailTrace_3795372
  have hstable : (prefixWord ++ tailWord_3795372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795372).length < 2 ^ (prefixWord ++ tailWord_3795372).sum := by decide
  have hdescent : baseEnd_3795372 < baseStart_3795372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795436 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 2, 3]
def baseStart_3795436 : Nat := 118140960795 + 3795436 * 2 ^ 59
def prefixEnd_3795436 : Nat := 4983230072969 + 3 ^ 40 * 3795436 * 2
def baseEnd_3795436 : Nat := 1299255307585411715263409

theorem tailTrace_3795436 : CollatzResearch.WordTrace tailWord_3795436 prefixEnd_3795436 1299255307585411715263409 := by
  unfold tailWord_3795436
  simp only [CollatzResearch.WordTrace]
  refine ⟨69215461738895527853683081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92287282318527370471577441 69215461738895527853683081)
  ·
    refine ⟨51911596304171645890262311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69215461738895527853683081 51911596304171645890262311)
    ·
      refine ⟨77867394456257468835393467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51911596304171645890262311 77867394456257468835393467)
      ·
        refine ⟨116801091684386203253090201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77867394456257468835393467 116801091684386203253090201)
        ·
          refine ⟨87600818763289652439817651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116801091684386203253090201 87600818763289652439817651)
          ·
            refine ⟨131401228144934478659726477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87600818763289652439817651 131401228144934478659726477)
            ·
              refine ⟨49275460554350429497397429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131401228144934478659726477 49275460554350429497397429)
              ·
                refine ⟨4619574426970352765381009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49275460554350429497397429 4619574426970352765381009)
                ·
                  refine ⟨3464680820227764574035757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4619574426970352765381009 3464680820227764574035757)
                  ·
                    refine ⟨1299255307585411715263409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464680820227764574035757 1299255307585411715263409)
                    ·
                      rfl

theorem cell22_3795436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_3795436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795436 prefixEnd_3795436 := by exact prefixLift 3795436
  have htrace : WordTrace (prefixWord ++ tailWord_3795436) baseStart_3795436 baseEnd_3795436 := by
    simpa [prefixWord, tailWord_3795436, baseEnd_3795436] using wordTrace_append hprefix tailTrace_3795436
  have hstable : (prefixWord ++ tailWord_3795436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795436).length < 2 ^ (prefixWord ++ tailWord_3795436).sum := by decide
  have hdescent : baseEnd_3795436 < baseStart_3795436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795470 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_3795470 : Nat := 118140960795 + 3795470 * 2 ^ 59
def prefixEnd_3795470 : Nat := 4983230072969 + 3 ^ 40 * 3795470 * 2
def baseEnd_3795470 : Nat := 1299266946480246959913305

theorem tailTrace_3795470 : CollatzResearch.WordTrace tailWord_3795470 prefixEnd_3795470 1299266946480246959913305 := by
  unfold tailWord_3795470
  simp only [CollatzResearch.WordTrace]
  refine ⟨17304020444958484939262983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92288109039778586342735909 17304020444958484939262983)
  ·
    refine ⟨25956030667437727408894475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17304020444958484939262983 25956030667437727408894475)
    ·
      refine ⟨38934046001156591113341713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25956030667437727408894475 38934046001156591113341713)
      ·
        refine ⟨29200534500867443335006285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38934046001156591113341713 29200534500867443335006285)
        ·
          refine ⟨10950200437825291250627357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29200534500867443335006285 10950200437825291250627357)
          ·
            refine ⟨4106325164184484218985259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10950200437825291250627357 4106325164184484218985259)
            ·
              refine ⟨6159487746276726328477889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4106325164184484218985259 6159487746276726328477889)
              ·
                refine ⟨4619615809707544746358417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6159487746276726328477889 4619615809707544746358417)
                ·
                  refine ⟨3464711857280658559768813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4619615809707544746358417 3464711857280658559768813)
                  ·
                    refine ⟨1299266946480246959913305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464711857280658559768813 1299266946480246959913305)
                    ·
                      rfl

theorem cell22_3795470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_3795470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795470 prefixEnd_3795470 := by exact prefixLift 3795470
  have htrace : WordTrace (prefixWord ++ tailWord_3795470) baseStart_3795470 baseEnd_3795470 := by
    simpa [prefixWord, tailWord_3795470, baseEnd_3795470] using wordTrace_append hprefix tailTrace_3795470
  have hstable : (prefixWord ++ tailWord_3795470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795470).length < 2 ^ (prefixWord ++ tailWord_3795470).sum := by decide
  have hdescent : baseEnd_3795470 < baseStart_3795470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795498 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 3, 3]
def baseStart_3795498 : Nat := 118140960795 + 3795498 * 2 ^ 59
def prefixEnd_3795498 : Nat := 4983230072969 + 3 ^ 40 * 3795498 * 2
def baseEnd_3795498 : Nat := 1299276531452464220213219

theorem tailTrace_3795498 : CollatzResearch.WordTrace tailWord_3795498 prefixEnd_3795498 1299276531452464220213219 := by
  unfold tailWord_3795498
  simp only [CollatzResearch.WordTrace]
  refine ⟨34608296200891610074030787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92288789869044293530748765 34608296200891610074030787)
  ·
    refine ⟨51912444301337415111046181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34608296200891610074030787 51912444301337415111046181)
    ·
      refine ⟨9733583306500765333321159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51912444301337415111046181 9733583306500765333321159)
      ·
        refine ⟨14600374959751147999981739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9733583306500765333321159 14600374959751147999981739)
        ·
          refine ⟨21900562439626721999972609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14600374959751147999981739 21900562439626721999972609)
          ·
            refine ⟨16425421829720041499979457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21900562439626721999972609 16425421829720041499979457)
            ·
              refine ⟨12319066372290031124984593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16425421829720041499979457 12319066372290031124984593)
              ·
                refine ⟨9239299779217523343738445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12319066372290031124984593 9239299779217523343738445)
                ·
                  refine ⟨3464737417206571253901917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9239299779217523343738445 3464737417206571253901917)
                  ·
                    refine ⟨1299276531452464220213219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464737417206571253901917 1299276531452464220213219)
                    ·
                      rfl

theorem cell22_3795498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_3795498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795498 prefixEnd_3795498 := by exact prefixLift 3795498
  have htrace : WordTrace (prefixWord ++ tailWord_3795498) baseStart_3795498 baseEnd_3795498 := by
    simpa [prefixWord, tailWord_3795498, baseEnd_3795498] using wordTrace_append hprefix tailTrace_3795498
  have hstable : (prefixWord ++ tailWord_3795498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795498).length < 2 ^ (prefixWord ++ tailWord_3795498).sum := by decide
  have hdescent : baseEnd_3795498 < baseStart_3795498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795571 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 4, 3]
def baseStart_3795571 : Nat := 118140960795 + 3795571 * 2 ^ 59
def prefixEnd_3795571 : Nat := 4983230072969 + 3 ^ 40 * 3795571 * 2
def baseEnd_3795571 : Nat := 1299301520844316363137995

theorem tailTrace_3795571 : CollatzResearch.WordTrace tailWord_3795571 prefixEnd_3795571 1299301520844316363137995 := by
  unfold tailWord_3795571
  simp only [CollatzResearch.WordTrace]
  refine ⟨138435847332301973763530567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92290564888201315842353711 138435847332301973763530567)
  ·
    refine ⟨207653770998452960645295851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138435847332301973763530567 207653770998452960645295851)
    ·
      refine ⟨311480656497679440967943777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207653770998452960645295851 311480656497679440967943777)
      ·
        refine ⟨233610492373259580725957833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311480656497679440967943777 233610492373259580725957833)
        ·
          refine ⟨175207869279944685544468375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233610492373259580725957833 175207869279944685544468375)
          ·
            refine ⟨262811803919917028316702563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175207869279944685544468375 262811803919917028316702563)
            ·
              refine ⟨394217705879875542475053845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262811803919917028316702563 394217705879875542475053845)
              ·
                refine ⟨18478954963119166053518149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 394217705879875542475053845 18478954963119166053518149)
                ·
                  refine ⟨3464804055584843635034653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18478954963119166053518149 3464804055584843635034653)
                  ·
                    refine ⟨1299301520844316363137995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464804055584843635034653 1299301520844316363137995)
                    ·
                      rfl

theorem cell22_3795571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 3].length) (baseStart_3795571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795571 prefixEnd_3795571 := by exact prefixLift 3795571
  have htrace : WordTrace (prefixWord ++ tailWord_3795571) baseStart_3795571 baseEnd_3795571 := by
    simpa [prefixWord, tailWord_3795571, baseEnd_3795571] using wordTrace_append hprefix tailTrace_3795571
  have hstable : (prefixWord ++ tailWord_3795571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795571).length < 2 ^ (prefixWord ++ tailWord_3795571).sum := by decide
  have hdescent : baseEnd_3795571 < baseStart_3795571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795584 : List Nat := [2, 1, 1, 2, 1, 15]
def baseStart_3795584 : Nat := 118140960795 + 3795584 * 2 ^ 59
def prefixEnd_3795584 : Nat := 4983230072969 + 3 ^ 40 * 3795584 * 2
def baseEnd_3795584 : Nat := 16040814456913440278555

theorem tailTrace_3795584 : CollatzResearch.WordTrace tailWord_3795584 prefixEnd_3795584 16040814456913440278555 := by
  unfold tailWord_3795584
  simp only [CollatzResearch.WordTrace]
  refine ⟨69218160740627438491876903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92290880987503251322502537 69218160740627438491876903)
  ·
    refine ⟨103827241110941157737815355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69218160740627438491876903 103827241110941157737815355)
    ·
      refine ⟨155740861666411736606723033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103827241110941157737815355 155740861666411736606723033)
      ·
        refine ⟨116805646249808802455042275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155740861666411736606723033 116805646249808802455042275)
        ·
          refine ⟨175208469374713203682563413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116805646249808802455042275 175208469374713203682563413)
          ·
            refine ⟨16040814456913440278555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 175208469374713203682563413 16040814456913440278555)
            ·
              rfl

theorem cell22_3795584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 15].length) (baseStart_3795584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795584 prefixEnd_3795584 := by exact prefixLift 3795584
  have htrace : WordTrace (prefixWord ++ tailWord_3795584) baseStart_3795584 baseEnd_3795584 := by
    simpa [prefixWord, tailWord_3795584, baseEnd_3795584] using wordTrace_append hprefix tailTrace_3795584
  have hstable : (prefixWord ++ tailWord_3795584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795584).length < 2 ^ (prefixWord ++ tailWord_3795584).sum := by decide
  have hdescent : baseEnd_3795584 < baseStart_3795584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795626 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3795626 : Nat := 118140960795 + 3795626 * 2 ^ 59
def prefixEnd_3795626 : Nat := 4983230072969 + 3 ^ 40 * 3795626 * 2
def baseEnd_3795626 : Nat := 1299320348468314553012827

theorem tailTrace_3795626 : CollatzResearch.WordTrace tailWord_3795626 prefixEnd_3795626 1299320348468314553012827 := by
  unfold tailWord_3795626
  simp only [CollatzResearch.WordTrace]
  refine ⟨34609463336775679539195683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92291902231401812104521821 34609463336775679539195683)
  ·
    refine ⟨51914195005163519308793525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34609463336775679539195683 51914195005163519308793525)
    ·
      refine ⟨4866955781734079935199393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51914195005163519308793525 4866955781734079935199393)
      ·
        refine ⟨3650216836300559951399545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4866955781734079935199393 3650216836300559951399545)
        ·
          refine ⟨2737662627225419963549659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3650216836300559951399545 2737662627225419963549659)
          ·
            refine ⟨4106493940838129945324489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737662627225419963549659 4106493940838129945324489)
            ·
              refine ⟨3079870455628597458993367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4106493940838129945324489 3079870455628597458993367)
              ·
                refine ⟨4619805683442896188490051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079870455628597458993367 4619805683442896188490051)
                ·
                  refine ⟨6929708525164344282735077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4619805683442896188490051 6929708525164344282735077)
                  ·
                    refine ⟨1299320348468314553012827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6929708525164344282735077 1299320348468314553012827)
                    ·
                      rfl

theorem cell22_3795626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3795626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795626 prefixEnd_3795626 := by exact prefixLift 3795626
  have htrace : WordTrace (prefixWord ++ tailWord_3795626) baseStart_3795626 baseEnd_3795626 := by
    simpa [prefixWord, tailWord_3795626, baseEnd_3795626] using wordTrace_append hprefix tailTrace_3795626
  have hstable : (prefixWord ++ tailWord_3795626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795626).length < 2 ^ (prefixWord ++ tailWord_3795626).sum := by decide
  have hdescent : baseEnd_3795626 < baseStart_3795626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795701 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3795701 : Nat := 118140960795 + 3795701 * 2 ^ 59
def prefixEnd_3795701 : Nat := 4983230072969 + 3 ^ 40 * 3795701 * 2
def baseEnd_3795701 : Nat := 1299346022501039357387597

theorem tailTrace_3795701 : CollatzResearch.WordTrace tailWord_3795701 prefixEnd_3795701 1299346022501039357387597 := by
  unfold tailWord_3795701
  simp only [CollatzResearch.WordTrace]
  refine ⟨138440588821831005965762957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92293725881220670643841971 138440588821831005965762957)
  ·
    refine ⟨51915220808186627237161109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138440588821831005965762957 51915220808186627237161109)
    ·
      refine ⟨2433525975383748151741927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51915220808186627237161109 2433525975383748151741927)
      ·
        refine ⟨3650288963075622227612891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433525975383748151741927 3650288963075622227612891)
        ·
          refine ⟨5475433444613433341419337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3650288963075622227612891 5475433444613433341419337)
          ·
            refine ⟨4106575083460075006064503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5475433444613433341419337 4106575083460075006064503)
            ·
              refine ⟨6159862625190112509096755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4106575083460075006064503 6159862625190112509096755)
              ·
                refine ⟨9239793937785168763645133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6159862625190112509096755 9239793937785168763645133)
                ·
                  refine ⟨3464922726669438286366925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9239793937785168763645133 3464922726669438286366925)
                  ·
                    refine ⟨1299346022501039357387597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464922726669438286366925 1299346022501039357387597)
                    ·
                      rfl

theorem cell22_3795701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3795701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795701 prefixEnd_3795701 := by exact prefixLift 3795701
  have htrace : WordTrace (prefixWord ++ tailWord_3795701) baseStart_3795701 baseEnd_3795701 := by
    simpa [prefixWord, tailWord_3795701, baseEnd_3795701] using wordTrace_append hprefix tailTrace_3795701
  have hstable : (prefixWord ++ tailWord_3795701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795701).length < 2 ^ (prefixWord ++ tailWord_3795701).sum := by decide
  have hdescent : baseEnd_3795701 < baseStart_3795701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795708 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 6]
def baseStart_3795708 : Nat := 118140960795 + 3795708 * 2 ^ 59
def prefixEnd_3795708 : Nat := 4983230072969 + 3 ^ 40 * 3795708 * 2
def baseEnd_3795708 : Nat := 433116139581364557487525

theorem tailTrace_3795708 : CollatzResearch.WordTrace tailWord_3795708 prefixEnd_3795708 433116139581364557487525 := by
  unfold tailWord_3795708
  simp only [CollatzResearch.WordTrace]
  refine ⟨69220422066402823080633889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92293896088537097440845185 69220422066402823080633889)
  ·
    refine ⟨51915316549802117310475417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69220422066402823080633889 51915316549802117310475417)
    ·
      refine ⟨38936487412351587982856563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51915316549802117310475417 38936487412351587982856563)
      ·
        refine ⟨58404731118527381974284845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38936487412351587982856563 58404731118527381974284845)
        ·
          refine ⟨21901774169447768240356817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58404731118527381974284845 21901774169447768240356817)
          ·
            refine ⟨16426330627085826180267613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21901774169447768240356817 16426330627085826180267613)
            ·
              refine ⟨6159873985157184817600355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16426330627085826180267613 6159873985157184817600355)
              ·
                refine ⟨9239810977735777226400533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6159873985157184817600355 9239810977735777226400533)
                ·
                  refine ⟨433116139581364557487525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9239810977735777226400533 433116139581364557487525)
                  ·
                    rfl

theorem cell22_3795708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_3795708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795708 prefixEnd_3795708 := by exact prefixLift 3795708
  have htrace : WordTrace (prefixWord ++ tailWord_3795708) baseStart_3795708 baseEnd_3795708 := by
    simpa [prefixWord, tailWord_3795708, baseEnd_3795708] using wordTrace_append hprefix tailTrace_3795708
  have hstable : (prefixWord ++ tailWord_3795708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795708).length < 2 ^ (prefixWord ++ tailWord_3795708).sum := by decide
  have hdescent : baseEnd_3795708 < baseStart_3795708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795721 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_3795721 : Nat := 118140960795 + 3795721 * 2 ^ 59
def prefixEnd_3795721 : Nat := 4983230072969 + 3 ^ 40 * 3795721 * 2
def baseEnd_3795721 : Nat := 1299352868909765971887535

theorem tailTrace_3795721 : CollatzResearch.WordTrace tailWord_3795721 prefixEnd_3795721 1299352868909765971887535 := by
  unfold tailWord_3795721
  simp only [CollatzResearch.WordTrace]
  refine ⟨138441318281758549381491017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92294212187839032920994011 138441318281758549381491017)
  ·
    refine ⟨103830988711318912036118263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138441318281758549381491017 103830988711318912036118263)
    ·
      refine ⟨155746483066978368054177395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103830988711318912036118263 155746483066978368054177395)
      ·
        refine ⟨233619724600467552081266093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155746483066978368054177395 233619724600467552081266093)
        ·
          refine ⟨87607396725175332030474785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233619724600467552081266093 87607396725175332030474785)
          ·
            refine ⟨65705547543881499022856089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87607396725175332030474785 65705547543881499022856089)
            ·
              refine ⟨49279160657911124267142067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65705547543881499022856089 49279160657911124267142067)
              ·
                refine ⟨73918740986866686400713101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49279160657911124267142067 73918740986866686400713101)
                ·
                  refine ⟨27719527870075007400267413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73918740986866686400713101 27719527870075007400267413)
                  ·
                    refine ⟨1299352868909765971887535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27719527870075007400267413 1299352868909765971887535)
                    ·
                      rfl

theorem cell22_3795721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_3795721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795721 prefixEnd_3795721 := by exact prefixLift 3795721
  have htrace : WordTrace (prefixWord ++ tailWord_3795721) baseStart_3795721 baseEnd_3795721 := by
    simpa [prefixWord, tailWord_3795721, baseEnd_3795721] using wordTrace_append hprefix tailTrace_3795721
  have hstable : (prefixWord ++ tailWord_3795721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795721).length < 2 ^ (prefixWord ++ tailWord_3795721).sum := by decide
  have hdescent : baseEnd_3795721 < baseStart_3795721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795770 : List Nat := [3, 1, 1, 1, 6, 2, 1, 7]
def baseStart_3795770 : Nat := 118140960795 + 3795770 * 2 ^ 59
def prefixEnd_3795770 : Nat := 4983230072969 + 3 ^ 40 * 3795770 * 2
def baseEnd_3795770 : Nat := 144374404734571797490265

theorem tailTrace_3795770 : CollatzResearch.WordTrace tailWord_3795770 prefixEnd_3795770 144374404734571797490265 := by
  unfold tailWord_3795770
  simp only [CollatzResearch.WordTrace]
  refine ⟨34610776364645257687506191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92295403639054020500016509 34610776364645257687506191)
  ·
    refine ⟨51916164546967886531259287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34610776364645257687506191 51916164546967886531259287)
    ·
      refine ⟨77874246820451829796888931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51916164546967886531259287 77874246820451829796888931)
      ·
        refine ⟨116811370230677744695333397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77874246820451829796888931 116811370230677744695333397)
        ·
          refine ⟨5475532979563019282593753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116811370230677744695333397 5475532979563019282593753)
          ·
            refine ⟨4106649734672264461945315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5475532979563019282593753 4106649734672264461945315)
            ·
              refine ⟨6159974602008396692917973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4106649734672264461945315 6159974602008396692917973)
              ·
                refine ⟨144374404734571797490265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6159974602008396692917973 144374404734571797490265)
                ·
                  rfl

theorem cell22_3795770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_3795770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795770 prefixEnd_3795770 := by exact prefixLift 3795770
  have htrace : WordTrace (prefixWord ++ tailWord_3795770) baseStart_3795770 baseEnd_3795770 := by
    simpa [prefixWord, tailWord_3795770, baseEnd_3795770] using wordTrace_append hprefix tailTrace_3795770
  have hstable : (prefixWord ++ tailWord_3795770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795770).length < 2 ^ (prefixWord ++ tailWord_3795770).sum := by decide
  have hdescent : baseEnd_3795770 < baseStart_3795770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795785 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 3, 3]
def baseStart_3795785 : Nat := 118140960795 + 3795785 * 2 ^ 59
def prefixEnd_3795785 : Nat := 4983230072969 + 3 ^ 40 * 3795785 * 2
def baseEnd_3795785 : Nat := 1299374777417691138287339

theorem tailTrace_3795785 : CollatzResearch.WordTrace tailWord_3795785 prefixEnd_3795785 1299374777417691138287339 := by
  unfold tailWord_3795785
  simp only [CollatzResearch.WordTrace]
  refine ⟨138443652553526688311820809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92295768369017792207880539 138443652553526688311820809)
  ·
    refine ⟨103832739415145016233865607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138443652553526688311820809 103832739415145016233865607)
    ·
      refine ⟨155749109122717524350798411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103832739415145016233865607 155749109122717524350798411)
      ·
        refine ⟨233623663684076286526197617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155749109122717524350798411 233623663684076286526197617)
        ·
          refine ⟨175217747763057214894648213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233623663684076286526197617 175217747763057214894648213)
          ·
            refine ⟨8213331926393306948186635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 175217747763057214894648213 8213331926393306948186635)
            ·
              refine ⟨12319997889589960422279953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8213331926393306948186635 12319997889589960422279953)
              ·
                refine ⟨9239998417192470316709965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12319997889589960422279953 9239998417192470316709965)
                ·
                  refine ⟨3464999406447176368766237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9239998417192470316709965 3464999406447176368766237)
                  ·
                    refine ⟨1299374777417691138287339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3464999406447176368766237 1299374777417691138287339)
                    ·
                      rfl

theorem cell22_3795785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 3].length) (baseStart_3795785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795785 prefixEnd_3795785 := by exact prefixLift 3795785
  have htrace : WordTrace (prefixWord ++ tailWord_3795785) baseStart_3795785 baseEnd_3795785 := by
    simpa [prefixWord, tailWord_3795785, baseEnd_3795785] using wordTrace_append hprefix tailTrace_3795785
  have hstable : (prefixWord ++ tailWord_3795785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795785).length < 2 ^ (prefixWord ++ tailWord_3795785).sum := by decide
  have hdescent : baseEnd_3795785 < baseStart_3795785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795789 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_3795789 : Nat := 118140960795 + 3795789 * 2 ^ 59
def prefixEnd_3795789 : Nat := 4983230072969 + 3 ^ 40 * 3795789 * 2
def baseEnd_3795789 : Nat := 1299376146699436461187327

theorem tailTrace_3795789 : CollatzResearch.WordTrace tailWord_3795789 prefixEnd_3795789 1299376146699436461187327 := by
  unfold tailWord_3795789
  simp only [CollatzResearch.WordTrace]
  refine ⟨138443798445512196994966421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92295865630341464663310947 138443798445512196994966421)
  ·
    refine ⟨6489553052133384234139051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138443798445512196994966421 6489553052133384234139051)
    ·
      refine ⟨9734329578200076351208577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6489553052133384234139051 9734329578200076351208577)
      ·
        refine ⟨7300747183650057263406433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9734329578200076351208577 7300747183650057263406433)
        ·
          refine ⟨5475560387737542947554825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7300747183650057263406433 5475560387737542947554825)
          ·
            refine ⟨4106670290803157210666119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5475560387737542947554825 4106670290803157210666119)
            ·
              refine ⟨6160005436204735815999179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4106670290803157210666119 6160005436204735815999179)
              ·
                refine ⟨9240008154307103723998769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6160005436204735815999179 9240008154307103723998769)
                ·
                  refine ⟨6930006115730327792999077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9240008154307103723998769 6930006115730327792999077)
                  ·
                    refine ⟨1299376146699436461187327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6930006115730327792999077 1299376146699436461187327)
                    ·
                      rfl

theorem cell22_3795789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_3795789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795789 prefixEnd_3795789 := by exact prefixLift 3795789
  have htrace : WordTrace (prefixWord ++ tailWord_3795789) baseStart_3795789 baseEnd_3795789 := by
    simpa [prefixWord, tailWord_3795789, baseEnd_3795789] using wordTrace_append hprefix tailTrace_3795789
  have hstable : (prefixWord ++ tailWord_3795789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795789).length < 2 ^ (prefixWord ++ tailWord_3795789).sum := by decide
  have hdescent : baseEnd_3795789 < baseStart_3795789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795802 : List Nat := [3, 1, 1, 2, 1, 4, 1, 5, 1, 3]
def baseStart_3795802 : Nat := 118140960795 + 3795802 * 2 ^ 59
def prefixEnd_3795802 : Nat := 4983230072969 + 3 ^ 40 * 3795802 * 2
def baseEnd_3795802 : Nat := 1299380596865108760612287

theorem tailTrace_3795802 : CollatzResearch.WordTrace tailWord_3795802 prefixEnd_3795802 1299380596865108760612287 := by
  unfold tailWord_3795802
  simp only [CollatzResearch.WordTrace]
  refine ⟨34611068148616275053797415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92296181729643400143459773 34611068148616275053797415)
  ·
    refine ⟨51916602222924412580696123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34611068148616275053797415 51916602222924412580696123)
    ·
      refine ⟨77874903334386618871044185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51916602222924412580696123 77874903334386618871044185)
      ·
        refine ⟨58406177500789964153283139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77874903334386618871044185 58406177500789964153283139)
        ·
          refine ⟨87609266251184946229924709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58406177500789964153283139 87609266251184946229924709)
          ·
            refine ⟨16426737422097177418110883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87609266251184946229924709 16426737422097177418110883)
            ·
              refine ⟨24640106133145766127166325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16426737422097177418110883 24640106133145766127166325)
              ·
                refine ⟨2310009949982415574421843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24640106133145766127166325 2310009949982415574421843)
                ·
                  refine ⟨3465014924973623361632765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310009949982415574421843 3465014924973623361632765)
                  ·
                    refine ⟨1299380596865108760612287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3465014924973623361632765 1299380596865108760612287)
                    ·
                      rfl

theorem cell22_3795802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_3795802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795802 prefixEnd_3795802 := by exact prefixLift 3795802
  have htrace : WordTrace (prefixWord ++ tailWord_3795802) baseStart_3795802 baseEnd_3795802 := by
    simpa [prefixWord, tailWord_3795802, baseEnd_3795802] using wordTrace_append hprefix tailTrace_3795802
  have hstable : (prefixWord ++ tailWord_3795802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795802).length < 2 ^ (prefixWord ++ tailWord_3795802).sum := by decide
  have hdescent : baseEnd_3795802 < baseStart_3795802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795813 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_3795813 : Nat := 118140960795 + 3795813 * 2 ^ 59
def prefixEnd_3795813 : Nat := 4983230072969 + 3 ^ 40 * 3795813 * 2
def baseEnd_3795813 : Nat := 1299384362389908398587253

theorem tailTrace_3795813 : CollatzResearch.WordTrace tailWord_3795813 prefixEnd_3795813 1299384362389908398587253 := by
  unfold tailWord_3795813
  simp only [CollatzResearch.WordTrace]
  refine ⟨138444673797425249093840093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92296449198283499395893395 138444673797425249093840093)
  ·
    refine ⟨51916752674034468410190035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138444673797425249093840093 51916752674034468410190035)
    ·
      refine ⟨77875129011051702615285053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51916752674034468410190035 77875129011051702615285053)
      ·
        refine ⟨29203173379144388480731895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77875129011051702615285053 29203173379144388480731895)
        ·
          refine ⟨43804760068716582721097843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29203173379144388480731895 43804760068716582721097843)
          ·
            refine ⟨65707140103074874081646765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43804760068716582721097843 65707140103074874081646765)
            ·
              refine ⟨24640177538653077780617537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65707140103074874081646765 24640177538653077780617537)
              ·
                refine ⟨18480133153989808335463153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24640177538653077780617537 18480133153989808335463153)
                ·
                  refine ⟨13860099865492356251597365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18480133153989808335463153 13860099865492356251597365)
                  ·
                    refine ⟨1299384362389908398587253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13860099865492356251597365 1299384362389908398587253)
                    ·
                      rfl

theorem cell22_3795813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_3795813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795813 prefixEnd_3795813 := by exact prefixLift 3795813
  have htrace : WordTrace (prefixWord ++ tailWord_3795813) baseStart_3795813 baseEnd_3795813 := by
    simpa [prefixWord, tailWord_3795813, baseEnd_3795813] using wordTrace_append hprefix tailTrace_3795813
  have hstable : (prefixWord ++ tailWord_3795813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795813).length < 2 ^ (prefixWord ++ tailWord_3795813).sum := by decide
  have hdescent : baseEnd_3795813 < baseStart_3795813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795815 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 5]
def baseStart_3795815 : Nat := 118140960795 + 3795815 * 2 ^ 59
def prefixEnd_3795815 : Nat := 4983230072969 + 3 ^ 40 * 3795815 * 2
def baseEnd_3795815 : Nat := 433128349010260353345749

theorem tailTrace_3795815 : CollatzResearch.WordTrace tailWord_3795815 prefixEnd_3795815 433128349010260353345749 := by
  unfold tailWord_3795815
  simp only [CollatzResearch.WordTrace]
  refine ⟨138444746743418003435412899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92296497828945335623608599 138444746743418003435412899)
  ·
    refine ⟨207667120115127005153119349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138444746743418003435412899 207667120115127005153119349)
    ·
      refine ⟨19468792510793156733104939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207667120115127005153119349 19468792510793156733104939)
      ·
        refine ⟨29203188766189735099657409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19468792510793156733104939 29203188766189735099657409)
        ·
          refine ⟨21902391574642301324743057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29203188766189735099657409 21902391574642301324743057)
          ·
            refine ⟨16426793680981725993557293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21902391574642301324743057 16426793680981725993557293)
            ·
              refine ⟨6160047630368147247583985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16426793680981725993557293 6160047630368147247583985)
              ·
                refine ⟨4620035722776110435687989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6160047630368147247583985 4620035722776110435687989)
                ·
                  refine ⟨433128349010260353345749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4620035722776110435687989 433128349010260353345749)
                  ·
                    rfl

theorem cell22_3795815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 5].length) (baseStart_3795815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795815 prefixEnd_3795815 := by exact prefixLift 3795815
  have htrace : WordTrace (prefixWord ++ tailWord_3795815) baseStart_3795815 baseEnd_3795815 := by
    simpa [prefixWord, tailWord_3795815, baseEnd_3795815] using wordTrace_append hprefix tailTrace_3795815
  have hstable : (prefixWord ++ tailWord_3795815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795815).length < 2 ^ (prefixWord ++ tailWord_3795815).sum := by decide
  have hdescent : baseEnd_3795815 < baseStart_3795815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795843 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 6]
def baseStart_3795843 : Nat := 118140960795 + 3795843 * 2 ^ 59
def prefixEnd_3795843 : Nat := 4983230072969 + 3 ^ 40 * 3795843 * 2
def baseEnd_3795843 : Nat := 433131544000999440112387

theorem tailTrace_3795843 : CollatzResearch.WordTrace tailWord_3795843 prefixEnd_3795843 433131544000999440112387 := by
  unfold tailWord_3795843
  simp only [CollatzResearch.WordTrace]
  refine ⟨138445767987316564217432183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92297178658211042811621455 138445767987316564217432183)
  ·
    refine ⟨207668651980974846326148275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138445767987316564217432183 207668651980974846326148275)
    ·
      refine ⟨311502977971462269489222413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207668651980974846326148275 311502977971462269489222413)
      ·
        refine ⟨116813616739298351058458405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311502977971462269489222413 116813616739298351058458405)
        ·
          refine ⟨21902553138618440823460951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116813616739298351058458405 21902553138618440823460951)
          ·
            refine ⟨32853829707927661235191427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21902553138618440823460951 32853829707927661235191427)
            ·
              refine ⟨49280744561891491852787141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32853829707927661235191427 49280744561891491852787141)
              ·
                refine ⟨9240139605354654722397589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49280744561891491852787141 9240139605354654722397589)
                ·
                  refine ⟨433131544000999440112387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9240139605354654722397589 433131544000999440112387)
                  ·
                    rfl

theorem cell22_3795843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 6].length) (baseStart_3795843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795843 prefixEnd_3795843 := by exact prefixLift 3795843
  have htrace : WordTrace (prefixWord ++ tailWord_3795843) baseStart_3795843 baseEnd_3795843 := by
    simpa [prefixWord, tailWord_3795843, baseEnd_3795843] using wordTrace_append hprefix tailTrace_3795843
  have hstable : (prefixWord ++ tailWord_3795843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795843).length < 2 ^ (prefixWord ++ tailWord_3795843).sum := by decide
  have hdescent : baseEnd_3795843 < baseStart_3795843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795845 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_3795845 : Nat := 118140960795 + 3795845 * 2 ^ 59
def prefixEnd_3795845 : Nat := 4983230072969 + 3 ^ 40 * 3795845 * 2
def baseEnd_3795845 : Nat := 1299395316643870981787155

theorem tailTrace_3795845 : CollatzResearch.WordTrace tailWord_3795845 prefixEnd_3795845 1299395316643870981787155 := by
  unfold tailWord_3795845
  simp only [CollatzResearch.WordTrace]
  refine ⟨138445840933309318559004989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92297227288872879039336659 138445840933309318559004989)
  ·
    refine ⟨51917190349990994459626871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138445840933309318559004989 51917190349990994459626871)
    ·
      refine ⟨77875785524986491689440307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51917190349990994459626871 77875785524986491689440307)
      ·
        refine ⟨116813678287479737534160461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77875785524986491689440307 116813678287479737534160461)
        ·
          refine ⟨43805129357804901575310173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116813678287479737534160461 43805129357804901575310173)
          ·
            refine ⟨16426923509176838090741315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43805129357804901575310173 16426923509176838090741315)
            ·
              refine ⟨24640385263765257136111973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16426923509176838090741315 24640385263765257136111973)
              ·
                refine ⟨4620072236955985713020995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24640385263765257136111973 4620072236955985713020995)
                ·
                  refine ⟨6930108355433978569531493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4620072236955985713020995 6930108355433978569531493)
                  ·
                    refine ⟨1299395316643870981787155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6930108355433978569531493 1299395316643870981787155)
                    ·
                      rfl

theorem cell22_3795845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_3795845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795845 prefixEnd_3795845 := by exact prefixLift 3795845
  have htrace : WordTrace (prefixWord ++ tailWord_3795845) baseStart_3795845 baseEnd_3795845 := by
    simpa [prefixWord, tailWord_3795845, baseEnd_3795845] using wordTrace_append hprefix tailTrace_3795845
  have hstable : (prefixWord ++ tailWord_3795845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795845).length < 2 ^ (prefixWord ++ tailWord_3795845).sum := by decide
  have hdescent : baseEnd_3795845 < baseStart_3795845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795875 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 4, 3]
def baseStart_3795875 : Nat := 118140960795 + 3795875 * 2 ^ 59
def prefixEnd_3795875 : Nat := 4983230072969 + 3 ^ 40 * 3795875 * 2
def baseEnd_3795875 : Nat := 1299405586256960903537063

theorem tailTrace_3795875 : CollatzResearch.WordTrace tailWord_3795875 prefixEnd_3795875 1299405586256960903537063 := by
  unfold tailWord_3795875
  simp only [CollatzResearch.WordTrace]
  refine ⟨138446935123200633682597079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92297956748800422455064719 138446935123200633682597079)
  ·
    refine ⟨207670402684800950523895619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138446935123200633682597079 207670402684800950523895619)
    ·
      refine ⟨311505604027201425785843429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207670402684800950523895619 311505604027201425785843429)
      ·
        refine ⟨58407300755100267334845643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311505604027201425785843429 58407300755100267334845643)
        ·
          refine ⟨87610951132650401002268465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58407300755100267334845643 87610951132650401002268465)
          ·
            refine ⟨65708213349487800751701349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87610951132650401002268465 65708213349487800751701349)
            ·
              refine ⟨12320290003028962640944003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65708213349487800751701349 12320290003028962640944003)
              ·
                refine ⟨18480435004543443961416005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12320290003028962640944003 18480435004543443961416005)
                ·
                  refine ⟨3465081563351895742765501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18480435004543443961416005 3465081563351895742765501)
                  ·
                    refine ⟨1299405586256960903537063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3465081563351895742765501 1299405586256960903537063)
                    ·
                      rfl

theorem cell22_3795875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 3].length) (baseStart_3795875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795875 prefixEnd_3795875 := by exact prefixLift 3795875
  have htrace : WordTrace (prefixWord ++ tailWord_3795875) baseStart_3795875 baseEnd_3795875 := by
    simpa [prefixWord, tailWord_3795875, baseEnd_3795875] using wordTrace_append hprefix tailTrace_3795875
  have hstable : (prefixWord ++ tailWord_3795875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795875).length < 2 ^ (prefixWord ++ tailWord_3795875).sum := by decide
  have hdescent : baseEnd_3795875 < baseStart_3795875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3795926 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_3795926 : Nat := 118140960795 + 3795926 * 2 ^ 59
def prefixEnd_3795926 : Nat := 4983230072969 + 3 ^ 40 * 3795926 * 2
def baseEnd_3795926 : Nat := 1299423044599213770511907

theorem tailTrace_3795926 : CollatzResearch.WordTrace tailWord_3795926 prefixEnd_3795926 1299423044599213770511907 := by
  unfold tailWord_3795926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8653049702875991837043977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92299196830677246261802421 8653049702875991837043977)
  ·
    refine ⟨6489787277156993877782983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8653049702875991837043977 6489787277156993877782983)
    ·
      refine ⟨9734680915735490816674475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6489787277156993877782983 9734680915735490816674475)
      ·
        refine ⟨14602021373603236225011713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9734680915735490816674475 14602021373603236225011713)
        ·
          refine ⟨10951516030202427168758785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14602021373603236225011713 10951516030202427168758785)
          ·
            refine ⟨8213637022651820376569089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10951516030202427168758785 8213637022651820376569089)
            ·
              refine ⟨6160227766988865282426817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8213637022651820376569089 6160227766988865282426817)
              ·
                refine ⟨4620170825241648961820113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6160227766988865282426817 4620170825241648961820113)
                ·
                  refine ⟨3465128118931236721365085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4620170825241648961820113 3465128118931236721365085)
                  ·
                    refine ⟨1299423044599213770511907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3465128118931236721365085 1299423044599213770511907)
                    ·
                      rfl

theorem cell22_3795926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_3795926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3795926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3795926 prefixEnd_3795926 := by exact prefixLift 3795926
  have htrace : WordTrace (prefixWord ++ tailWord_3795926) baseStart_3795926 baseEnd_3795926 := by
    simpa [prefixWord, tailWord_3795926, baseEnd_3795926] using wordTrace_append hprefix tailTrace_3795926
  have hstable : (prefixWord ++ tailWord_3795926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3795926).length < 2 ^ (prefixWord ++ tailWord_3795926).sum := by decide
  have hdescent : baseEnd_3795926 < baseStart_3795926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3795926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796014 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3796014 : Nat := 118140960795 + 3796014 * 2 ^ 59
def prefixEnd_3796014 : Nat := 4983230072969 + 3 ^ 40 * 3796014 * 2
def baseEnd_3796014 : Nat := 1299453168797610874311637

theorem tailTrace_3796014 : CollatzResearch.WordTrace tailWord_3796014 prefixEnd_3796014 1299453168797610874311637 := by
  unfold tailWord_3796014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17306500608712132552738387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92301336579798040281271397 17306500608712132552738387)
  ·
    refine ⟨25959750913068198829107581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17306500608712132552738387 25959750913068198829107581)
    ·
      refine ⟨9734906592400574560915343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25959750913068198829107581 9734906592400574560915343)
      ·
        refine ⟨14602359888600861841373015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9734906592400574560915343 14602359888600861841373015)
        ·
          refine ⟨21903539832901292762059523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14602359888600861841373015 21903539832901292762059523)
          ·
            refine ⟨32855309749351939143089285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21903539832901292762059523 32855309749351939143089285)
            ·
              refine ⟨6160370578003488589329241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32855309749351939143089285 6160370578003488589329241)
              ·
                refine ⟨4620277933502616441996931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6160370578003488589329241 4620277933502616441996931)
                ·
                  refine ⟨6930416900253924662995397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4620277933502616441996931 6930416900253924662995397)
                  ·
                    refine ⟨1299453168797610874311637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6930416900253924662995397 1299453168797610874311637)
                    ·
                      rfl

theorem cell22_3796014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3796014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796014 prefixEnd_3796014 := by exact prefixLift 3796014
  have htrace : WordTrace (prefixWord ++ tailWord_3796014) baseStart_3796014 baseEnd_3796014 := by
    simpa [prefixWord, tailWord_3796014, baseEnd_3796014] using wordTrace_append hprefix tailTrace_3796014
  have hstable : (prefixWord ++ tailWord_3796014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796014).length < 2 ^ (prefixWord ++ tailWord_3796014).sum := by decide
  have hdescent : baseEnd_3796014 < baseStart_3796014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796029 : List Nat := [1, 4, 1, 3, 1, 2, 3, 3, 4]
def baseStart_3796029 : Nat := 118140960795 + 3796029 * 2 ^ 59
def prefixEnd_3796029 : Nat := 4983230072969 + 3 ^ 40 * 3796029 * 2
def baseEnd_3796029 : Nat := 433152767868051945062197

theorem tailTrace_3796029 : CollatzResearch.WordTrace tailWord_3796029 prefixEnd_3796029 433152767868051945062197 := by
  unfold tailWord_3796029
  simp only [CollatzResearch.WordTrace]
  refine ⟨138452551964642717983703141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92301701309761811989135427 138452551964642717983703141)
  ·
    refine ⟨25959853493370509621944339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138452551964642717983703141 25959853493370509621944339)
    ·
      refine ⟨38939780240055764432916509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25959853493370509621944339 38939780240055764432916509)
      ·
        refine ⟨14602417590020911662343691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38939780240055764432916509 14602417590020911662343691)
        ·
          refine ⟨21903626385031367493515537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14602417590020911662343691 21903626385031367493515537)
          ·
            refine ⟨16427719788773525620136653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21903626385031367493515537 16427719788773525620136653)
            ·
              refine ⟨6160394920790072107551245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16427719788773525620136653 6160394920790072107551245)
              ·
                refine ⟨2310148095296277040331717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6160394920790072107551245 2310148095296277040331717)
                ·
                  refine ⟨433152767868051945062197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2310148095296277040331717 433152767868051945062197)
                  ·
                    rfl

theorem cell22_3796029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_3796029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796029 prefixEnd_3796029 := by exact prefixLift 3796029
  have htrace : WordTrace (prefixWord ++ tailWord_3796029) baseStart_3796029 baseEnd_3796029 := by
    simpa [prefixWord, tailWord_3796029, baseEnd_3796029] using wordTrace_append hprefix tailTrace_3796029
  have hstable : (prefixWord ++ tailWord_3796029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796029).length < 2 ^ (prefixWord ++ tailWord_3796029).sum := by decide
  have hdescent : baseEnd_3796029 < baseStart_3796029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796106 : List Nat := [3, 1, 2, 3, 1, 1, 3, 4, 1, 3]
def baseStart_3796106 : Nat := 118140960795 + 3796106 * 2 ^ 59
def prefixEnd_3796106 : Nat := 4983230072969 + 3 ^ 40 * 3796106 * 2
def baseEnd_3796106 : Nat := 1299484662277753301011355

theorem tailTrace_3796106 : CollatzResearch.WordTrace tailWord_3796106 prefixEnd_3796106 1299484662277753301011355 := by
  unfold tailWord_3796106
  simp only [CollatzResearch.WordTrace]
  refine ⟨34613840096340940033564043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92303573590242506756170781 34613840096340940033564043)
  ·
    refine ⟨51920760144511410050346065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34613840096340940033564043 51920760144511410050346065)
    ·
      refine ⟨38940570108383557537759549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51920760144511410050346065 38940570108383557537759549)
      ·
        refine ⟨14602713790643834076659831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38940570108383557537759549 14602713790643834076659831)
        ·
          refine ⟨21904070685965751114989747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14602713790643834076659831 21904070685965751114989747)
          ·
            refine ⟨32856106028948626672484621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21904070685965751114989747 32856106028948626672484621)
            ·
              refine ⟨12321039760855735002181733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32856106028948626672484621 12321039760855735002181733)
              ·
                refine ⟨2310194955160450312909075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12321039760855735002181733 2310194955160450312909075)
                ·
                  refine ⟨3465292432740675469363613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310194955160450312909075 3465292432740675469363613)
                  ·
                    refine ⟨1299484662277753301011355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3465292432740675469363613 1299484662277753301011355)
                    ·
                      rfl

theorem cell22_3796106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_3796106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796106 prefixEnd_3796106 := by exact prefixLift 3796106
  have htrace : WordTrace (prefixWord ++ tailWord_3796106) baseStart_3796106 baseEnd_3796106 := by
    simpa [prefixWord, tailWord_3796106, baseEnd_3796106] using wordTrace_append hprefix tailTrace_3796106
  have hstable : (prefixWord ++ tailWord_3796106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796106).length < 2 ^ (prefixWord ++ tailWord_3796106).sum := by decide
  have hdescent : baseEnd_3796106 < baseStart_3796106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796192 : List Nat := [2, 1, 1, 3, 1, 5, 1, 8]
def baseStart_3796192 : Nat := 118140960795 + 3796192 * 2 ^ 59
def prefixEnd_3796192 : Nat := 4983230072969 + 3 ^ 40 * 3796192 * 2
def baseEnd_3796192 : Nat := 144390455759475304817899

theorem tailTrace_3796192 : CollatzResearch.WordTrace tailWord_3796192 prefixEnd_3796192 144390455759475304817899 := by
  unfold tailWord_3796192
  simp only [CollatzResearch.WordTrace]
  refine ⟨69229248531526098410943415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92305664708701464547924553 69229248531526098410943415)
  ·
    refine ⟨103843872797289147616415123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69229248531526098410943415 103843872797289147616415123)
    ·
      refine ⟨155765809195933721424622685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103843872797289147616415123 155765809195933721424622685)
      ·
        refine ⟨58412178448475145534233507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155765809195933721424622685 58412178448475145534233507)
        ·
          refine ⟨87618267672712718301350261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58412178448475145534233507 87618267672712718301350261)
          ·
            refine ⟨8214212594316817340751587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87618267672712718301350261 8214212594316817340751587)
            ·
              refine ⟨12321318891475226011127381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8214212594316817340751587 12321318891475226011127381)
              ·
                refine ⟨144390455759475304817899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12321318891475226011127381 144390455759475304817899)
                ·
                  rfl

theorem cell22_3796192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 8].length) (baseStart_3796192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796192 prefixEnd_3796192 := by exact prefixLift 3796192
  have htrace : WordTrace (prefixWord ++ tailWord_3796192) baseStart_3796192 baseEnd_3796192 := by
    simpa [prefixWord, tailWord_3796192, baseEnd_3796192] using wordTrace_append hprefix tailTrace_3796192
  have hstable : (prefixWord ++ tailWord_3796192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796192).length < 2 ^ (prefixWord ++ tailWord_3796192).sum := by decide
  have hdescent : baseEnd_3796192 < baseStart_3796192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796226 : List Nat := [3, 4, 1, 1, 3, 1, 2, 7]
def baseStart_3796226 : Nat := 118140960795 + 3796226 * 2 ^ 59
def prefixEnd_3796226 : Nat := 4983230072969 + 3 ^ 40 * 3796226 * 2
def baseEnd_3796226 : Nat := 144391748970012554223443

theorem tailTrace_3796226 : CollatzResearch.WordTrace tailWord_3796226 prefixEnd_3796226 144391748970012554223443 := by
  unfold tailWord_3796226
  simp only [CollatzResearch.WordTrace]
  refine ⟨34614934286232255157156133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92306491429952680419083021 34614934286232255157156133)
  ·
    refine ⟨6490300178668547841966775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34614934286232255157156133 6490300178668547841966775)
    ·
      refine ⟨9735450268002821762950163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6490300178668547841966775 9735450268002821762950163)
      ·
        refine ⟨14603175402004232644425245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9735450268002821762950163 14603175402004232644425245)
        ·
          refine ⟨5476190775751587241659467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14603175402004232644425245 5476190775751587241659467)
          ·
            refine ⟨8214286163627380862489201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5476190775751587241659467 8214286163627380862489201)
            ·
              refine ⟨6160714622720535646866901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8214286163627380862489201 6160714622720535646866901)
              ·
                refine ⟨144391748970012554223443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6160714622720535646866901 144391748970012554223443)
                ·
                  rfl

theorem cell22_3796226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_3796226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796226 prefixEnd_3796226 := by exact prefixLift 3796226
  have htrace : WordTrace (prefixWord ++ tailWord_3796226) baseStart_3796226 baseEnd_3796226 := by
    simpa [prefixWord, tailWord_3796226, baseEnd_3796226] using wordTrace_append hprefix tailTrace_3796226
  have hstable : (prefixWord ++ tailWord_3796226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796226).length < 2 ^ (prefixWord ++ tailWord_3796226).sum := by decide
  have hdescent : baseEnd_3796226 < baseStart_3796226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796275 : List Nat := [1, 1, 1, 2, 5, 4, 2, 2, 1, 3]
def baseStart_3796275 : Nat := 118140960795 + 3796275 * 2 ^ 59
def prefixEnd_3796275 : Nat := 4983230072969 + 3 ^ 40 * 3796275 * 2
def baseEnd_3796275 : Nat := 1299542514431493193535837

theorem tailTrace_3796275 : CollatzResearch.WordTrace tailWord_3796275 prefixEnd_3796275 1299542514431493193535837 := by
  unfold tailWord_3796275
  simp only [CollatzResearch.WordTrace]
  refine ⟨138461524321751501997158279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92307682881167667998105519 138461524321751501997158279)
  ·
    refine ⟨207692286482627252995737419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138461524321751501997158279 207692286482627252995737419)
    ·
      refine ⟨311538429723940879493606129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207692286482627252995737419 311538429723940879493606129)
      ·
        refine ⟨233653822292955659620204597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311538429723940879493606129 233653822292955659620204597)
        ·
          refine ⟨21905045839964593089394181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233653822292955659620204597 21905045839964593089394181)
          ·
            refine ⟨4107196094993361204261409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21905045839964593089394181 4107196094993361204261409)
            ·
              refine ⟨3080397071245020903196057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4107196094993361204261409 3080397071245020903196057)
              ·
                refine ⟨2310297803433765677397043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3080397071245020903196057 2310297803433765677397043)
                ·
                  refine ⟨3465446705150648516095565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310297803433765677397043 3465446705150648516095565)
                  ·
                    refine ⟨1299542514431493193535837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3465446705150648516095565 1299542514431493193535837)
                    ·
                      rfl

theorem cell22_3796275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 1, 3].length) (baseStart_3796275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796275 prefixEnd_3796275 := by exact prefixLift 3796275
  have htrace : WordTrace (prefixWord ++ tailWord_3796275) baseStart_3796275 baseEnd_3796275 := by
    simpa [prefixWord, tailWord_3796275, baseEnd_3796275] using wordTrace_append hprefix tailTrace_3796275
  have hstable : (prefixWord ++ tailWord_3796275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796275).length < 2 ^ (prefixWord ++ tailWord_3796275).sum := by decide
  have hdescent : baseEnd_3796275 < baseStart_3796275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796284 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_3796284 : Nat := 118140960795 + 3796284 * 2 ^ 59
def prefixEnd_3796284 : Nat := 4983230072969 + 3 ^ 40 * 3796284 * 2
def baseEnd_3796284 : Nat := 1299545595315420170060809

theorem tailTrace_3796284 : CollatzResearch.WordTrace tailWord_3796284 prefixEnd_3796284 1299545595315420170060809 := by
  unfold tailWord_3796284
  simp only [CollatzResearch.WordTrace]
  refine ⟨69230926289359448267117953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92307901719145931022823937 69230926289359448267117953)
  ·
    refine ⟨51923194717019586200338465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69230926289359448267117953 51923194717019586200338465)
    ·
      refine ⟨38942396037764689650253849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51923194717019586200338465 38942396037764689650253849)
      ·
        refine ⟨29206797028323517237690387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38942396037764689650253849 29206797028323517237690387)
        ·
          refine ⟨43810195542485275856535581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29206797028323517237690387 43810195542485275856535581)
          ·
            refine ⟨16428823328431978446200843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43810195542485275856535581 16428823328431978446200843)
            ·
              refine ⟨24643234992647967669301265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16428823328431978446200843 24643234992647967669301265)
              ·
                refine ⟨18482426244485975751975949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24643234992647967669301265 18482426244485975751975949)
                ·
                  refine ⟨6930909841682240906990981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18482426244485975751975949 6930909841682240906990981)
                  ·
                    refine ⟨1299545595315420170060809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6930909841682240906990981 1299545595315420170060809)
                    ·
                      rfl

theorem cell22_3796284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_3796284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796284 prefixEnd_3796284 := by exact prefixLift 3796284
  have htrace : WordTrace (prefixWord ++ tailWord_3796284) baseStart_3796284 baseEnd_3796284 := by
    simpa [prefixWord, tailWord_3796284, baseEnd_3796284] using wordTrace_append hprefix tailTrace_3796284
  have hstable : (prefixWord ++ tailWord_3796284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796284).length < 2 ^ (prefixWord ++ tailWord_3796284).sum := by decide
  have hdescent : baseEnd_3796284 < baseStart_3796284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796314 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_3796314 : Nat := 118140960795 + 3796314 * 2 ^ 59
def prefixEnd_3796314 : Nat := 4983230072969 + 3 ^ 40 * 3796314 * 2
def baseEnd_3796314 : Nat := 1299555864928510091810717

theorem tailTrace_3796314 : CollatzResearch.WordTrace tailWord_3796314 prefixEnd_3796314 1299555864928510091810717 := by
  unfold tailWord_3796314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34615736692152552914456999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92308631179073474438551997 34615736692152552914456999)
  ·
    refine ⟨51923605038228829371685499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34615736692152552914456999 51923605038228829371685499)
    ·
      refine ⟨77885407557343244057528249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51923605038228829371685499 77885407557343244057528249)
      ·
        refine ⟨58414055668007433043146187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77885407557343244057528249 58414055668007433043146187)
        ·
          refine ⟨87621083502011149564719281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58414055668007433043146187 87621083502011149564719281)
          ·
            refine ⟨65715812626508362173539461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87621083502011149564719281 65715812626508362173539461)
            ·
              refine ⟨12321714867470317907538649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65715812626508362173539461 12321714867470317907538649)
              ·
                refine ⟨9241286150602738430653987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12321714867470317907538649 9241286150602738430653987)
                ·
                  refine ⟨13861929225904107645980981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9241286150602738430653987 13861929225904107645980981)
                  ·
                    refine ⟨1299555864928510091810717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13861929225904107645980981 1299555864928510091810717)
                    ·
                      rfl

theorem cell22_3796314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_3796314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796314 prefixEnd_3796314 := by exact prefixLift 3796314
  have htrace : WordTrace (prefixWord ++ tailWord_3796314) baseStart_3796314 baseEnd_3796314 := by
    simpa [prefixWord, tailWord_3796314, baseEnd_3796314] using wordTrace_append hprefix tailTrace_3796314
  have hstable : (prefixWord ++ tailWord_3796314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796314).length < 2 ^ (prefixWord ++ tailWord_3796314).sum := by decide
  have hdescent : baseEnd_3796314 < baseStart_3796314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796348 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 2, 3]
def baseStart_3796348 : Nat := 118140960795 + 3796348 * 2 ^ 59
def prefixEnd_3796348 : Nat := 4983230072969 + 3 ^ 40 * 3796348 * 2
def baseEnd_3796348 : Nat := 1299567503823345336460613

theorem tailTrace_3796348 : CollatzResearch.WordTrace tailWord_3796348 prefixEnd_3796348 1299567503823345336460613 := by
  unfold tailWord_3796348
  simp only [CollatzResearch.WordTrace]
  refine ⟨69232093425243517732282849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92309457900324690309710465 69232093425243517732282849)
  ·
    refine ⟨51924070068932638299212137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69232093425243517732282849 51924070068932638299212137)
    ·
      refine ⟨38943052551699478724409103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51924070068932638299212137 38943052551699478724409103)
      ·
        refine ⟨58414578827549218086613655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38943052551699478724409103 58414578827549218086613655)
        ·
          refine ⟨87621868241323827129920483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58414578827549218086613655 87621868241323827129920483)
          ·
            refine ⟨131432802361985740694880725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87621868241323827129920483 131432802361985740694880725)
            ·
              refine ⟨3080456305359040797536267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 131432802361985740694880725 3080456305359040797536267)
              ·
                refine ⟨4620684458038561196304401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3080456305359040797536267 4620684458038561196304401)
                ·
                  refine ⟨3465513343528920897228301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4620684458038561196304401 3465513343528920897228301)
                  ·
                    refine ⟨1299567503823345336460613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3465513343528920897228301 1299567503823345336460613)
                    ·
                      rfl

theorem cell22_3796348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_3796348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796348 prefixEnd_3796348 := by exact prefixLift 3796348
  have htrace : WordTrace (prefixWord ++ tailWord_3796348) baseStart_3796348 baseEnd_3796348 := by
    simpa [prefixWord, tailWord_3796348, baseEnd_3796348] using wordTrace_append hprefix tailTrace_3796348
  have hstable : (prefixWord ++ tailWord_3796348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796348).length < 2 ^ (prefixWord ++ tailWord_3796348).sum := by decide
  have hdescent : baseEnd_3796348 < baseStart_3796348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796603 : List Nat := [1, 1, 1, 1, 1, 4, 4, 5, 4]
def baseStart_3796603 : Nat := 118140960795 + 3796603 * 2 ^ 59
def prefixEnd_3796603 : Nat := 4983230072969 + 3 ^ 40 * 3796603 * 2
def baseEnd_3796603 : Nat := 433218265178203223778277

theorem tailTrace_3796603 : CollatzResearch.WordTrace tailWord_3796603 prefixEnd_3796603 433218265178203223778277 := by
  unfold tailWord_3796603
  simp only [CollatzResearch.WordTrace]
  refine ⟨138473487464563214015098463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92315658309708809343398975 138473487464563214015098463)
  ·
    refine ⟨207710231196844821022647695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138473487464563214015098463 207710231196844821022647695)
    ·
      refine ⟨311565346795267231533971543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207710231196844821022647695 311565346795267231533971543)
      ·
        refine ⟨467348020192900847300957315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311565346795267231533971543 467348020192900847300957315)
        ·
          refine ⟨701022030289351270951435973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467348020192900847300957315 701022030289351270951435973)
          ·
            refine ⟨131441630679253363303394245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 701022030289351270951435973 131441630679253363303394245)
            ·
              refine ⟨24645305752360005619386421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131441630679253363303394245 24645305752360005619386421)
              ·
                refine ⟨2310497414283750526817477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24645305752360005619386421 2310497414283750526817477)
                ·
                  refine ⟨433218265178203223778277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2310497414283750526817477 433218265178203223778277)
                  ·
                    rfl

theorem cell22_3796603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 4].length) (baseStart_3796603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796603 prefixEnd_3796603 := by exact prefixLift 3796603
  have htrace : WordTrace (prefixWord ++ tailWord_3796603) baseStart_3796603 baseEnd_3796603 := by
    simpa [prefixWord, tailWord_3796603, baseEnd_3796603] using wordTrace_append hprefix tailTrace_3796603
  have hstable : (prefixWord ++ tailWord_3796603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796603).length < 2 ^ (prefixWord ++ tailWord_3796603).sum := by decide
  have hdescent : baseEnd_3796603 < baseStart_3796603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796654 : List Nat := [4, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_3796654 : Nat := 118140960795 + 3796654 * 2 ^ 59
def prefixEnd_3796654 : Nat := 4983230072969 + 3 ^ 40 * 3796654 * 2
def baseEnd_3796654 : Nat := 433224084625620846103225

theorem tailTrace_3796654 : CollatzResearch.WordTrace tailWord_3796654 prefixEnd_3796654 433224084625620846103225 := by
  unfold tailWord_3796654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17309418448422306215650627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92316898391585633150136677 17309418448422306215650627)
  ·
    refine ⟨25964127672633459323475941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17309418448422306215650627 25964127672633459323475941)
    ·
      refine ⟨4868273938618773623151739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25964127672633459323475941 4868273938618773623151739)
      ·
        refine ⟨7302410907928160434727609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4868273938618773623151739 7302410907928160434727609)
        ·
          refine ⟨5476808180946120326045707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7302410907928160434727609 5476808180946120326045707)
          ·
            refine ⟨8215212271419180489068561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5476808180946120326045707 8215212271419180489068561)
            ·
              refine ⟨6161409203564385366801421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8215212271419180489068561 6161409203564385366801421)
              ·
                refine ⟨2310528451336644512550533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6161409203564385366801421 2310528451336644512550533)
                ·
                  refine ⟨433224084625620846103225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2310528451336644512550533 433224084625620846103225)
                  ·
                    rfl

theorem cell22_3796654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_3796654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796654 prefixEnd_3796654 := by exact prefixLift 3796654
  have htrace : WordTrace (prefixWord ++ tailWord_3796654) baseStart_3796654 baseEnd_3796654 := by
    simpa [prefixWord, tailWord_3796654, baseEnd_3796654] using wordTrace_append hprefix tailTrace_3796654
  have hstable : (prefixWord ++ tailWord_3796654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796654).length < 2 ^ (prefixWord ++ tailWord_3796654).sum := by decide
  have hdescent : baseEnd_3796654 < baseStart_3796654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796680 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 3, 3]
def baseStart_3796680 : Nat := 118140960795 + 3796680 * 2 ^ 59
def prefixEnd_3796680 : Nat := 4983230072969 + 3 ^ 40 * 3796680 * 2
def baseEnd_3796680 : Nat := 1299681154208207137159595

theorem tailTrace_3796680 : CollatzResearch.WordTrace tailWord_3796680 prefixEnd_3796680 1299681154208207137159595 := by
  unfold tailWord_3796680
  simp only [CollatzResearch.WordTrace]
  refine ⟨69238147942642128082825747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92317530590189504110434329 69238147942642128082825747)
  ·
    refine ⟨103857221913963192124238621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69238147942642128082825747 103857221913963192124238621)
    ·
      refine ⟨38946458217736197046589483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103857221913963192124238621 38946458217736197046589483)
      ·
        refine ⟨58419687326604295569884225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38946458217736197046589483 58419687326604295569884225)
        ·
          refine ⟨43814765494953221677413169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58419687326604295569884225 43814765494953221677413169)
          ·
            refine ⟨32861074121214916258059877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43814765494953221677413169 32861074121214916258059877)
            ·
              refine ⟨6161451397727796798386227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32861074121214916258059877 6161451397727796798386227)
              ·
                refine ⟨9242177096591695197579341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6161451397727796798386227 9242177096591695197579341)
                ·
                  refine ⟨3465816411221885699092253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9242177096591695197579341 3465816411221885699092253)
                  ·
                    refine ⟨1299681154208207137159595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3465816411221885699092253 1299681154208207137159595)
                    ·
                      rfl

theorem cell22_3796680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_3796680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796680 prefixEnd_3796680 := by exact prefixLift 3796680
  have htrace : WordTrace (prefixWord ++ tailWord_3796680) baseStart_3796680 baseEnd_3796680 := by
    simpa [prefixWord, tailWord_3796680, baseEnd_3796680] using wordTrace_append hprefix tailTrace_3796680
  have hstable : (prefixWord ++ tailWord_3796680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796680).length < 2 ^ (prefixWord ++ tailWord_3796680).sum := by decide
  have hdescent : baseEnd_3796680 < baseStart_3796680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796691 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 5, 7]
def baseStart_3796691 : Nat := 118140960795 + 3796691 * 2 ^ 59
def prefixEnd_3796691 : Nat := 4983230072969 + 3 ^ 40 * 3796691 * 2
def baseEnd_3796691 : Nat := 1299684919733006775134561

theorem tailTrace_3796691 : CollatzResearch.WordTrace tailWord_3796691 prefixEnd_3796691 1299684919733006775134561 := by
  unfold tailWord_3796691
  simp only [CollatzResearch.WordTrace]
  refine ⟨138476697088244405044301927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92317798058829603362867951 138476697088244405044301927)
  ·
    refine ⟨207715045632366607566452891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138476697088244405044301927 207715045632366607566452891)
    ·
      refine ⟨311572568448549911349679337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207715045632366607566452891 311572568448549911349679337)
      ·
        refine ⟨233679426336412433512259503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311572568448549911349679337 233679426336412433512259503)
        ·
          refine ⟨350519139504618650268389255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233679426336412433512259503 350519139504618650268389255)
          ·
            refine ⟨525778709256927975402583883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350519139504618650268389255 525778709256927975402583883)
            ·
              refine ⟨788668063885391963103875825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525778709256927975402583883 788668063885391963103875825)
              ·
                refine ⟨591501047914043972327906869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 788668063885391963103875825 591501047914043972327906869)
                ·
                  refine ⟨55453223241941622405741269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 591501047914043972327906869 55453223241941622405741269)
                  ·
                    refine ⟨1299684919733006775134561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55453223241941622405741269 1299684919733006775134561)
                    ·
                      rfl

theorem cell22_3796691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_3796691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796691 prefixEnd_3796691 := by exact prefixLift 3796691
  have htrace : WordTrace (prefixWord ++ tailWord_3796691) baseStart_3796691 baseEnd_3796691 := by
    simpa [prefixWord, tailWord_3796691, baseEnd_3796691] using wordTrace_append hprefix tailTrace_3796691
  have hstable : (prefixWord ++ tailWord_3796691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796691).length < 2 ^ (prefixWord ++ tailWord_3796691).sum := by decide
  have hdescent : baseEnd_3796691 < baseStart_3796691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796753 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 1, 5]
def baseStart_3796753 : Nat := 118140960795 + 3796753 * 2 ^ 59
def prefixEnd_3796753 : Nat := 4983230072969 + 3 ^ 40 * 3796753 * 2
def baseEnd_3796753 : Nat := 1299706143600059280084371

theorem tailTrace_3796753 : CollatzResearch.WordTrace tailWord_3796753 prefixEnd_3796753 1299706143600059280084371 := by
  unfold tailWord_3796753
  simp only [CollatzResearch.WordTrace]
  refine ⟨138478958414019789633058913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92319305609346526422039275 138478958414019789633058913)
  ·
    refine ⟨103859218810514842224794185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138478958414019789633058913 103859218810514842224794185)
    ·
      refine ⟨77894414107886131668595639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103859218810514842224794185 77894414107886131668595639)
      ·
        refine ⟨116841621161829197502893459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77894414107886131668595639 116841621161829197502893459)
        ·
          refine ⟨175262431742743796254340189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116841621161829197502893459 175262431742743796254340189)
          ·
            refine ⟨65723411903528923595377571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175262431742743796254340189 65723411903528923595377571)
            ·
              refine ⟨98585117855293385393066357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65723411903528923595377571 98585117855293385393066357)
              ·
                refine ⟨9242354798933754880599971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98585117855293385393066357 9242354798933754880599971)
                ·
                  refine ⟨13863532198400632320899957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9242354798933754880599971 13863532198400632320899957)
                  ·
                    refine ⟨1299706143600059280084371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13863532198400632320899957 1299706143600059280084371)
                    ·
                      rfl

theorem cell22_3796753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_3796753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796753 prefixEnd_3796753 := by exact prefixLift 3796753
  have htrace : WordTrace (prefixWord ++ tailWord_3796753) baseStart_3796753 baseEnd_3796753 := by
    simpa [prefixWord, tailWord_3796753, baseEnd_3796753] using wordTrace_append hprefix tailTrace_3796753
  have hstable : (prefixWord ++ tailWord_3796753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796753).length < 2 ^ (prefixWord ++ tailWord_3796753).sum := by decide
  have hdescent : baseEnd_3796753 < baseStart_3796753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796757 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 1, 4]
def baseStart_3796757 : Nat := 118140960795 + 3796757 * 2 ^ 59
def prefixEnd_3796757 : Nat := 4983230072969 + 3 ^ 40 * 3796757 * 2
def baseEnd_3796757 : Nat := 1299707512881804602984359

theorem tailTrace_3796757 : CollatzResearch.WordTrace tailWord_3796757 prefixEnd_3796757 1299707512881804602984359 := by
  unfold tailWord_3796757
  simp only [CollatzResearch.WordTrace]
  refine ⟨138479104306005298316204525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92319402870670198877469683 138479104306005298316204525)
  ·
    refine ⟨51929664114751986868576697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138479104306005298316204525 51929664114751986868576697)
    ·
      refine ⟨38947248086063990151432523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51929664114751986868576697 38947248086063990151432523)
      ·
        refine ⟨58420872129095985227148785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38947248086063990151432523 58420872129095985227148785)
        ·
          refine ⟨43815654096821988920361589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58420872129095985227148785 43815654096821988920361589)
          ·
            refine ⟨4107717571577061461283899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43815654096821988920361589 4107717571577061461283899)
            ·
              refine ⟨6161576357365592191925849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4107717571577061461283899 6161576357365592191925849)
              ·
                refine ⟨4621182268024194143944387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6161576357365592191925849 4621182268024194143944387)
                ·
                  refine ⟨6931773402036291215916581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621182268024194143944387 6931773402036291215916581)
                  ·
                    refine ⟨1299707512881804602984359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6931773402036291215916581 1299707512881804602984359)
                    ·
                      rfl

theorem cell22_3796757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_3796757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796757 prefixEnd_3796757 := by exact prefixLift 3796757
  have htrace : WordTrace (prefixWord ++ tailWord_3796757) baseStart_3796757 baseEnd_3796757 := by
    simpa [prefixWord, tailWord_3796757, baseEnd_3796757] using wordTrace_append hprefix tailTrace_3796757
  have hstable : (prefixWord ++ tailWord_3796757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796757).length < 2 ^ (prefixWord ++ tailWord_3796757).sum := by decide
  have hdescent : baseEnd_3796757 < baseStart_3796757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796770 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_3796770 : Nat := 118140960795 + 3796770 * 2 ^ 59
def prefixEnd_3796770 : Nat := 4983230072969 + 3 ^ 40 * 3796770 * 2
def baseEnd_3796770 : Nat := 1299711963047476902409319

theorem tailTrace_3796770 : CollatzResearch.WordTrace tailWord_3796770 prefixEnd_3796770 1299711963047476902409319 := by
  unfold tailWord_3796770
  simp only [CollatzResearch.WordTrace]
  refine ⟨34619894613739550384106941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92319718969972134357618509 34619894613739550384106941)
  ·
    refine ⟨12982460480152331394040103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34619894613739550384106941 12982460480152331394040103)
    ·
      refine ⟨19473690720228497091060155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12982460480152331394040103 19473690720228497091060155)
      ·
        refine ⟨29210536080342745636590233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19473690720228497091060155 29210536080342745636590233)
        ·
          refine ⟨21907902060257059227442675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29210536080342745636590233 21907902060257059227442675)
          ·
            refine ⟨32861853090385588841164013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21907902060257059227442675 32861853090385588841164013)
            ·
              refine ⟨12323194908894595815436505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32861853090385588841164013 12323194908894595815436505)
              ·
                refine ⟨9242396181670946861577379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12323194908894595815436505 9242396181670946861577379)
                ·
                  refine ⟨13863594272506420292366069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9242396181670946861577379 13863594272506420292366069)
                  ·
                    refine ⟨1299711963047476902409319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13863594272506420292366069 1299711963047476902409319)
                    ·
                      rfl

theorem cell22_3796770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_3796770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796770 prefixEnd_3796770 := by exact prefixLift 3796770
  have htrace : WordTrace (prefixWord ++ tailWord_3796770) baseStart_3796770 baseEnd_3796770 := by
    simpa [prefixWord, tailWord_3796770, baseEnd_3796770] using wordTrace_append hprefix tailTrace_3796770
  have hstable : (prefixWord ++ tailWord_3796770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796770).length < 2 ^ (prefixWord ++ tailWord_3796770).sum := by decide
  have hdescent : baseEnd_3796770 < baseStart_3796770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796785 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 2, 4]
def baseStart_3796785 : Nat := 118140960795 + 3796785 * 2 ^ 59
def prefixEnd_3796785 : Nat := 4983230072969 + 3 ^ 40 * 3796785 * 2
def baseEnd_3796785 : Nat := 1299717097854021863284273

theorem tailTrace_3796785 : CollatzResearch.WordTrace tailWord_3796785 prefixEnd_3796785 1299717097854021863284273 := by
  unfold tailWord_3796785
  simp only [CollatzResearch.WordTrace]
  refine ⟨138480125549903859098223809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92320083699935906065482539 138480125549903859098223809)
  ·
    refine ⟨103860094162427894323667857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138480125549903859098223809 103860094162427894323667857)
    ·
      refine ⟨77895070621820920742750893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103860094162427894323667857 77895070621820920742750893)
      ·
        refine ⟨29210651483182845278531585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77895070621820920742750893 29210651483182845278531585)
        ·
          refine ⟨21907988612387133958898689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29210651483182845278531585 21907988612387133958898689)
          ·
            refine ⟨16430991459290350469174017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21907988612387133958898689 16430991459290350469174017)
            ·
              refine ⟨12323243594467762851880513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16430991459290350469174017 12323243594467762851880513)
              ·
                refine ⟨9242432695850822138910385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12323243594467762851880513 9242432695850822138910385)
                ·
                  refine ⟨6931824521888116604182789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9242432695850822138910385 6931824521888116604182789)
                  ·
                    refine ⟨1299717097854021863284273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6931824521888116604182789 1299717097854021863284273)
                    ·
                      rfl

theorem cell22_3796785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_3796785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796785 prefixEnd_3796785 := by exact prefixLift 3796785
  have htrace : WordTrace (prefixWord ++ tailWord_3796785) baseStart_3796785 baseEnd_3796785 := by
    simpa [prefixWord, tailWord_3796785, baseEnd_3796785] using wordTrace_append hprefix tailTrace_3796785
  have hstable : (prefixWord ++ tailWord_3796785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796785).length < 2 ^ (prefixWord ++ tailWord_3796785).sum := by decide
  have hdescent : baseEnd_3796785 < baseStart_3796785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3796920 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 4, 4]
def baseStart_3796920 : Nat := 118140960795 + 3796920 * 2 ^ 59
def prefixEnd_3796920 : Nat := 4983230072969 + 3 ^ 40 * 3796920 * 2
def baseEnd_3796920 : Nat := 1299763311112926511158859

theorem tailTrace_3796920 : CollatzResearch.WordTrace tailWord_3796920 prefixEnd_3796920 1299763311112926511158859 := by
  unfold tailWord_3796920
  simp only [CollatzResearch.WordTrace]
  refine ⟨69242524702207388577194107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92323366269609851436258809 69242524702207388577194107)
  ·
    refine ⟨103863787053311082865791161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69242524702207388577194107 103863787053311082865791161)
    ·
      refine ⟨77897840289983312149343371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103863787053311082865791161 77897840289983312149343371)
      ·
        refine ⟨116846760434974968224015057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77897840289983312149343371 116846760434974968224015057)
        ·
          refine ⟨87635070326231226168011293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116846760434974968224015057 87635070326231226168011293)
          ·
            refine ⟨32863151372336709813004235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87635070326231226168011293 32863151372336709813004235)
            ·
              refine ⟨49294727058505064719506353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32863151372336709813004235 49294727058505064719506353)
              ·
                refine ⟨36971045293878798539629765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49294727058505064719506353 36971045293878798539629765)
                ·
                  refine ⟨6932070992602274726180581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36971045293878798539629765 6932070992602274726180581)
                  ·
                    refine ⟨1299763311112926511158859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6932070992602274726180581 1299763311112926511158859)
                    ·
                      rfl

theorem cell22_3796920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_3796920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3796920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3796920 prefixEnd_3796920 := by exact prefixLift 3796920
  have htrace : WordTrace (prefixWord ++ tailWord_3796920) baseStart_3796920 baseEnd_3796920 := by
    simpa [prefixWord, tailWord_3796920, baseEnd_3796920] using wordTrace_append hprefix tailTrace_3796920
  have hstable : (prefixWord ++ tailWord_3796920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3796920).length < 2 ^ (prefixWord ++ tailWord_3796920).sum := by decide
  have hdescent : baseEnd_3796920 < baseStart_3796920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3796920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797042 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_3797042 : Nat := 118140960795 + 3797042 * 2 ^ 59
def prefixEnd_3797042 : Nat := 4983230072969 + 3 ^ 40 * 3797042 * 2
def baseEnd_3797042 : Nat := 433268358068719619869495

theorem tailTrace_3797042 : CollatzResearch.WordTrace tailWord_3797042 prefixEnd_3797042 433268358068719619869495 := by
  unfold tailWord_3797042
  simp only [CollatzResearch.WordTrace]
  refine ⟨34622374777493197997582345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92326332739981861326886253 34622374777493197997582345)
  ·
    refine ⟨25966781083119898498186759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34622374777493197997582345 25966781083119898498186759)
    ·
      refine ⟨38950171624679847747280139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25966781083119898498186759 38950171624679847747280139)
      ·
        refine ⟨58425257437019771620920209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38950171624679847747280139 58425257437019771620920209)
        ·
          refine ⟨43818943077764828715690157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58425257437019771620920209 43818943077764828715690157)
          ·
            refine ⟨16432103654161810768383809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43818943077764828715690157 16432103654161810768383809)
            ·
              refine ⟨12324077740621358076287857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16432103654161810768383809 12324077740621358076287857)
              ·
                refine ⟨9243058305466018557215893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12324077740621358076287857 9243058305466018557215893)
                ·
                  refine ⟨433268358068719619869495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9243058305466018557215893 433268358068719619869495)
                  ·
                    rfl

theorem cell22_3797042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_3797042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797042 prefixEnd_3797042 := by exact prefixLift 3797042
  have htrace : WordTrace (prefixWord ++ tailWord_3797042) baseStart_3797042 baseEnd_3797042 := by
    simpa [prefixWord, tailWord_3797042, baseEnd_3797042] using wordTrace_append hprefix tailTrace_3797042
  have hstable : (prefixWord ++ tailWord_3797042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797042).length < 2 ^ (prefixWord ++ tailWord_3797042).sum := by decide
  have hdescent : baseEnd_3797042 < baseStart_3797042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797091 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 2, 3]
def baseStart_3797091 : Nat := 118140960795 + 3797091 * 2 ^ 59
def prefixEnd_3797091 : Nat := 4983230072969 + 3 ^ 40 * 3797091 * 2
def baseEnd_3797091 : Nat := 1299821847907539065133335

theorem tailTrace_3797091 : CollatzResearch.WordTrace tailWord_3797091 prefixEnd_3797091 1299821847907539065133335 := by
  unfold tailWord_3797091
  simp only [CollatzResearch.WordTrace]
  refine ⟨138491286286795273358863127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92327524191196848905908751 138491286286795273358863127)
  ·
    refine ⟨207736929430192910038294691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138491286286795273358863127 207736929430192910038294691)
    ·
      refine ⟨311605394145289365057442037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207736929430192910038294691 311605394145289365057442037)
      ·
        refine ⟨29213005701120877974135191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311605394145289365057442037 29213005701120877974135191)
        ·
          refine ⟨43819508551681316961202787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29213005701120877974135191 43819508551681316961202787)
          ·
            refine ⟨65729262827521975441804181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43819508551681316961202787 65729262827521975441804181)
            ·
              refine ⟨3081059195040092598834571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65729262827521975441804181 3081059195040092598834571)
              ·
                refine ⟨4621588792560138898251857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081059195040092598834571 4621588792560138898251857)
                ·
                  refine ⟨3466191594420104173688893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4621588792560138898251857 3466191594420104173688893)
                  ·
                    refine ⟨1299821847907539065133335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3466191594420104173688893 1299821847907539065133335)
                    ·
                      rfl

theorem cell22_3797091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 2, 3].length) (baseStart_3797091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797091 prefixEnd_3797091 := by exact prefixLift 3797091
  have htrace : WordTrace (prefixWord ++ tailWord_3797091) baseStart_3797091 baseEnd_3797091 := by
    simpa [prefixWord, tailWord_3797091, baseEnd_3797091] using wordTrace_append hprefix tailTrace_3797091
  have hstable : (prefixWord ++ tailWord_3797091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797091).length < 2 ^ (prefixWord ++ tailWord_3797091).sum := by decide
  have hdescent : baseEnd_3797091 < baseStart_3797091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797136 : List Nat := [2, 1, 1, 1, 1, 1, 7, 4, 1, 3]
def baseStart_3797136 : Nat := 118140960795 + 3797136 * 2 ^ 59
def prefixEnd_3797136 : Nat := 4983230072969 + 3 ^ 40 * 3797136 * 2
def baseEnd_3797136 : Nat := 1299837252327173947758197

theorem tailTrace_3797136 : CollatzResearch.WordTrace tailWord_3797136 prefixEnd_3797136 1299837252327173947758197 := by
  unfold tailWord_3797136
  simp only [CollatzResearch.WordTrace]
  refine ⟨69246463785816123022125631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92328618381088164029500841 69246463785816123022125631)
  ·
    refine ⟨103869695678724184533188447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69246463785816123022125631 103869695678724184533188447)
    ·
      refine ⟨155804543518086276799782671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103869695678724184533188447 155804543518086276799782671)
      ·
        refine ⟨233706815277129415199674007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155804543518086276799782671 233706815277129415199674007)
        ·
          refine ⟨350560222915694122799511011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233706815277129415199674007 350560222915694122799511011)
          ·
            refine ⟨525840334373541184199266517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350560222915694122799511011 525840334373541184199266517)
            ·
              refine ⟨12324382836879871504670309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 525840334373541184199266517 12324382836879871504670309)
              ·
                refine ⟨2310821781914975907125683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12324382836879871504670309 2310821781914975907125683)
                ·
                  refine ⟨3466232672872463860688525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310821781914975907125683 3466232672872463860688525)
                  ·
                    refine ⟨1299837252327173947758197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3466232672872463860688525 1299837252327173947758197)
                    ·
                      rfl

theorem cell22_3797136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 1, 3].length) (baseStart_3797136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797136 prefixEnd_3797136 := by exact prefixLift 3797136
  have htrace : WordTrace (prefixWord ++ tailWord_3797136) baseStart_3797136 baseEnd_3797136 := by
    simpa [prefixWord, tailWord_3797136, baseEnd_3797136] using wordTrace_append hprefix tailTrace_3797136
  have hstable : (prefixWord ++ tailWord_3797136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797136).length < 2 ^ (prefixWord ++ tailWord_3797136).sum := by decide
  have hdescent : baseEnd_3797136 < baseStart_3797136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797142 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3797142 : Nat := 118140960795 + 3797142 * 2 ^ 59
def prefixEnd_3797142 : Nat := 4983230072969 + 3 ^ 40 * 3797142 * 2
def baseEnd_3797142 : Nat := 1299839306249791932108179

theorem tailTrace_3797142 : CollatzResearch.WordTrace tailWord_3797142 prefixEnd_3797142 1299839306249791932108179 := by
  unfold tailWord_3797142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655821650600656816810605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92328764273073672712646453 8655821650600656816810605)
  ·
    refine ⟨3245933118975246306303977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8655821650600656816810605 3245933118975246306303977)
    ·
      refine ⟨2434449839231434729727983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3245933118975246306303977 2434449839231434729727983)
      ·
        refine ⟨3651674758847152094591975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2434449839231434729727983 3651674758847152094591975)
        ·
          refine ⟨5477512138270728141887963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3651674758847152094591975 5477512138270728141887963)
          ·
            refine ⟨8216268207406092212831945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5477512138270728141887963 8216268207406092212831945)
            ·
              refine ⟨6162201155554569159623959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8216268207406092212831945 6162201155554569159623959)
              ·
                refine ⟨9243301733331853739435939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6162201155554569159623959 9243301733331853739435939)
                ·
                  refine ⟨13864952599997780609153909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9243301733331853739435939 13864952599997780609153909)
                  ·
                    refine ⟨1299839306249791932108179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13864952599997780609153909 1299839306249791932108179)
                    ·
                      rfl

theorem cell22_3797142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3797142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797142 prefixEnd_3797142 := by exact prefixLift 3797142
  have htrace : WordTrace (prefixWord ++ tailWord_3797142) baseStart_3797142 baseEnd_3797142 := by
    simpa [prefixWord, tailWord_3797142, baseEnd_3797142] using wordTrace_append hprefix tailTrace_3797142
  have hstable : (prefixWord ++ tailWord_3797142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797142).length < 2 ^ (prefixWord ++ tailWord_3797142).sum := by decide
  have hdescent : baseEnd_3797142 < baseStart_3797142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797149 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 5]
def baseStart_3797149 : Nat := 118140960795 + 3797149 * 2 ^ 59
def prefixEnd_3797149 : Nat := 4983230072969 + 3 ^ 40 * 3797149 * 2
def baseEnd_3797149 : Nat := 433280567497615415727719

theorem tailTrace_3797149 : CollatzResearch.WordTrace tailWord_3797149 prefixEnd_3797149 433280567497615415727719 := by
  unfold tailWord_3797149
  simp only [CollatzResearch.WordTrace]
  refine ⟨138493401720585149264474501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92328934480390099509649667 138493401720585149264474501)
  ·
    refine ⟨25967512822609715487088969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138493401720585149264474501 25967512822609715487088969)
    ·
      refine ⟨19475634616957286615316727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25967512822609715487088969 19475634616957286615316727)
      ·
        refine ⟨29213451925435929922975091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19475634616957286615316727 29213451925435929922975091)
        ·
          refine ⟨43820177888153894884462637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29213451925435929922975091 43820177888153894884462637)
          ·
            refine ⟨16432566708057710581673489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43820177888153894884462637 16432566708057710581673489)
            ·
              refine ⟨12324425031043282936255117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16432566708057710581673489 12324425031043282936255117)
              ·
                refine ⟨4621659386641231101095669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12324425031043282936255117 4621659386641231101095669)
                ·
                  refine ⟨433280567497615415727719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4621659386641231101095669 433280567497615415727719)
                  ·
                    rfl

theorem cell22_3797149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_3797149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797149 prefixEnd_3797149 := by exact prefixLift 3797149
  have htrace : WordTrace (prefixWord ++ tailWord_3797149) baseStart_3797149 baseEnd_3797149 := by
    simpa [prefixWord, tailWord_3797149, baseEnd_3797149] using wordTrace_append hprefix tailTrace_3797149
  have hstable : (prefixWord ++ tailWord_3797149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797149).length < 2 ^ (prefixWord ++ tailWord_3797149).sum := by decide
  have hdescent : baseEnd_3797149 < baseStart_3797149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797177 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 8]
def baseStart_3797177 : Nat := 118140960795 + 3797177 * 2 ^ 59
def prefixEnd_3797177 : Nat := 4983230072969 + 3 ^ 40 * 3797177 * 2
def baseEnd_3797177 : Nat := 433283762488354502494357

theorem tailTrace_3797177 : CollatzResearch.WordTrace tailWord_3797177 prefixEnd_3797177 433283762488354502494357 := by
  unfold tailWord_3797177
  simp only [CollatzResearch.WordTrace]
  refine ⟨138494422964483710046493785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92329615309655806697662523 138494422964483710046493785)
  ·
    refine ⟨103870817223362782534870339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138494422964483710046493785 103870817223362782534870339)
    ·
      refine ⟨155806225835044173802305509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103870817223362782534870339 155806225835044173802305509)
      ·
        refine ⟨29213667344070782587932283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155806225835044173802305509 29213667344070782587932283)
        ·
          refine ⟨43820501016106173881898425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29213667344070782587932283 43820501016106173881898425)
          ·
            refine ⟨32865375762079630411423819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43820501016106173881898425 32865375762079630411423819)
            ·
              refine ⟨49298063643119445617135729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32865375762079630411423819 49298063643119445617135729)
              ·
                refine ⟨36973547732339584212851797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49298063643119445617135729 36973547732339584212851797)
                ·
                  refine ⟨433283762488354502494357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36973547732339584212851797 433283762488354502494357)
                  ·
                    rfl

theorem cell22_3797177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_3797177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797177 prefixEnd_3797177 := by exact prefixLift 3797177
  have htrace : WordTrace (prefixWord ++ tailWord_3797177) baseStart_3797177 baseEnd_3797177 := by
    simpa [prefixWord, tailWord_3797177, baseEnd_3797177] using wordTrace_append hprefix tailTrace_3797177
  have hstable : (prefixWord ++ tailWord_3797177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797177).length < 2 ^ (prefixWord ++ tailWord_3797177).sum := by decide
  have hdescent : baseEnd_3797177 < baseStart_3797177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797179 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 1, 4]
def baseStart_3797179 : Nat := 118140960795 + 3797179 * 2 ^ 59
def prefixEnd_3797179 : Nat := 4983230072969 + 3 ^ 40 * 3797179 * 2
def baseEnd_3797179 : Nat := 1299851972105936168933065

theorem tailTrace_3797179 : CollatzResearch.WordTrace tailWord_3797179 prefixEnd_3797179 1299851972105936168933065 := by
  unfold tailWord_3797179
  simp only [CollatzResearch.WordTrace]
  refine ⟨138494495910476464388066591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92329663940317642925377727 138494495910476464388066591)
  ·
    refine ⟨207741743865714696582099887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138494495910476464388066591 207741743865714696582099887)
    ·
      refine ⟨311612615798572044873149831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207741743865714696582099887 311612615798572044873149831)
      ·
        refine ⟨467418923697858067309724747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311612615798572044873149831 467418923697858067309724747)
        ·
          refine ⟨701128385546787100964587121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467418923697858067309724747 701128385546787100964587121)
          ·
            refine ⟨525846289160090325723440341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701128385546787100964587121 525846289160090325723440341)
            ·
              refine ⟨12324522402189617009143133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 525846289160090325723440341 12324522402189617009143133)
              ·
                refine ⟨4621695900821106378428675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12324522402189617009143133 4621695900821106378428675)
                ·
                  refine ⟨6932543851231659567643013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621695900821106378428675 6932543851231659567643013)
                  ·
                    refine ⟨1299851972105936168933065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6932543851231659567643013 1299851972105936168933065)
                    ·
                      rfl

theorem cell22_3797179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 4].length) (baseStart_3797179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797179 prefixEnd_3797179 := by exact prefixLift 3797179
  have htrace : WordTrace (prefixWord ++ tailWord_3797179) baseStart_3797179 baseEnd_3797179 := by
    simpa [prefixWord, tailWord_3797179, baseEnd_3797179] using wordTrace_append hprefix tailTrace_3797179
  have hstable : (prefixWord ++ tailWord_3797179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797179).length < 2 ^ (prefixWord ++ tailWord_3797179).sum := by decide
  have hdescent : baseEnd_3797179 < baseStart_3797179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797194 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_3797194 : Nat := 118140960795 + 3797194 * 2 ^ 59
def prefixEnd_3797194 : Nat := 4983230072969 + 3 ^ 40 * 3797194 * 2
def baseEnd_3797194 : Nat := 433285702304160376602673

theorem tailTrace_3797194 : CollatzResearch.WordTrace tailWord_3797194 prefixEnd_3797194 433285702304160376602673 := by
  unfold tailWord_3797194
  simp only [CollatzResearch.WordTrace]
  refine ⟨34623760751355530487465659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92330028670281414633241757 34623760751355530487465659)
  ·
    refine ⟨51935641127033295731198489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34623760751355530487465659 51935641127033295731198489)
    ·
      refine ⟨38951730845274971798398867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51935641127033295731198489 38951730845274971798398867)
      ·
        refine ⟨58427596267912457697598301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38951730845274971798398867 58427596267912457697598301)
        ·
          refine ⟨21910348600467171636599363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58427596267912457697598301 21910348600467171636599363)
          ·
            refine ⟨32865522900700757454899045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21910348600467171636599363 32865522900700757454899045)
            ·
              refine ⟨6162285543881392022793571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32865522900700757454899045 6162285543881392022793571)
              ·
                refine ⟨9243428315822088034190357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6162285543881392022793571 9243428315822088034190357)
                ·
                  refine ⟨433285702304160376602673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9243428315822088034190357 433285702304160376602673)
                  ·
                    rfl

theorem cell22_3797194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_3797194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797194 prefixEnd_3797194 := by exact prefixLift 3797194
  have htrace : WordTrace (prefixWord ++ tailWord_3797194) baseStart_3797194 baseEnd_3797194 := by
    simpa [prefixWord, tailWord_3797194, baseEnd_3797194] using wordTrace_append hprefix tailTrace_3797194
  have hstable : (prefixWord ++ tailWord_3797194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797194).length < 2 ^ (prefixWord ++ tailWord_3797194).sum := by decide
  have hdescent : baseEnd_3797194 < baseStart_3797194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797209 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 1, 5]
def baseStart_3797209 : Nat := 118140960795 + 3797209 * 2 ^ 59
def prefixEnd_3797209 : Nat := 4983230072969 + 3 ^ 40 * 3797209 * 2
def baseEnd_3797209 : Nat := 1299862241719026090682973

theorem tailTrace_3797209 : CollatzResearch.WordTrace tailWord_3797209 prefixEnd_3797209 1299862241719026090682973 := by
  unfold tailWord_3797209
  simp only [CollatzResearch.WordTrace]
  refine ⟨138495590100367779511658681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92330393400245186341105787 138495590100367779511658681)
  ·
    refine ⟨103871692575275834633744011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138495590100367779511658681 103871692575275834633744011)
    ·
      refine ⟨155807538862913751950616017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103871692575275834633744011 155807538862913751950616017)
      ·
        refine ⟨116855654147185313962962013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155807538862913751950616017 116855654147185313962962013)
        ·
          refine ⟨43820870305194492736110755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116855654147185313962962013 43820870305194492736110755)
          ·
            refine ⟨65731305457791739104166133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43820870305194492736110755 65731305457791739104166133)
            ·
              refine ⟨6162309886667975541015575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65731305457791739104166133 6162309886667975541015575)
              ·
                refine ⟨9243464830001963311523363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6162309886667975541015575 9243464830001963311523363)
                ·
                  refine ⟨13865197245002944967285045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9243464830001963311523363 13865197245002944967285045)
                  ·
                    refine ⟨1299862241719026090682973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13865197245002944967285045 1299862241719026090682973)
                    ·
                      rfl

theorem cell22_3797209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_3797209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797209 prefixEnd_3797209 := by exact prefixLift 3797209
  have htrace : WordTrace (prefixWord ++ tailWord_3797209) baseStart_3797209 baseEnd_3797209 := by
    simpa [prefixWord, tailWord_3797209, baseEnd_3797209] using wordTrace_append hprefix tailTrace_3797209
  have hstable : (prefixWord ++ tailWord_3797209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797209).length < 2 ^ (prefixWord ++ tailWord_3797209).sum := by decide
  have hdescent : baseEnd_3797209 < baseStart_3797209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797213 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3797213 : Nat := 118140960795 + 3797213 * 2 ^ 59
def prefixEnd_3797213 : Nat := 4983230072969 + 3 ^ 40 * 3797213 * 2
def baseEnd_3797213 : Nat := 1299863611000771413582961

theorem tailTrace_3797213 : CollatzResearch.WordTrace tailWord_3797213 prefixEnd_3797213 1299863611000771413582961 := by
  unfold tailWord_3797213
  simp only [CollatzResearch.WordTrace]
  refine ⟨138495735992353288194804293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92330490661568858796536195 138495735992353288194804293)
  ·
    refine ⟨25967950498566241536525805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138495735992353288194804293 25967950498566241536525805)
    ·
      refine ⟨9737981436962340576197177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25967950498566241536525805 9737981436962340576197177)
      ·
        refine ⟨7303486077721755432147883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9737981436962340576197177 7303486077721755432147883)
        ·
          refine ⟨10955229116582633148221825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7303486077721755432147883 10955229116582633148221825)
          ·
            refine ⟨8216421837436974861166369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10955229116582633148221825 8216421837436974861166369)
            ·
              refine ⟨6162316378077731145874777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8216421837436974861166369 6162316378077731145874777)
              ·
                refine ⟨4621737283558298359406083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6162316378077731145874777 4621737283558298359406083)
                ·
                  refine ⟨6932605925337447539109125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4621737283558298359406083 6932605925337447539109125)
                  ·
                    refine ⟨1299863611000771413582961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6932605925337447539109125 1299863611000771413582961)
                    ·
                      rfl

theorem cell22_3797213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3797213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797213 prefixEnd_3797213 := by exact prefixLift 3797213
  have htrace : WordTrace (prefixWord ++ tailWord_3797213) baseStart_3797213 baseEnd_3797213 := by
    simpa [prefixWord, tailWord_3797213, baseEnd_3797213] using wordTrace_append hprefix tailTrace_3797213
  have hstable : (prefixWord ++ tailWord_3797213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797213).length < 2 ^ (prefixWord ++ tailWord_3797213).sum := by decide
  have hdescent : baseEnd_3797213 < baseStart_3797213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797224 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3797224 : Nat := 118140960795 + 3797224 * 2 ^ 59
def prefixEnd_3797224 : Nat := 4983230072969 + 3 ^ 40 * 3797224 * 2
def baseEnd_3797224 : Nat := 1299867376525571051557927

theorem tailTrace_3797224 : CollatzResearch.WordTrace tailWord_3797224 prefixEnd_3797224 1299867376525571051557927 := by
  unfold tailWord_3797224
  simp only [CollatzResearch.WordTrace]
  refine ⟨69248068597656718536727363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92330758130208958048969817 69248068597656718536727363)
  ·
    refine ⟨103872102896485077805091045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69248068597656718536727363 103872102896485077805091045)
    ·
      refine ⟨19476019293090952088454571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103872102896485077805091045 19476019293090952088454571)
      ·
        refine ⟨29214028939636428132681857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19476019293090952088454571 29214028939636428132681857)
        ·
          refine ⟨21910521704727321099511393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29214028939636428132681857 21910521704727321099511393)
          ·
            refine ⟨16432891278545490824633545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21910521704727321099511393 16432891278545490824633545)
            ·
              refine ⟨12324668458909118118475159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16432891278545490824633545 12324668458909118118475159)
              ·
                refine ⟨18487002688363677177712739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12324668458909118118475159 18487002688363677177712739)
                ·
                  refine ⟨27730504032545515766569109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18487002688363677177712739 27730504032545515766569109)
                  ·
                    refine ⟨1299867376525571051557927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27730504032545515766569109 1299867376525571051557927)
                    ·
                      rfl

theorem cell22_3797224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3797224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797224 prefixEnd_3797224 := by exact prefixLift 3797224
  have htrace : WordTrace (prefixWord ++ tailWord_3797224) baseStart_3797224 baseEnd_3797224 := by
    simpa [prefixWord, tailWord_3797224, baseEnd_3797224] using wordTrace_append hprefix tailTrace_3797224
  have hstable : (prefixWord ++ tailWord_3797224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797224).length < 2 ^ (prefixWord ++ tailWord_3797224).sum := by decide
  have hdescent : baseEnd_3797224 < baseStart_3797224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797299 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 2, 5]
def baseStart_3797299 : Nat := 118140960795 + 3797299 * 2 ^ 59
def prefixEnd_3797299 : Nat := 4983230072969 + 3 ^ 40 * 3797299 * 2
def baseEnd_3797299 : Nat := 1299893050558295855932697

theorem tailTrace_3797299 : CollatzResearch.WordTrace tailWord_3797299 prefixEnd_3797299 1299893050558295855932697 := by
  unfold tailWord_3797299
  simp only [CollatzResearch.WordTrace]
  refine ⟨138498872670041724882434951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92332581780027816588289967 138498872670041724882434951)
  ·
    refine ⟨207748309005062587323652427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138498872670041724882434951 207748309005062587323652427)
    ·
      refine ⟨311622463507593880985478641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207748309005062587323652427 311622463507593880985478641)
      ·
        refine ⟨233716847630695410739108981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311622463507593880985478641 233716847630695410739108981)
        ·
          refine ⟨21910954465377694756791467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233716847630695410739108981 21910954465377694756791467)
          ·
            refine ⟨32866431698066542135187201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21910954465377694756791467 32866431698066542135187201)
            ·
              refine ⟨24649823773549906601390401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32866431698066542135187201 24649823773549906601390401)
              ·
                refine ⟨18487367830162429951042801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24649823773549906601390401 18487367830162429951042801)
                ·
                  refine ⟨13865525872621822463282101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18487367830162429951042801 13865525872621822463282101)
                  ·
                    refine ⟨1299893050558295855932697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13865525872621822463282101 1299893050558295855932697)
                    ·
                      rfl

theorem cell22_3797299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_3797299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797299 prefixEnd_3797299 := by exact prefixLift 3797299
  have htrace : WordTrace (prefixWord ++ tailWord_3797299) baseStart_3797299 baseEnd_3797299 := by
    simpa [prefixWord, tailWord_3797299, baseEnd_3797299] using wordTrace_append hprefix tailTrace_3797299
  have hstable : (prefixWord ++ tailWord_3797299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797299).length < 2 ^ (prefixWord ++ tailWord_3797299).sum := by decide
  have hdescent : baseEnd_3797299 < baseStart_3797299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797301 : List Nat := [1, 3, 3, 1, 2, 1, 4, 2, 5]
def baseStart_3797301 : Nat := 118140960795 + 3797301 * 2 ^ 59
def prefixEnd_3797301 : Nat := 4983230072969 + 3 ^ 40 * 3797301 * 2
def baseEnd_3797301 : Nat := 433297911733056172460897

theorem tailTrace_3797301 : CollatzResearch.WordTrace tailWord_3797301 prefixEnd_3797301 433297911733056172460897 := by
  unfold tailWord_3797301
  simp only [CollatzResearch.WordTrace]
  refine ⟨138498945616034479224007757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92332630410689652816005171 138498945616034479224007757)
  ·
    refine ⟨51937104606012929709002909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138498945616034479224007757 51937104606012929709002909)
    ·
      refine ⟨19476414227254848640876091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51937104606012929709002909 19476414227254848640876091)
      ·
        refine ⟨29214621340882272961314137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19476414227254848640876091 29214621340882272961314137)
        ·
          refine ⟨21910966005661704720985603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29214621340882272961314137 21910966005661704720985603)
          ·
            refine ⟨32866449008492557081478405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21910966005661704720985603 32866449008492557081478405)
            ·
              refine ⟨6162459189092354452777201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32866449008492557081478405 6162459189092354452777201)
              ·
                refine ⟨4621844391819265839582901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6162459189092354452777201 4621844391819265839582901)
                ·
                  refine ⟨433297911733056172460897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4621844391819265839582901 433297911733056172460897)
                  ·
                    rfl

theorem cell22_3797301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_3797301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797301 prefixEnd_3797301 := by exact prefixLift 3797301
  have htrace : WordTrace (prefixWord ++ tailWord_3797301) baseStart_3797301 baseEnd_3797301 := by
    simpa [prefixWord, tailWord_3797301, baseEnd_3797301] using wordTrace_append hprefix tailTrace_3797301
  have hstable : (prefixWord ++ tailWord_3797301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797301).length < 2 ^ (prefixWord ++ tailWord_3797301).sum := by decide
  have hdescent : baseEnd_3797301 < baseStart_3797301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797305 : List Nat := [1, 2, 1, 6, 1, 2, 1, 4, 1, 3]
def baseStart_3797305 : Nat := 118140960795 + 3797305 * 2 ^ 59
def prefixEnd_3797305 : Nat := 4983230072969 + 3 ^ 40 * 3797305 * 2
def baseEnd_3797305 : Nat := 1299895104480913840282679

theorem tailTrace_3797305 : CollatzResearch.WordTrace tailWord_3797305 prefixEnd_3797305 1299895104480913840282679 := by
  unfold tailWord_3797305
  simp only [CollatzResearch.WordTrace]
  refine ⟨138499091508019987907153369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92332727672013325271435579 138499091508019987907153369)
  ·
    refine ⟨103874318631014990930365027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138499091508019987907153369 103874318631014990930365027)
    ·
      refine ⟨155811477946522486395547541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103874318631014990930365027 155811477946522486395547541)
      ·
        refine ⟨7303663028743241549791291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155811477946522486395547541 7303663028743241549791291)
        ·
          refine ⟨10955494543114862324686937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7303663028743241549791291 10955494543114862324686937)
          ·
            refine ⟨8216620907336146743515203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10955494543114862324686937 8216620907336146743515203)
            ·
              refine ⟨12324931361004220115272805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8216620907336146743515203 12324931361004220115272805)
              ·
                refine ⟨2310924630188291271613651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12324931361004220115272805 2310924630188291271613651)
                ·
                  refine ⟨3466386945282436907420477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2310924630188291271613651 3466386945282436907420477)
                  ·
                    refine ⟨1299895104480913840282679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3466386945282436907420477 1299895104480913840282679)
                    ·
                      rfl

theorem cell22_3797305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 1, 3].length) (baseStart_3797305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797305 prefixEnd_3797305 := by exact prefixLift 3797305
  have htrace : WordTrace (prefixWord ++ tailWord_3797305) baseStart_3797305 baseEnd_3797305 := by
    simpa [prefixWord, tailWord_3797305, baseEnd_3797305] using wordTrace_append hprefix tailTrace_3797305
  have hstable : (prefixWord ++ tailWord_3797305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797305).length < 2 ^ (prefixWord ++ tailWord_3797305).sum := by decide
  have hdescent : baseEnd_3797305 < baseStart_3797305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797329 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 8]
def baseStart_3797329 : Nat := 118140960795 + 3797329 * 2 ^ 59
def prefixEnd_3797329 : Nat := 4983230072969 + 3 ^ 40 * 3797329 * 2
def baseEnd_3797329 : Nat := 433301106723795259227535

theorem tailTrace_3797329 : CollatzResearch.WordTrace tailWord_3797329 prefixEnd_3797329 433301106723795259227535 := by
  unfold tailWord_3797329
  simp only [CollatzResearch.WordTrace]
  refine ⟨138499966859933040006027041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92333311239955360004018027 138499966859933040006027041)
  ·
    refine ⟨103874975144949780004520281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138499966859933040006027041 103874975144949780004520281)
    ·
      refine ⟨77906231358712335003390211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103874975144949780004520281 77906231358712335003390211)
      ·
        refine ⟨116859347038068502505085317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77906231358712335003390211 116859347038068502505085317)
        ·
          refine ⟨21911127569637844219703497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116859347038068502505085317 21911127569637844219703497)
          ·
            refine ⟨16433345677228383164777623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21911127569637844219703497 16433345677228383164777623)
            ·
              refine ⟨24650018515842574747166435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16433345677228383164777623 24650018515842574747166435)
              ·
                refine ⟨36975027773763862120749653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24650018515842574747166435 36975027773763862120749653)
                ·
                  refine ⟨433301106723795259227535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36975027773763862120749653 433301106723795259227535)
                  ·
                    rfl

theorem cell22_3797329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_3797329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797329 prefixEnd_3797329 := by exact prefixLift 3797329
  have htrace : WordTrace (prefixWord ++ tailWord_3797329) baseStart_3797329 baseEnd_3797329 := by
    simpa [prefixWord, tailWord_3797329, baseEnd_3797329] using wordTrace_append hprefix tailTrace_3797329
  have hstable : (prefixWord ++ tailWord_3797329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797329).length < 2 ^ (prefixWord ++ tailWord_3797329).sum := by decide
  have hdescent : baseEnd_3797329 < baseStart_3797329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797429 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 2, 3]
def baseStart_3797429 : Nat := 118140960795 + 3797429 * 2 ^ 59
def prefixEnd_3797429 : Nat := 4983230072969 + 3 ^ 40 * 3797429 * 2
def baseEnd_3797429 : Nat := 1299937552215018850182299

theorem tailTrace_3797429 : CollatzResearch.WordTrace tailWord_3797429 prefixEnd_3797429 1299937552215018850182299 := by
  unfold tailWord_3797429
  simp only [CollatzResearch.WordTrace]
  refine ⟨138503614159570757084667341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92335742773047171389778227 138503614159570757084667341)
  ·
    refine ⟨51938855309839033906750253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138503614159570757084667341 51938855309839033906750253)
    ·
      refine ⟨19477070741189637715031345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51938855309839033906750253 19477070741189637715031345)
      ·
        refine ⟨14607803055892228286273509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19477070741189637715031345 14607803055892228286273509)
        ·
          refine ⟨2738963072979792803676283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14607803055892228286273509 2738963072979792803676283)
          ·
            refine ⟨4108444609469689205514425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738963072979792803676283 4108444609469689205514425)
            ·
              refine ⟨3081333457102266904135819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4108444609469689205514425 3081333457102266904135819)
              ·
                refine ⟨4622000185653400356203729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081333457102266904135819 4622000185653400356203729)
                ·
                  refine ⟨3466500139240050267152797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4622000185653400356203729 3466500139240050267152797)
                  ·
                    refine ⟨1299937552215018850182299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3466500139240050267152797 1299937552215018850182299)
                    ·
                      rfl

theorem cell22_3797429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_3797429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797429 prefixEnd_3797429 := by exact prefixLift 3797429
  have htrace : WordTrace (prefixWord ++ tailWord_3797429) baseStart_3797429 baseEnd_3797429 := by
    simpa [prefixWord, tailWord_3797429, baseEnd_3797429] using wordTrace_append hprefix tailTrace_3797429
  have hstable : (prefixWord ++ tailWord_3797429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797429).length < 2 ^ (prefixWord ++ tailWord_3797429).sum := by decide
  have hdescent : baseEnd_3797429 < baseStart_3797429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797515 : List Nat := [1, 1, 1, 1, 7, 2, 2, 3, 4]
def baseStart_3797515 : Nat := 118140960795 + 3797515 * 2 ^ 59
def prefixEnd_3797515 : Nat := 4983230072969 + 3 ^ 40 * 3797515 * 2
def baseEnd_3797515 : Nat := 433322330590847764177345

theorem tailTrace_3797515 : CollatzResearch.WordTrace tailWord_3797515 prefixEnd_3797515 433322330590847764177345 := by
  unfold tailWord_3797515
  simp only [CollatzResearch.WordTrace]
  refine ⟨138506750837259193772297999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92337833891506129181531999 138506750837259193772297999)
  ·
    refine ⟨207760126255888790658446999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138506750837259193772297999 207760126255888790658446999)
    ·
      refine ⟨311640189383833185987670499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207760126255888790658446999 311640189383833185987670499)
      ·
        refine ⟨467460284075749778981505749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311640189383833185987670499 467460284075749778981505749)
        ·
          refine ⟨10956100408025385444879041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 467460284075749778981505749 10956100408025385444879041)
          ·
            refine ⟨8217075306019039083659281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10956100408025385444879041 8217075306019039083659281)
            ·
              refine ⟨6162806479514279312744461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8217075306019039083659281 6162806479514279312744461)
              ·
                refine ⟨2311052429817854742279173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6162806479514279312744461 2311052429817854742279173)
                ·
                  refine ⟨433322330590847764177345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311052429817854742279173 433322330590847764177345)
                  ·
                    rfl

theorem cell22_3797515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 4].length) (baseStart_3797515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797515 prefixEnd_3797515 := by exact prefixLift 3797515
  have htrace : WordTrace (prefixWord ++ tailWord_3797515) baseStart_3797515 baseEnd_3797515 := by
    simpa [prefixWord, tailWord_3797515, baseEnd_3797515] using wordTrace_append hprefix tailTrace_3797515
  have hstable : (prefixWord ++ tailWord_3797515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797515).length < 2 ^ (prefixWord ++ tailWord_3797515).sum := by decide
  have hdescent : baseEnd_3797515 < baseStart_3797515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797530 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 2, 3]
def baseStart_3797530 : Nat := 118140960795 + 3797530 * 2 ^ 59
def prefixEnd_3797530 : Nat := 4983230072969 + 3 ^ 40 * 3797530 * 2
def baseEnd_3797530 : Nat := 1299972126579088253406989

theorem tailTrace_3797530 : CollatzResearch.WordTrace tailWord_3797530 prefixEnd_3797530 1299972126579088253406989 := by
  unfold tailWord_3797530
  simp only [CollatzResearch.WordTrace]
  refine ⟨34626824483051212833523511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92338198621469900889396029 34626824483051212833523511)
  ·
    refine ⟨51940236724576819250285267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34626824483051212833523511 51940236724576819250285267)
    ·
      refine ⟨77910355086865228875427901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51940236724576819250285267 77910355086865228875427901)
      ·
        refine ⟨29216383157574460828285463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77910355086865228875427901 29216383157574460828285463)
        ·
          refine ⟨43824574736361691242428195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29216383157574460828285463 43824574736361691242428195)
          ·
            refine ⟨65736862104542536863642293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43824574736361691242428195 65736862104542536863642293)
            ·
              refine ⟨6162830822300862830966465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65736862104542536863642293 6162830822300862830966465)
              ·
                refine ⟨4622123116725647123224849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6162830822300862830966465 4622123116725647123224849)
                ·
                  refine ⟨3466592337544235342418637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4622123116725647123224849 3466592337544235342418637)
                  ·
                    refine ⟨1299972126579088253406989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3466592337544235342418637 1299972126579088253406989)
                    ·
                      rfl

theorem cell22_3797530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_3797530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797530 prefixEnd_3797530 := by exact prefixLift 3797530
  have htrace : WordTrace (prefixWord ++ tailWord_3797530) baseStart_3797530 baseEnd_3797530 := by
    simpa [prefixWord, tailWord_3797530, baseEnd_3797530] using wordTrace_append hprefix tailTrace_3797530
  have hstable : (prefixWord ++ tailWord_3797530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797530).length < 2 ^ (prefixWord ++ tailWord_3797530).sum := by decide
  have hdescent : baseEnd_3797530 < baseStart_3797530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797566 : List Nat := [4, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_3797566 : Nat := 118140960795 + 3797566 * 2 ^ 59
def prefixEnd_3797566 : Nat := 4983230072969 + 3 ^ 40 * 3797566 * 2
def baseEnd_3797566 : Nat := 433328150038265386502293

theorem tailTrace_3797566 : CollatzResearch.WordTrace tailWord_3797566 prefixEnd_3797566 433328150038265386502293 := by
  unfold tailWord_3797566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17313576370009303685300569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92339073973382952988269701 17313576370009303685300569)
  ·
    refine ⟨12985182277506977763975427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17313576370009303685300569 12985182277506977763975427)
    ·
      refine ⟨19477773416260466645963141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12985182277506977763975427 19477773416260466645963141)
      ·
        refine ⟨3652082515548837496118089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19477773416260466645963141 3652082515548837496118089)
        ·
          refine ⟨2739061886661628122088567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3652082515548837496118089 2739061886661628122088567)
          ·
            refine ⟨4108592829992442183132851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739061886661628122088567 4108592829992442183132851)
            ·
              refine ⟨6162889244988663274699277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108592829992442183132851 6162889244988663274699277)
              ·
                refine ⟨2311083466870748728012229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6162889244988663274699277 2311083466870748728012229)
                ·
                  refine ⟨433328150038265386502293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311083466870748728012229 433328150038265386502293)
                  ·
                    rfl

theorem cell22_3797566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_3797566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797566 prefixEnd_3797566 := by exact prefixLift 3797566
  have htrace : WordTrace (prefixWord ++ tailWord_3797566) baseStart_3797566 baseEnd_3797566 := by
    simpa [prefixWord, tailWord_3797566, baseEnd_3797566] using wordTrace_append hprefix tailTrace_3797566
  have hstable : (prefixWord ++ tailWord_3797566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797566).length < 2 ^ (prefixWord ++ tailWord_3797566).sum := by decide
  have hdescent : baseEnd_3797566 < baseStart_3797566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797588 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 7]
def baseStart_3797588 : Nat := 118140960795 + 3797588 * 2 ^ 59
def prefixEnd_3797588 : Nat := 4983230072969 + 3 ^ 40 * 3797588 * 2
def baseEnd_3797588 : Nat := 433330660388131811818937

theorem tailTrace_3797588 : CollatzResearch.WordTrace tailWord_3797588 prefixEnd_3797588 433330660388131811818937 := by
  unfold tailWord_3797588
  simp only [CollatzResearch.WordTrace]
  refine ⟨69254706682997363619852709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92339608910663151493136945 69254706682997363619852709)
  ·
    refine ⟨12985257503062005678722383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69254706682997363619852709 12985257503062005678722383)
    ·
      refine ⟨19477886254593008518083575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12985257503062005678722383 19477886254593008518083575)
      ·
        refine ⟨29216829381889512777125363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19477886254593008518083575 29216829381889512777125363)
        ·
          refine ⟨43825244072834269165688045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29216829381889512777125363 43825244072834269165688045)
          ·
            refine ⟨16434466527312850937133017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43825244072834269165688045 16434466527312850937133017)
            ·
              refine ⟨12325849895484638202849763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16434466527312850937133017 12325849895484638202849763)
              ·
                refine ⟨18488774843226957304274645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12325849895484638202849763 18488774843226957304274645)
                ·
                  refine ⟨433330660388131811818937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18488774843226957304274645 433330660388131811818937)
                  ·
                    rfl

theorem cell22_3797588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_3797588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797588 prefixEnd_3797588 := by exact prefixLift 3797588
  have htrace : WordTrace (prefixWord ++ tailWord_3797588) baseStart_3797588 baseEnd_3797588 := by
    simpa [prefixWord, tailWord_3797588, baseEnd_3797588] using wordTrace_append hprefix tailTrace_3797588
  have hstable : (prefixWord ++ tailWord_3797588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797588).length < 2 ^ (prefixWord ++ tailWord_3797588).sum := by decide
  have hdescent : baseEnd_3797588 < baseStart_3797588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797605 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 5]
def baseStart_3797605 : Nat := 118140960795 + 3797605 * 2 ^ 59
def prefixEnd_3797605 : Nat := 4983230072969 + 3 ^ 40 * 3797605 * 2
def baseEnd_3797605 : Nat := 433332600203937685927253

theorem tailTrace_3797605 : CollatzResearch.WordTrace tailWord_3797605 prefixEnd_3797605 433332600203937685927253 := by
  unfold tailWord_3797605
  simp only [CollatzResearch.WordTrace]
  refine ⟨138510033406933139143074269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92340022271288759428716179 138510033406933139143074269)
  ·
    refine ⟨51941262527599927178652851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138510033406933139143074269 51941262527599927178652851)
    ·
      refine ⟨77911893791399890767979277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51941262527599927178652851 77911893791399890767979277)
      ·
        refine ⟨29216960171774959037992229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77911893791399890767979277 29216960171774959037992229)
        ·
          refine ⟨5478180032207804819623543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29216960171774959037992229 5478180032207804819623543)
          ·
            refine ⟨8217270048311707229435315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478180032207804819623543 8217270048311707229435315)
            ·
              refine ⟨12325905072467560844152973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8217270048311707229435315 12325905072467560844152973)
              ·
                refine ⟨4622214402175335316557365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12325905072467560844152973 4622214402175335316557365)
                ·
                  refine ⟨433332600203937685927253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4622214402175335316557365 433332600203937685927253)
                  ·
                    rfl

theorem cell22_3797605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_3797605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797605 prefixEnd_3797605 := by exact prefixLift 3797605
  have htrace : WordTrace (prefixWord ++ tailWord_3797605) baseStart_3797605 baseEnd_3797605 := by
    simpa [prefixWord, tailWord_3797605, baseEnd_3797605] using wordTrace_append hprefix tailTrace_3797605
  have hstable : (prefixWord ++ tailWord_3797605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797605).length < 2 ^ (prefixWord ++ tailWord_3797605).sum := by decide
  have hdescent : baseEnd_3797605 < baseStart_3797605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797716 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_3797716 : Nat := 118140960795 + 3797716 * 2 ^ 59
def prefixEnd_3797716 : Nat := 4983230072969 + 3 ^ 40 * 3797716 * 2
def baseEnd_3797716 : Nat := 1300035798180245768256419

theorem tailTrace_3797716 : CollatzResearch.WordTrace tailWord_3797716 prefixEnd_3797716 1300035798180245768256419 := by
  unfold tailWord_3797716
  simp only [CollatzResearch.WordTrace]
  refine ⟨69257040954765502550182501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92342721273020670066910001 69257040954765502550182501)
  ·
    refine ⟨12985695179018531728159219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69257040954765502550182501 12985695179018531728159219)
    ·
      refine ⟨19478542768527797592238829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12985695179018531728159219 19478542768527797592238829)
      ·
        refine ⟨7304453538197924097089561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19478542768527797592238829 7304453538197924097089561)
        ·
          refine ⟨5478340153648443072817171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7304453538197924097089561 5478340153648443072817171)
          ·
            refine ⟨8217510230472664609225757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478340153648443072817171 8217510230472664609225757)
            ·
              refine ⟨3081566336427249228459659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8217510230472664609225757 3081566336427249228459659)
              ·
                refine ⟨4622349504640873842689489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081566336427249228459659 4622349504640873842689489)
                ·
                  refine ⟨3466762128480655382017117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4622349504640873842689489 3466762128480655382017117)
                  ·
                    refine ⟨1300035798180245768256419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3466762128480655382017117 1300035798180245768256419)
                    ·
                      rfl

theorem cell22_3797716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_3797716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797716 prefixEnd_3797716 := by exact prefixLift 3797716
  have htrace : WordTrace (prefixWord ++ tailWord_3797716) baseStart_3797716 baseEnd_3797716 := by
    simpa [prefixWord, tailWord_3797716, baseEnd_3797716] using wordTrace_append hprefix tailTrace_3797716
  have hstable : (prefixWord ++ tailWord_3797716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797716).length < 2 ^ (prefixWord ++ tailWord_3797716).sum := by decide
  have hdescent : baseEnd_3797716 < baseStart_3797716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797770 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_3797770 : Nat := 118140960795 + 3797770 * 2 ^ 59
def prefixEnd_3797770 : Nat := 4983230072969 + 3 ^ 40 * 3797770 * 2
def baseEnd_3797770 : Nat := 1300054283483807627406253

theorem tailTrace_3797770 : CollatzResearch.WordTrace tailWord_3797770 prefixEnd_3797770 1300054283483807627406253 := by
  unfold tailWord_3797770
  simp only [CollatzResearch.WordTrace]
  refine ⟨34629012862833843080707691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92344034300890248215220509 34629012862833843080707691)
  ·
    refine ⟨51943519294250764621061537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34629012862833843080707691 51943519294250764621061537)
    ·
      refine ⟨38957639470688073465796153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51943519294250764621061537 38957639470688073465796153)
      ·
        refine ⟨29218229603016055099347115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38957639470688073465796153 29218229603016055099347115)
        ·
          refine ⟨43827344404524082649020673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29218229603016055099347115 43827344404524082649020673)
          ·
            refine ⟨32870508303393061986765505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43827344404524082649020673 32870508303393061986765505)
            ·
              refine ⟨24652881227544796490074129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32870508303393061986765505 24652881227544796490074129)
              ·
                refine ⟨18489660920658597367555597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24652881227544796490074129 18489660920658597367555597)
                ·
                  refine ⟨6933622845246974012833349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18489660920658597367555597 6933622845246974012833349)
                  ·
                    refine ⟨1300054283483807627406253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6933622845246974012833349 1300054283483807627406253)
                    ·
                      rfl

theorem cell22_3797770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_3797770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797770 prefixEnd_3797770 := by exact prefixLift 3797770
  have htrace : WordTrace (prefixWord ++ tailWord_3797770) baseStart_3797770 baseEnd_3797770 := by
    simpa [prefixWord, tailWord_3797770, baseEnd_3797770] using wordTrace_append hprefix tailTrace_3797770
  have hstable : (prefixWord ++ tailWord_3797770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797770).length < 2 ^ (prefixWord ++ tailWord_3797770).sum := by decide
  have hdescent : baseEnd_3797770 < baseStart_3797770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797815 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 2, 4]
def baseStart_3797815 : Nat := 118140960795 + 3797815 * 2 ^ 59
def prefixEnd_3797815 : Nat := 4983230072969 + 3 ^ 40 * 3797815 * 2
def baseEnd_3797815 : Nat := 1300069687903442510031115

theorem tailTrace_3797815 : CollatzResearch.WordTrace tailWord_3797815 prefixEnd_3797815 1300069687903442510031115 := by
  unfold tailWord_3797815
  simp only [CollatzResearch.WordTrace]
  refine ⟨138517692736172345008218899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92345128490781563338812599 138517692736172345008218899)
  ·
    refine ⟨207776539104258517512328349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138517692736172345008218899 207776539104258517512328349)
    ·
      refine ⟨77916202164096944067123131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207776539104258517512328349 77916202164096944067123131)
      ·
        refine ⟨116874303246145416100684697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77916202164096944067123131 116874303246145416100684697)
        ·
          refine ⟨87655727434609062075513523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116874303246145416100684697 87655727434609062075513523)
          ·
            refine ⟨131483591151913593113270285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87655727434609062075513523 131483591151913593113270285)
            ·
              refine ⟨49306346681967597417476357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131483591151913593113270285 49306346681967597417476357)
              ·
                refine ⟨9244940002868924515776817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49306346681967597417476357 9244940002868924515776817)
                ·
                  refine ⟨6933705002151693386832613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9244940002868924515776817 6933705002151693386832613)
                  ·
                    refine ⟨1300069687903442510031115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6933705002151693386832613 1300069687903442510031115)
                    ·
                      rfl

theorem cell22_3797815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_3797815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797815 prefixEnd_3797815 := by exact prefixLift 3797815
  have htrace : WordTrace (prefixWord ++ tailWord_3797815) baseStart_3797815 baseEnd_3797815 := by
    simpa [prefixWord, tailWord_3797815, baseEnd_3797815] using wordTrace_append hprefix tailTrace_3797815
  have hstable : (prefixWord ++ tailWord_3797815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797815).length < 2 ^ (prefixWord ++ tailWord_3797815).sum := by decide
  have hdescent : baseEnd_3797815 < baseStart_3797815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797847 : List Nat := [1, 1, 3, 2, 4, 2, 3, 6]
def baseStart_3797847 : Nat := 118140960795 + 3797847 * 2 ^ 59
def prefixEnd_3797847 : Nat := 4983230072969 + 3 ^ 40 * 3797847 * 2
def baseEnd_3797847 : Nat := 144453404684156121470113

theorem tailTrace_3797847 : CollatzResearch.WordTrace tailWord_3797847 prefixEnd_3797847 144453404684156121470113 := by
  unfold tailWord_3797847
  simp only [CollatzResearch.WordTrace]
  refine ⟨138518859872056414473383795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92345906581370942982255863 138518859872056414473383795)
  ·
    refine ⟨207778289808084621710075693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138518859872056414473383795 207778289808084621710075693)
    ·
      refine ⟨77916858678031733141278385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207778289808084621710075693 77916858678031733141278385)
      ·
        refine ⟨58437644008523799855958789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77916858678031733141278385 58437644008523799855958789)
        ·
          refine ⟨10957058251598212472992273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58437644008523799855958789 10957058251598212472992273)
          ·
            refine ⟨8217793688698659354744205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10957058251598212472992273 8217793688698659354744205)
            ·
              refine ⟨3081672633261997258029077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8217793688698659354744205 3081672633261997258029077)
              ·
                refine ⟨144453404684156121470113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3081672633261997258029077 144453404684156121470113)
                ·
                  rfl

theorem cell22_3797847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 6].length) (baseStart_3797847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797847 prefixEnd_3797847 := by exact prefixLift 3797847
  have htrace : WordTrace (prefixWord ++ tailWord_3797847) baseStart_3797847 baseEnd_3797847 := by
    simpa [prefixWord, tailWord_3797847, baseEnd_3797847] using wordTrace_append hprefix tailTrace_3797847
  have hstable : (prefixWord ++ tailWord_3797847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797847).length < 2 ^ (prefixWord ++ tailWord_3797847).sum := by decide
  have hdescent : baseEnd_3797847 < baseStart_3797847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797920 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 8]
def baseStart_3797920 : Nat := 118140960795 + 3797920 * 2 ^ 59
def prefixEnd_3797920 : Nat := 4983230072969 + 3 ^ 40 * 3797920 * 2
def baseEnd_3797920 : Nat := 433368543849752412051931

theorem tailTrace_3797920 : CollatzResearch.WordTrace tailWord_3797920 prefixEnd_3797920 433368543849752412051931 := by
  unfold tailWord_3797920
  simp only [CollatzResearch.WordTrace]
  refine ⟨69260761200395973970395607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92347681600527965293860809 69260761200395973970395607)
  ·
    refine ⟨103891141800593960955593411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69260761200395973970395607 103891141800593960955593411)
    ·
      refine ⟨155836712700890941433390117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103891141800593960955593411 155836712700890941433390117)
      ·
        refine ⟨29219383631417051518760647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155836712700890941433390117 29219383631417051518760647)
        ·
          refine ⟨43829075447125577278140971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29219383631417051518760647 43829075447125577278140971)
          ·
            refine ⟨65743613170688365917211457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43829075447125577278140971 65743613170688365917211457)
            ·
              refine ⟨49307709878016274437908593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65743613170688365917211457 49307709878016274437908593)
              ·
                refine ⟨36980782408512205828431445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49307709878016274437908593 36980782408512205828431445)
                ·
                  refine ⟨433368543849752412051931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36980782408512205828431445 433368543849752412051931)
                  ·
                    rfl

theorem cell22_3797920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_3797920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797920 prefixEnd_3797920 := by exact prefixLift 3797920
  have htrace : WordTrace (prefixWord ++ tailWord_3797920) baseStart_3797920 baseEnd_3797920 := by
    simpa [prefixWord, tailWord_3797920, baseEnd_3797920] using wordTrace_append hprefix tailTrace_3797920
  have hstable : (prefixWord ++ tailWord_3797920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797920).length < 2 ^ (prefixWord ++ tailWord_3797920).sum := by decide
  have hdescent : baseEnd_3797920 < baseStart_3797920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797935 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 5, 5]
def baseStart_3797935 : Nat := 118140960795 + 3797935 * 2 ^ 59
def prefixEnd_3797935 : Nat := 4983230072969 + 3 ^ 40 * 3797935 * 2
def baseEnd_3797935 : Nat := 1300110766355802197030747

theorem tailTrace_3797935 : CollatzResearch.WordTrace tailWord_3797935 prefixEnd_3797935 1300110766355802197030747 := by
  unfold tailWord_3797935
  simp only [CollatzResearch.WordTrace]
  refine ⟨138522069495737605502587259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92348046330491737001724839 138522069495737605502587259)
  ·
    refine ⟨207783104243606408253880889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138522069495737605502587259 207783104243606408253880889)
    ·
      refine ⟨155837328182704806190410667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207783104243606408253880889 155837328182704806190410667)
      ·
        refine ⟨233755992274057209285616001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155837328182704806190410667 233755992274057209285616001)
        ·
          refine ⟨175316994205542906964212001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233755992274057209285616001 175316994205542906964212001)
          ·
            refine ⟨131487745654157180223159001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175316994205542906964212001 131487745654157180223159001)
            ·
              refine ⟨98615809240617885167369251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131487745654157180223159001 98615809240617885167369251)
              ·
                refine ⟨147923713860926827751053877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98615809240617885167369251 147923713860926827751053877)
                ·
                  refine ⟨13867848174461890101661301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147923713860926827751053877 13867848174461890101661301)
                  ·
                    refine ⟨1300110766355802197030747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13867848174461890101661301 1300110766355802197030747)
                    ·
                      rfl

theorem cell22_3797935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_3797935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797935 prefixEnd_3797935 := by exact prefixLift 3797935
  have htrace : WordTrace (prefixWord ++ tailWord_3797935) baseStart_3797935 baseEnd_3797935 := by
    simpa [prefixWord, tailWord_3797935, baseEnd_3797935] using wordTrace_append hprefix tailTrace_3797935
  have hstable : (prefixWord ++ tailWord_3797935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797935).length < 2 ^ (prefixWord ++ tailWord_3797935).sum := by decide
  have hdescent : baseEnd_3797935 < baseStart_3797935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797956 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_3797956 : Nat := 118140960795 + 3797956 * 2 ^ 59
def prefixEnd_3797956 : Nat := 4983230072969 + 3 ^ 40 * 3797956 * 2
def baseEnd_3797956 : Nat := 1300117955084965142255683

theorem tailTrace_3797956 : CollatzResearch.WordTrace tailWord_3797956 prefixEnd_3797956 1300117955084965142255683 := by
  unfold tailWord_3797956
  simp only [CollatzResearch.WordTrace]
  refine ⟨69261417714330763044550861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92348556952441017392734481 69261417714330763044550861)
  ·
    refine ⟨25973031642874036141706573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69261417714330763044550861 25973031642874036141706573)
    ·
      refine ⟨9739886866077763553139965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25973031642874036141706573 9739886866077763553139965)
      ·
        refine ⟨3652457574779161332427487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9739886866077763553139965 3652457574779161332427487)
        ·
          refine ⟨5478686362168741998641231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652457574779161332427487 5478686362168741998641231)
          ·
            refine ⟨8218029543253112997961847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478686362168741998641231 8218029543253112997961847)
            ·
              refine ⟨12327044314879669496942771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218029543253112997961847 12327044314879669496942771)
              ·
                refine ⟨18490566472319504245414157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12327044314879669496942771 18490566472319504245414157)
                ·
                  refine ⟨6933962427119814092030309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18490566472319504245414157 6933962427119814092030309)
                  ·
                    refine ⟨1300117955084965142255683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6933962427119814092030309 1300117955084965142255683)
                    ·
                      rfl

theorem cell22_3797956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_3797956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797956 prefixEnd_3797956 := by exact prefixLift 3797956
  have htrace : WordTrace (prefixWord ++ tailWord_3797956) baseStart_3797956 baseEnd_3797956 := by
    simpa [prefixWord, tailWord_3797956, baseEnd_3797956] using wordTrace_append hprefix tailTrace_3797956
  have hstable : (prefixWord ++ tailWord_3797956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797956).length < 2 ^ (prefixWord ++ tailWord_3797956).sum := by decide
  have hdescent : baseEnd_3797956 < baseStart_3797956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3797967 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 2, 4]
def baseStart_3797967 : Nat := 118140960795 + 3797967 * 2 ^ 59
def prefixEnd_3797967 : Nat := 4983230072969 + 3 ^ 40 * 3797967 * 2
def baseEnd_3797967 : Nat := 1300121720609764780230649

theorem tailTrace_3797967 : CollatzResearch.WordTrace tailWord_3797967 prefixEnd_3797967 1300121720609764780230649 := by
  unfold tailWord_3797967
  simp only [CollatzResearch.WordTrace]
  refine ⟨138523236631621674967752155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92348824421081116645168103 138523236631621674967752155)
  ·
    refine ⟨207784854947432512451628233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138523236631621674967752155 207784854947432512451628233)
    ·
      refine ⟨155838641210574384338721175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207784854947432512451628233 155838641210574384338721175)
      ·
        refine ⟨233757961815861576508081763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155838641210574384338721175 233757961815861576508081763)
        ·
          refine ⟨350636942723792364762122645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233757961815861576508081763 350636942723792364762122645)
          ·
            refine ⟨16436106690177767098224499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 350636942723792364762122645 16436106690177767098224499)
            ·
              refine ⟨24654160035266650647336749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16436106690177767098224499 24654160035266650647336749)
              ·
                refine ⟨9245310013224993992751281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24654160035266650647336749 9245310013224993992751281)
                ·
                  refine ⟨6933982509918745494563461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9245310013224993992751281 6933982509918745494563461)
                  ·
                    refine ⟨1300121720609764780230649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6933982509918745494563461 1300121720609764780230649)
                    ·
                      rfl

theorem cell22_3797967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_3797967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3797967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3797967 prefixEnd_3797967 := by exact prefixLift 3797967
  have htrace : WordTrace (prefixWord ++ tailWord_3797967) baseStart_3797967 baseEnd_3797967 := by
    simpa [prefixWord, tailWord_3797967, baseEnd_3797967] using wordTrace_append hprefix tailTrace_3797967
  have hstable : (prefixWord ++ tailWord_3797967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3797967).length < 2 ^ (prefixWord ++ tailWord_3797967).sum := by decide
  have hdescent : baseEnd_3797967 < baseStart_3797967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3797967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798042 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_3798042 : Nat := 118140960795 + 3798042 * 2 ^ 59
def prefixEnd_3798042 : Nat := 4983230072969 + 3 ^ 40 * 3798042 * 2
def baseEnd_3798042 : Nat := 1300147394642489584605419

theorem tailTrace_3798042 : CollatzResearch.WordTrace tailWord_3798042 prefixEnd_3798042 1300147394642489584605419 := by
  unfold tailWord_3798042
  simp only [CollatzResearch.WordTrace]
  refine ⟨34631493026587490694183095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92350648070899975184488253 34631493026587490694183095)
  ·
    refine ⟨51947239539881236041274643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34631493026587490694183095 51947239539881236041274643)
    ·
      refine ⟨77920859309821854061911965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51947239539881236041274643 77920859309821854061911965)
      ·
        refine ⟨29220322241183195273216987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77920859309821854061911965 29220322241183195273216987)
        ·
          refine ⟨43830483361774792909825481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29220322241183195273216987 43830483361774792909825481)
          ·
            refine ⟨32872862521331094682369111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43830483361774792909825481 32872862521331094682369111)
            ·
              refine ⟨49309293781996642023553667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32872862521331094682369111 49309293781996642023553667)
              ·
                refine ⟨73963940672994963035330501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49309293781996642023553667 73963940672994963035330501)
                ·
                  refine ⟨13868238876186555569124469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73963940672994963035330501 13868238876186555569124469)
                  ·
                    refine ⟨1300147394642489584605419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13868238876186555569124469 1300147394642489584605419)
                    ·
                      rfl

theorem cell22_3798042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_3798042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798042 prefixEnd_3798042 := by exact prefixLift 3798042
  have htrace : WordTrace (prefixWord ++ tailWord_3798042) baseStart_3798042 baseEnd_3798042 := by
    simpa [prefixWord, tailWord_3798042, baseEnd_3798042] using wordTrace_append hprefix tailTrace_3798042
  have hstable : (prefixWord ++ tailWord_3798042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798042).length < 2 ^ (prefixWord ++ tailWord_3798042).sum := by decide
  have hdescent : baseEnd_3798042 < baseStart_3798042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798044 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 7]
def baseStart_3798044 : Nat := 118140960795 + 3798044 * 2 ^ 59
def prefixEnd_3798044 : Nat := 4983230072969 + 3 ^ 40 * 3798044 * 2
def baseEnd_3798044 : Nat := 433382693094454082018471

theorem tailTrace_3798044 : CollatzResearch.WordTrace tailWord_3798044 prefixEnd_3798044 433382693094454082018471 := by
  unfold tailWord_3798044
  simp only [CollatzResearch.WordTrace]
  refine ⟨69263022526171358559152593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92350696701561811412203457 69263022526171358559152593)
  ·
    refine ⟨51947266894628518919364445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69263022526171358559152593 51947266894628518919364445)
    ·
      refine ⟨19480225085485694594761667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51947266894628518919364445 19480225085485694594761667)
      ·
        refine ⟨29220337628228541892142501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19480225085485694594761667 29220337628228541892142501)
        ·
          refine ⟨5478813305292851604776719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29220337628228541892142501 5478813305292851604776719)
          ·
            refine ⟨8218219957939277407165079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478813305292851604776719 8218219957939277407165079)
            ·
              refine ⟨12327329936908916110747619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218219957939277407165079 12327329936908916110747619)
              ·
                refine ⟨18490994905363374166121429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12327329936908916110747619 18490994905363374166121429)
                ·
                  refine ⟨433382693094454082018471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18490994905363374166121429 433382693094454082018471)
                  ·
                    rfl

theorem cell22_3798044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_3798044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798044 prefixEnd_3798044 := by exact prefixLift 3798044
  have htrace : WordTrace (prefixWord ++ tailWord_3798044) baseStart_3798044 baseEnd_3798044 := by
    simpa [prefixWord, tailWord_3798044, baseEnd_3798044] using wordTrace_append hprefix tailTrace_3798044
  have hstable : (prefixWord ++ tailWord_3798044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798044).length < 2 ^ (prefixWord ++ tailWord_3798044).sum := by decide
  have hdescent : baseEnd_3798044 < baseStart_3798044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798048 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 3, 3]
def baseStart_3798048 : Nat := 118140960795 + 3798048 * 2 ^ 59
def prefixEnd_3798048 : Nat := 4983230072969 + 3 ^ 40 * 3798048 * 2
def baseEnd_3798048 : Nat := 1300149448565107568955401

theorem tailTrace_3798048 : CollatzResearch.WordTrace tailWord_3798048 prefixEnd_3798048 1300149448565107568955401 := by
  unfold tailWord_3798048
  simp only [CollatzResearch.WordTrace]
  refine ⟨69263095472164112900725399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92350793962885483867633865 69263095472164112900725399)
  ·
    refine ⟨103894643208246169351088099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69263095472164112900725399 103894643208246169351088099)
    ·
      refine ⟨155841964812369254026632149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103894643208246169351088099 155841964812369254026632149)
      ·
        refine ⟨3652546050289904391249191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 155841964812369254026632149 3652546050289904391249191)
        ·
          refine ⟨5478819075434856586873787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652546050289904391249191 5478819075434856586873787)
          ·
            refine ⟨8218228613152284880310681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478819075434856586873787 8218228613152284880310681)
            ·
              refine ⟨6163671459864213660233011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8218228613152284880310681 6163671459864213660233011)
              ·
                refine ⟨9245507189796320490349517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6163671459864213660233011 9245507189796320490349517)
                ·
                  refine ⟨3467065196173620183881069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9245507189796320490349517 3467065196173620183881069)
                  ·
                    refine ⟨1300149448565107568955401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3467065196173620183881069 1300149448565107568955401)
                    ·
                      rfl

theorem cell22_3798048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 3, 3].length) (baseStart_3798048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798048 prefixEnd_3798048 := by exact prefixLift 3798048
  have htrace : WordTrace (prefixWord ++ tailWord_3798048) baseStart_3798048 baseEnd_3798048 := by
    simpa [prefixWord, tailWord_3798048, baseEnd_3798048] using wordTrace_append hprefix tailTrace_3798048
  have hstable : (prefixWord ++ tailWord_3798048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798048).length < 2 ^ (prefixWord ++ tailWord_3798048).sum := by decide
  have hdescent : baseEnd_3798048 < baseStart_3798048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798074 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_3798074 : Nat := 118140960795 + 3798074 * 2 ^ 59
def prefixEnd_3798074 : Nat := 4983230072969 + 3 ^ 40 * 3798074 * 2
def baseEnd_3798074 : Nat := 1300158348896452167805321

theorem tailTrace_3798074 : CollatzResearch.WordTrace tailWord_3798074 prefixEnd_3798074 1300158348896452167805321 := by
  unfold tailWord_3798074
  simp only [CollatzResearch.WordTrace]
  refine ⟨34631784810558508060474319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92351426161489354827931517 34631784810558508060474319)
  ·
    refine ⟨51947677215837762090711479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34631784810558508060474319 51947677215837762090711479)
    ·
      refine ⟨77921515823756643136067219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51947677215837762090711479 77921515823756643136067219)
      ·
        refine ⟨116882273735634964704100829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77921515823756643136067219 116882273735634964704100829)
        ·
          refine ⟨43830852650863111764037811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116882273735634964704100829 43830852650863111764037811)
          ·
            refine ⟨65746278976294667646056717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43830852650863111764037811 65746278976294667646056717)
            ·
              refine ⟨24654854616110500367271269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65746278976294667646056717 24654854616110500367271269)
              ·
                refine ⟨4622785240520718818863363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24654854616110500367271269 4622785240520718818863363)
                ·
                  refine ⟨6934177860781078228295045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4622785240520718818863363 6934177860781078228295045)
                  ·
                    refine ⟨1300158348896452167805321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6934177860781078228295045 1300158348896452167805321)
                    ·
                      rfl

theorem cell22_3798074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_3798074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798074 prefixEnd_3798074 := by exact prefixLift 3798074
  have htrace : WordTrace (prefixWord ++ tailWord_3798074) baseStart_3798074 baseEnd_3798074 := by
    simpa [prefixWord, tailWord_3798074, baseEnd_3798074] using wordTrace_append hprefix tailTrace_3798074
  have hstable : (prefixWord ++ tailWord_3798074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798074).length < 2 ^ (prefixWord ++ tailWord_3798074).sum := by decide
  have hdescent : baseEnd_3798074 < baseStart_3798074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798089 : List Nat := [1, 2, 1, 1, 2, 2, 2, 7, 4]
def baseStart_3798089 : Nat := 118140960795 + 3798089 * 2 ^ 59
def prefixEnd_3798089 : Nat := 4983230072969 + 3 ^ 40 * 3798089 * 2
def baseEnd_3798089 : Nat := 433387827900999042893425

theorem tailTrace_3798089 : CollatzResearch.WordTrace tailWord_3798089 prefixEnd_3798089 433387827900999042893425 := by
  unfold tailWord_3798089
  simp only [CollatzResearch.WordTrace]
  refine ⟨138527686337179689803693321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92351790891453126535795547 138527686337179689803693321)
  ·
    refine ⟨103895764752884767352769991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138527686337179689803693321 103895764752884767352769991)
    ·
      refine ⟨155843647129327151029154987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103895764752884767352769991 155843647129327151029154987)
      ·
        refine ⟨233765470693990726543732481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155843647129327151029154987 233765470693990726543732481)
        ·
          refine ⟨175324103020493044907799361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233765470693990726543732481 175324103020493044907799361)
          ·
            refine ⟨131493077265369783680849521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175324103020493044907799361 131493077265369783680849521)
            ·
              refine ⟨98619807949027337760637141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131493077265369783680849521 98619807949027337760637141)
              ·
                refine ⟨2311401748805328228764933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98619807949027337760637141 2311401748805328228764933)
                ·
                  refine ⟨433387827900999042893425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311401748805328228764933 433387827900999042893425)
                  ·
                    rfl

theorem cell22_3798089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 4].length) (baseStart_3798089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798089 prefixEnd_3798089 := by exact prefixLift 3798089
  have htrace : WordTrace (prefixWord ++ tailWord_3798089) baseStart_3798089 baseEnd_3798089 := by
    simpa [prefixWord, tailWord_3798089, baseEnd_3798089] using wordTrace_append hprefix tailTrace_3798089
  have hstable : (prefixWord ++ tailWord_3798089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798089).length < 2 ^ (prefixWord ++ tailWord_3798089).sum := by decide
  have hdescent : baseEnd_3798089 < baseStart_3798089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798104 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 4, 3]
def baseStart_3798104 : Nat := 118140960795 + 3798104 * 2 ^ 59
def prefixEnd_3798104 : Nat := 4983230072969 + 3 ^ 40 * 3798104 * 2
def baseEnd_3798104 : Nat := 1300168618509542089555229

theorem tailTrace_3798104 : CollatzResearch.WordTrace tailWord_3798104 prefixEnd_3798104 1300168618509542089555229 := by
  unfold tailWord_3798104
  simp only [CollatzResearch.WordTrace]
  refine ⟨69264116716062673682744683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92352155621416898243659577 69264116716062673682744683)
  ·
    refine ⟨103896175074094010524117025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69264116716062673682744683 103896175074094010524117025)
    ·
      refine ⟨77922131305570507893087769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103896175074094010524117025 77922131305570507893087769)
      ·
        refine ⟨58441598479177880919815827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77922131305570507893087769 58441598479177880919815827)
        ·
          refine ⟨87662397718766821379723741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58441598479177880919815827 87662397718766821379723741)
          ·
            refine ⟨32873399144537558017396403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87662397718766821379723741 32873399144537558017396403)
            ·
              refine ⟨49310098716806337026094605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32873399144537558017396403 49310098716806337026094605)
              ·
                refine ⟨18491287018802376384785477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49310098716806337026094605 18491287018802376384785477)
                ·
                  refine ⟨3467116316025445572147277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18491287018802376384785477 3467116316025445572147277)
                  ·
                    refine ⟨1300168618509542089555229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3467116316025445572147277 1300168618509542089555229)
                    ·
                      rfl

theorem cell22_3798104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_3798104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798104 prefixEnd_3798104 := by exact prefixLift 3798104
  have htrace : WordTrace (prefixWord ++ tailWord_3798104) baseStart_3798104 baseEnd_3798104 := by
    simpa [prefixWord, tailWord_3798104, baseEnd_3798104] using wordTrace_append hprefix tailTrace_3798104
  have hstable : (prefixWord ++ tailWord_3798104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798104).length < 2 ^ (prefixWord ++ tailWord_3798104).sum := by decide
  have hdescent : baseEnd_3798104 < baseStart_3798104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798121 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 2, 3]
def baseStart_3798121 : Nat := 118140960795 + 3798121 * 2 ^ 59
def prefixEnd_3798121 : Nat := 4983230072969 + 3 ^ 40 * 3798121 * 2
def baseEnd_3798121 : Nat := 1300174437956959711880177

theorem tailTrace_3798121 : CollatzResearch.WordTrace tailWord_3798121 prefixEnd_3798121 1300174437956959711880177 := by
  unfold tailWord_3798121
  simp only [CollatzResearch.WordTrace]
  refine ⟨138528853473063759268858217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92352568982042506179238811 138528853473063759268858217)
  ·
    refine ⟨103896640104797819451643663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138528853473063759268858217 103896640104797819451643663)
    ·
      refine ⟨155844960157196729177465495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103896640104797819451643663 155844960157196729177465495)
      ·
        refine ⟨233767440235795093766198243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155844960157196729177465495 233767440235795093766198243)
        ·
          refine ⟨350651160353692640649297365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233767440235795093766198243 350651160353692640649297365)
          ·
            refine ⟨8218386570789671265217907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 350651160353692640649297365 8218386570789671265217907)
            ·
              refine ⟨12327579856184506897826861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218386570789671265217907 12327579856184506897826861)
              ·
                refine ⟨4622842446069190086685073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12327579856184506897826861 4622842446069190086685073)
                ·
                  refine ⟨3467131834551892565013805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4622842446069190086685073 3467131834551892565013805)
                  ·
                    refine ⟨1300174437956959711880177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3467131834551892565013805 1300174437956959711880177)
                    ·
                      rfl

theorem cell22_3798121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 3].length) (baseStart_3798121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798121 prefixEnd_3798121 := by exact prefixLift 3798121
  have htrace : WordTrace (prefixWord ++ tailWord_3798121) baseStart_3798121 baseEnd_3798121 := by
    simpa [prefixWord, tailWord_3798121, baseEnd_3798121] using wordTrace_append hprefix tailTrace_3798121
  have hstable : (prefixWord ++ tailWord_3798121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798121).length < 2 ^ (prefixWord ++ tailWord_3798121).sum := by decide
  have hdescent : baseEnd_3798121 < baseStart_3798121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798134 : List Nat := [5, 1, 1, 2, 1, 1, 1, 10]
def baseStart_3798134 : Nat := 118140960795 + 3798134 * 2 ^ 59
def prefixEnd_3798134 : Nat := 4983230072969 + 3 ^ 40 * 3798134 * 2
def baseEnd_3798134 : Nat := 144464320902514667922793

theorem tailTrace_3798134 : CollatzResearch.WordTrace tailWord_3798134 prefixEnd_3798134 144464320902514667922793 := by
  unfold tailWord_3798134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8658082976376041405567591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92352885081344441659387637 8658082976376041405567591)
  ·
    refine ⟨12987124464564062108351387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8658082976376041405567591 12987124464564062108351387)
    ·
      refine ⟨19480686696846093162527081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12987124464564062108351387 19480686696846093162527081)
      ·
        refine ⟨14610515022634569871895311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19480686696846093162527081 14610515022634569871895311)
        ·
          refine ⟨21915772533951854807842967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14610515022634569871895311 21915772533951854807842967)
          ·
            refine ⟨32873658800927782211764451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21915772533951854807842967 32873658800927782211764451)
            ·
              refine ⟨49310488201391673317646677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32873658800927782211764451 49310488201391673317646677)
              ·
                refine ⟨144464320902514667922793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49310488201391673317646677 144464320902514667922793)
                ·
                  rfl

theorem cell22_3798134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_3798134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798134 prefixEnd_3798134 := by exact prefixLift 3798134
  have htrace : WordTrace (prefixWord ++ tailWord_3798134) baseStart_3798134 baseEnd_3798134 := by
    simpa [prefixWord, tailWord_3798134, baseEnd_3798134] using wordTrace_append hprefix tailTrace_3798134
  have hstable : (prefixWord ++ tailWord_3798134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798134).length < 2 ^ (prefixWord ++ tailWord_3798134).sum := by decide
  have hdescent : baseEnd_3798134 < baseStart_3798134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798183 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 3, 3]
def baseStart_3798183 : Nat := 118140960795 + 3798183 * 2 ^ 59
def prefixEnd_3798183 : Nat := 4983230072969 + 3 ^ 40 * 3798183 * 2
def baseEnd_3798183 : Nat := 1300195661824012216829987

theorem tailTrace_3798183 : CollatzResearch.WordTrace tailWord_3798183 prefixEnd_3798183 1300195661824012216829987 := by
  unfold tailWord_3798183
  simp only [CollatzResearch.WordTrace]
  refine ⟨138531114798839143857615203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92354076532559429238410135 138531114798839143857615203)
  ·
    refine ⟨207796672198258715786422805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138531114798839143857615203 207796672198258715786422805)
    ·
      refine ⟨9740469009293377302488569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 207796672198258715786422805 9740469009293377302488569)
      ·
        refine ⟨7305351756970032976866427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9740469009293377302488569 7305351756970032976866427)
        ·
          refine ⟨10958027635455049465299641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7305351756970032976866427 10958027635455049465299641)
          ·
            refine ⟨8218520726591287098974731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10958027635455049465299641 8218520726591287098974731)
            ·
              refine ⟨12327781089886930648462097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218520726591287098974731 12327781089886930648462097)
              ·
                refine ⟨9245835817415197986346573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12327781089886930648462097 9245835817415197986346573)
                ·
                  refine ⟨3467188431530699244879965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9245835817415197986346573 3467188431530699244879965)
                  ·
                    refine ⟨1300195661824012216829987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3467188431530699244879965 1300195661824012216829987)
                    ·
                      rfl

theorem cell22_3798183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_3798183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798183 prefixEnd_3798183 := by exact prefixLift 3798183
  have htrace : WordTrace (prefixWord ++ tailWord_3798183) baseStart_3798183 baseEnd_3798183 := by
    simpa [prefixWord, tailWord_3798183, baseEnd_3798183] using wordTrace_append hprefix tailTrace_3798183
  have hstable : (prefixWord ++ tailWord_3798183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798183).length < 2 ^ (prefixWord ++ tailWord_3798183).sum := by decide
  have hdescent : baseEnd_3798183 < baseStart_3798183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798271 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 2, 4]
def baseStart_3798271 : Nat := 118140960795 + 3798271 * 2 ^ 59
def prefixEnd_3798271 : Nat := 4983230072969 + 3 ^ 40 * 3798271 * 2
def baseEnd_3798271 : Nat := 1300225786022409320629717

theorem tailTrace_3798271 : CollatzResearch.WordTrace tailWord_3798271 prefixEnd_3798271 1300225786022409320629717 := by
  unfold tailWord_3798271
  simp only [CollatzResearch.WordTrace]
  refine ⟨138534324422520334886818667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92356216281680223257879111 138534324422520334886818667)
  ·
    refine ⟨207801486633780502330228001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138534324422520334886818667 207801486633780502330228001)
    ·
      refine ⟨155851114975335376747671001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207801486633780502330228001 155851114975335376747671001)
      ·
        refine ⟨116888336231501532560753251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155851114975335376747671001 116888336231501532560753251)
        ·
          refine ⟨175332504347252298841129877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116888336231501532560753251 175332504347252298841129877)
          ·
            refine ⟨8218711141277451508177963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 175332504347252298841129877 8218711141277451508177963)
            ·
              refine ⟨12328066711916177262266945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218711141277451508177963 12328066711916177262266945)
              ·
                refine ⟨9246050033937132946700209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12328066711916177262266945 9246050033937132946700209)
                ·
                  refine ⟨6934537525452849710025157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9246050033937132946700209 6934537525452849710025157)
                  ·
                    refine ⟨1300225786022409320629717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6934537525452849710025157 1300225786022409320629717)
                    ·
                      rfl

theorem cell22_3798271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_3798271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798271 prefixEnd_3798271 := by exact prefixLift 3798271
  have htrace : WordTrace (prefixWord ++ tailWord_3798271) baseStart_3798271 baseEnd_3798271 := by
    simpa [prefixWord, tailWord_3798271, baseEnd_3798271] using wordTrace_append hprefix tailTrace_3798271
  have hstable : (prefixWord ++ tailWord_3798271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798271).length < 2 ^ (prefixWord ++ tailWord_3798271).sum := by decide
  have hdescent : baseEnd_3798271 < baseStart_3798271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798286 : List Nat := [4, 1, 1, 2, 1, 4, 2, 7]
def baseStart_3798286 : Nat := 118140960795 + 3798286 * 2 ^ 59
def prefixEnd_3798286 : Nat := 4983230072969 + 3 ^ 40 * 3798286 * 2
def baseEnd_3798286 : Nat := 144470102314328253500519

theorem tailTrace_3798286 : CollatzResearch.WordTrace tailWord_3798286 prefixEnd_3798286 144470102314328253500519 := by
  unfold tailWord_3798286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17316858939683249056076839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92356581011643994965743141 17316858939683249056076839)
  ·
    refine ⟨25975288409524873584115259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17316858939683249056076839 25975288409524873584115259)
    ·
      refine ⟨38962932614287310376172889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25975288409524873584115259 38962932614287310376172889)
      ·
        refine ⟨29222199460715482782129667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38962932614287310376172889 29222199460715482782129667)
        ·
          refine ⟨43833299191073224173194501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29222199460715482782129667 43833299191073224173194501)
          ·
            refine ⟨8218743598326229532473969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43833299191073224173194501 8218743598326229532473969)
            ·
              refine ⟨6164057698744672149355477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8218743598326229532473969 6164057698744672149355477)
              ·
                refine ⟨144470102314328253500519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6164057698744672149355477 144470102314328253500519)
                ·
                  rfl

theorem cell22_3798286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_3798286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798286 prefixEnd_3798286 := by exact prefixLift 3798286
  have htrace : WordTrace (prefixWord ++ tailWord_3798286) baseStart_3798286 baseEnd_3798286 := by
    simpa [prefixWord, tailWord_3798286, baseEnd_3798286] using wordTrace_append hprefix tailTrace_3798286
  have hstable : (prefixWord ++ tailWord_3798286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798286).length < 2 ^ (prefixWord ++ tailWord_3798286).sum := by decide
  have hdescent : baseEnd_3798286 < baseStart_3798286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798326 : List Nat := [5, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_3798326 : Nat := 118140960795 + 3798326 * 2 ^ 59
def prefixEnd_3798326 : Nat := 4983230072969 + 3 ^ 40 * 3798326 * 2
def baseEnd_3798326 : Nat := 433414871215469170168183

theorem tailTrace_3798326 : CollatzResearch.WordTrace tailWord_3798326 prefixEnd_3798326 433414871215469170168183 := by
  unfold tailWord_3798326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8658520652332567455004427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92357553624880719520047221 8658520652332567455004427)
  ·
    refine ⟨12987780978498851182506641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8658520652332567455004427 12987780978498851182506641)
    ·
      refine ⟨9740835733874138386879981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12987780978498851182506641 9740835733874138386879981)
      ·
        refine ⟨3652813400202801895079993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9740835733874138386879981 3652813400202801895079993)
        ·
          refine ⟨2739610050152101421309995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3652813400202801895079993 2739610050152101421309995)
          ·
            refine ⟨4109415075228152131964993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739610050152101421309995 4109415075228152131964993)
            ·
              refine ⟨3082061306421114098973745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4109415075228152131964993 3082061306421114098973745)
              ·
                refine ⟨2311545979815835574230309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3082061306421114098973745 2311545979815835574230309)
                ·
                  refine ⟨433414871215469170168183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311545979815835574230309 433414871215469170168183)
                  ·
                    rfl

theorem cell22_3798326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_3798326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798326 prefixEnd_3798326 := by exact prefixLift 3798326
  have htrace : WordTrace (prefixWord ++ tailWord_3798326) baseStart_3798326 baseEnd_3798326 := by
    simpa [prefixWord, tailWord_3798326, baseEnd_3798326] using wordTrace_append hprefix tailTrace_3798326
  have hstable : (prefixWord ++ tailWord_3798326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798326).length < 2 ^ (prefixWord ++ tailWord_3798326).sum := by decide
  have hdescent : baseEnd_3798326 < baseStart_3798326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798335 : List Nat := [1, 1, 2, 2, 4, 3, 1, 4, 1, 3]
def baseStart_3798335 : Nat := 118140960795 + 3798335 * 2 ^ 59
def prefixEnd_3798335 : Nat := 4983230072969 + 3 ^ 40 * 3798335 * 2
def baseEnd_3798335 : Nat := 1300247694530334487029521

theorem tailTrace_3798335 : CollatzResearch.WordTrace tailWord_3798335 prefixEnd_3798335 1300247694530334487029521 := by
  unfold tailWord_3798335
  simp only [CollatzResearch.WordTrace]
  refine ⟨138536658694288473817148459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92357772462858982544765639 138536658694288473817148459)
  ·
    refine ⟨207804988041432710725722689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138536658694288473817148459 207804988041432710725722689)
    ·
      refine ⟨155853741031074533044292017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207804988041432710725722689 155853741031074533044292017)
      ·
        refine ⟨116890305773305899783219013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155853741031074533044292017 116890305773305899783219013)
        ·
          refine ⟨21916932332494856209353565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116890305773305899783219013 21916932332494856209353565)
          ·
            refine ⟨8218849624685571078507587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21916932332494856209353565 8218849624685571078507587)
            ·
              refine ⟨12328274437028356617761381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218849624685571078507587 12328274437028356617761381)
              ·
                refine ⟨2311551456942816865830259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12328274437028356617761381 2311551456942816865830259)
                ·
                  refine ⟨3467327185414225298745389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311551456942816865830259 3467327185414225298745389)
                  ·
                    refine ⟨1300247694530334487029521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3467327185414225298745389 1300247694530334487029521)
                    ·
                      rfl

theorem cell22_3798335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 1, 3].length) (baseStart_3798335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798335 prefixEnd_3798335 := by exact prefixLift 3798335
  have htrace : WordTrace (prefixWord ++ tailWord_3798335) baseStart_3798335 baseEnd_3798335 := by
    simpa [prefixWord, tailWord_3798335, baseEnd_3798335] using wordTrace_append hprefix tailTrace_3798335
  have hstable : (prefixWord ++ tailWord_3798335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798335).length < 2 ^ (prefixWord ++ tailWord_3798335).sum := by decide
  have hdescent : baseEnd_3798335 < baseStart_3798335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798361 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 3, 4]
def baseStart_3798361 : Nat := 118140960795 + 3798361 * 2 ^ 59
def prefixEnd_3798361 : Nat := 4983230072969 + 3 ^ 40 * 3798361 * 2
def baseEnd_3798361 : Nat := 1300256594861679085879441

theorem tailTrace_3798361 : CollatzResearch.WordTrace tailWord_3798361 prefixEnd_3798361 1300256594861679085879441 := by
  unfold tailWord_3798361
  simp only [CollatzResearch.WordTrace]
  refine ⟨138537606992194280257594937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92358404661462853505063291 138537606992194280257594937)
  ·
    refine ⟨103903205244145710193196203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138537606992194280257594937 103903205244145710193196203)
    ·
      refine ⟨155854807866218565289794305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103903205244145710193196203 155854807866218565289794305)
      ·
        refine ⟨116891105899663923967345729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155854807866218565289794305 116891105899663923967345729)
        ·
          refine ⟨87668329424747942975509297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116891105899663923967345729 87668329424747942975509297)
          ·
            refine ⟨65751247068560957231631973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87668329424747942975509297 65751247068560957231631973)
            ·
              refine ⟨12328358825355179480930995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65751247068560957231631973 12328358825355179480930995)
              ·
                refine ⟨18492538238032769221396493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12328358825355179480930995 18492538238032769221396493)
                ·
                  refine ⟨6934701839262288458023685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18492538238032769221396493 6934701839262288458023685)
                  ·
                    refine ⟨1300256594861679085879441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6934701839262288458023685 1300256594861679085879441)
                    ·
                      rfl

theorem cell22_3798361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_3798361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798361 prefixEnd_3798361 := by exact prefixLift 3798361
  have htrace : WordTrace (prefixWord ++ tailWord_3798361) baseStart_3798361 baseEnd_3798361 := by
    simpa [prefixWord, tailWord_3798361, baseEnd_3798361] using wordTrace_append hprefix tailTrace_3798361
  have hstable : (prefixWord ++ tailWord_3798361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798361).length < 2 ^ (prefixWord ++ tailWord_3798361).sum := by decide
  have hdescent : baseEnd_3798361 < baseStart_3798361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798382 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_3798382 : Nat := 118140960795 + 3798382 * 2 ^ 59
def prefixEnd_3798382 : Nat := 4983230072969 + 3 ^ 40 * 3798382 * 2
def baseEnd_3798382 : Nat := 433421261196947343701459

theorem tailTrace_3798382 : CollatzResearch.WordTrace tailWord_3798382 prefixEnd_3798382 433421261196947343701459 := by
  unfold tailWord_3798382
  simp only [CollatzResearch.WordTrace]
  refine ⟨17317296615639775105513675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92358915283412133896072933 17317296615639775105513675)
  ·
    refine ⟨25975944923459662658270513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17317296615639775105513675 25975944923459662658270513)
    ·
      refine ⟨19481958692594746993702885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25975944923459662658270513 19481958692594746993702885)
      ·
        refine ⟨3652867254861515061319291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19481958692594746993702885 3652867254861515061319291)
        ·
          refine ⟨5479300882292272591978937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652867254861515061319291 5479300882292272591978937)
          ·
            refine ⟨4109475661719204443984203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5479300882292272591978937 4109475661719204443984203)
            ·
              refine ⟨6164213492578806665976305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4109475661719204443984203 6164213492578806665976305)
              ·
                refine ⟨4623160119434104999482229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6164213492578806665976305 4623160119434104999482229)
                ·
                  refine ⟨433421261196947343701459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4623160119434104999482229 433421261196947343701459)
                  ·
                    rfl

theorem cell22_3798382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_3798382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798382 prefixEnd_3798382 := by exact prefixLift 3798382
  have htrace : WordTrace (prefixWord ++ tailWord_3798382) baseStart_3798382 baseEnd_3798382 := by
    simpa [prefixWord, tailWord_3798382, baseEnd_3798382] using wordTrace_append hprefix tailTrace_3798382
  have hstable : (prefixWord ++ tailWord_3798382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798382).length < 2 ^ (prefixWord ++ tailWord_3798382).sum := by decide
  have hdescent : baseEnd_3798382 < baseStart_3798382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798393 : List Nat := [1, 2, 1, 3, 2, 1, 4, 4, 4]
def baseStart_3798393 : Nat := 118140960795 + 3798393 * 2 ^ 59
def prefixEnd_3798393 : Nat := 4983230072969 + 3 ^ 40 * 3798393 * 2
def baseEnd_3798393 : Nat := 433422516371880556359781

theorem tailTrace_3798393 : CollatzResearch.WordTrace tailWord_3798393 prefixEnd_3798393 433422516371880556359781 := by
  unfold tailWord_3798393
  simp only [CollatzResearch.WordTrace]
  refine ⟨138538774128078349722759833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92359182752052233148506555 138538774128078349722759833)
  ·
    refine ⟨103904080596058762292069875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138538774128078349722759833 103904080596058762292069875)
    ·
      refine ⟨155856120894088143438104813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103904080596058762292069875 155856120894088143438104813)
      ·
        refine ⟨58446045335283053789289305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155856120894088143438104813 58446045335283053789289305)
        ·
          refine ⟨43834534001462290341966979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58446045335283053789289305 43834534001462290341966979)
          ·
            refine ⟨65751801002193435512950469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43834534001462290341966979 65751801002193435512950469)
            ·
              refine ⟨12328462687911269158678213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65751801002193435512950469 12328462687911269158678213)
              ·
                refine ⟨2311586753983362967252165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12328462687911269158678213 2311586753983362967252165)
                ·
                  refine ⟨433422516371880556359781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311586753983362967252165 433422516371880556359781)
                  ·
                    rfl

theorem cell22_3798393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 4].length) (baseStart_3798393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798393 prefixEnd_3798393 := by exact prefixLift 3798393
  have htrace : WordTrace (prefixWord ++ tailWord_3798393) baseStart_3798393 baseEnd_3798393 := by
    simpa [prefixWord, tailWord_3798393, baseEnd_3798393] using wordTrace_append hprefix tailTrace_3798393
  have hstable : (prefixWord ++ tailWord_3798393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798393).length < 2 ^ (prefixWord ++ tailWord_3798393).sum := by decide
  have hdescent : baseEnd_3798393 < baseStart_3798393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798408 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 1, 5]
def baseStart_3798408 : Nat := 118140960795 + 3798408 * 2 ^ 59
def prefixEnd_3798408 : Nat := 4983230072969 + 3 ^ 40 * 3798408 * 2
def baseEnd_3798408 : Nat := 1300272683922186629954297

theorem tailTrace_3798408 : CollatzResearch.WordTrace tailWord_3798408 prefixEnd_3798408 1300272683922186629954297 := by
  unfold tailWord_3798408
  simp only [CollatzResearch.WordTrace]
  refine ⟨69269660611512003642277939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92359547482016004856370585 69269660611512003642277939)
  ·
    refine ⟨103904490917268005463416909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69269660611512003642277939 103904490917268005463416909)
    ·
      refine ⟨38964184093975502048781341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103904490917268005463416909 38964184093975502048781341)
      ·
        refine ⟨14611569035240813268293003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38964184093975502048781341 14611569035240813268293003)
        ·
          refine ⟨21917353552861219902439505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14611569035240813268293003 21917353552861219902439505)
          ·
            refine ⟨16438015164645914926829629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21917353552861219902439505 16438015164645914926829629)
            ·
              refine ⟨6164255686742218097561111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16438015164645914926829629 6164255686742218097561111)
              ·
                refine ⟨9246383530113327146341667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6164255686742218097561111 9246383530113327146341667)
                ·
                  refine ⟨13869575295169990719512501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9246383530113327146341667 13869575295169990719512501)
                  ·
                    refine ⟨1300272683922186629954297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13869575295169990719512501 1300272683922186629954297)
                    ·
                      rfl

theorem cell22_3798408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_3798408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798408 prefixEnd_3798408 := by exact prefixLift 3798408
  have htrace : WordTrace (prefixWord ++ tailWord_3798408) baseStart_3798408 baseEnd_3798408 := by
    simpa [prefixWord, tailWord_3798408, baseEnd_3798408] using wordTrace_append hprefix tailTrace_3798408
  have hstable : (prefixWord ++ tailWord_3798408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798408).length < 2 ^ (prefixWord ++ tailWord_3798408).sum := by decide
  have hdescent : baseEnd_3798408 < baseStart_3798408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3798481 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_3798481 : Nat := 118140960795 + 3798481 * 2 ^ 59
def prefixEnd_3798481 : Nat := 4983230072969 + 3 ^ 40 * 3798481 * 2
def baseEnd_3798481 : Nat := 1300297673314038772879073

theorem tailTrace_3798481 : CollatzResearch.WordTrace tailWord_3798481 prefixEnd_3798481 1300297673314038772879073 := by
  unfold tailWord_3798481
  simp only [CollatzResearch.WordTrace]
  refine ⟨138541983751759540751963297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92361322501173027167975531 138541983751759540751963297)
  ·
    refine ⟨103906487813819655563972473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138541983751759540751963297 103906487813819655563972473)
    ·
      refine ⟨77929865860364741672979355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103906487813819655563972473 77929865860364741672979355)
      ·
        refine ⟨116894798790547112509469033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77929865860364741672979355 116894798790547112509469033)
        ·
          refine ⟨87671099092910334382101775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116894798790547112509469033 87671099092910334382101775)
          ·
            refine ⟨131506648639365501573152663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87671099092910334382101775 131506648639365501573152663)
            ·
              refine ⟨197259972959048252359728995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131506648639365501573152663 197259972959048252359728995)
              ·
                refine ⟨295889959438572378539593493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197259972959048252359728995 295889959438572378539593493)
                ·
                  refine ⟨13869841848683080244043445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 295889959438572378539593493 13869841848683080244043445)
                  ·
                    refine ⟨1300297673314038772879073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13869841848683080244043445 1300297673314038772879073)
                    ·
                      rfl

theorem cell22_3798481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_3798481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3798481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3798481 prefixEnd_3798481 := by exact prefixLift 3798481
  have htrace : WordTrace (prefixWord ++ tailWord_3798481) baseStart_3798481 baseEnd_3798481 := by
    simpa [prefixWord, tailWord_3798481, baseEnd_3798481] using wordTrace_append hprefix tailTrace_3798481
  have hstable : (prefixWord ++ tailWord_3798481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3798481).length < 2 ^ (prefixWord ++ tailWord_3798481).sum := by decide
  have hdescent : baseEnd_3798481 < baseStart_3798481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3798481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
