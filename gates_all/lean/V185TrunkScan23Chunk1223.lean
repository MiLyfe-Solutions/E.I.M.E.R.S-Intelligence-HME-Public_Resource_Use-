import V185TrunkScan23Chunk1222

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7247118 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_7247118 : Nat := 118140960795 + 7247118 * 2 ^ 59
def prefixEnd_7247118 : Nat := 4983230072969 + 3 ^ 40 * 7247118 * 2
def baseEnd_7247118 : Nat := 3721254893850481851196117

theorem tailTrace_7247118 : CollatzResearch.WordTrace tailWord_7247118 prefixEnd_7247118 3721254893850481851196117 := by
  unfold tailWord_7247118
  simp only [CollatzResearch.WordTrace]
  refine ⟨33040513569867083757555751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176216072372624446706964005 33040513569867083757555751)
  ·
    refine ⟨49560770354800625636333627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33040513569867083757555751 49560770354800625636333627)
    ·
      refine ⟨74341155532200938454500441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49560770354800625636333627 74341155532200938454500441)
      ·
        refine ⟨55755866649150703840875331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74341155532200938454500441 55755866649150703840875331)
        ·
          refine ⟨83633799973726055761312997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55755866649150703840875331 83633799973726055761312997)
          ·
            refine ⟨15681337495073635455246187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83633799973726055761312997 15681337495073635455246187)
            ·
              refine ⟨23522006242610453182869281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15681337495073635455246187 23522006242610453182869281)
              ·
                refine ⟨17641504681957839887151961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23522006242610453182869281 17641504681957839887151961)
                ·
                  refine ⟨13231128511468379915363971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17641504681957839887151961 13231128511468379915363971)
                  ·
                    refine ⟨19846692767202569873045957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13231128511468379915363971 19846692767202569873045957)
                    ·
                      refine ⟨3721254893850481851196117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19846692767202569873045957 3721254893850481851196117)
                      ·
                        rfl

theorem cell23_7247118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_7247118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247118 prefixEnd_7247118 := by exact prefixLift 7247118
  have htrace : WordTrace (prefixWord ++ tailWord_7247118) baseStart_7247118 baseEnd_7247118 := by
    simpa [prefixWord, tailWord_7247118, baseEnd_7247118] using wordTrace_append hprefix tailTrace_7247118
  have hstable : (prefixWord ++ tailWord_7247118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247118).length < 2 ^ (prefixWord ++ tailWord_7247118).sum := by decide
  have hdescent : baseEnd_7247118 < baseStart_7247118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247128 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 3, 4]
def baseStart_7247128 : Nat := 118140960795 + 7247128 * 2 ^ 59
def prefixEnd_7247128 : Nat := 4983230072969 + 3 ^ 40 * 7247128 * 2
def baseEnd_7247128 : Nat := 1240420009552342270690357

theorem tailTrace_7247128 : CollatzResearch.WordTrace tailWord_7247128 prefixEnd_7247128 1240420009552342270690357 := by
  unfold tailWord_7247128
  simp only [CollatzResearch.WordTrace]
  refine ⟨132162236644450220884155019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176216315525933627845540025 132162236644450220884155019)
  ·
    refine ⟨198243354966675331326232529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132162236644450220884155019 198243354966675331326232529)
    ·
      refine ⟨148682516225006498494674397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198243354966675331326232529 148682516225006498494674397)
      ·
        refine ⟨55755943584377436935502899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148682516225006498494674397 55755943584377436935502899)
        ·
          refine ⟨83633915376566155403254349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55755943584377436935502899 83633915376566155403254349)
          ·
            refine ⟨31362718266212308276220381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83633915376566155403254349 31362718266212308276220381)
            ·
              refine ⟨11761019349829615603582643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31362718266212308276220381 11761019349829615603582643)
              ·
                refine ⟨17641529024744423405373965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11761019349829615603582643 17641529024744423405373965)
                ·
                  refine ⟨6615573384279158777015237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17641529024744423405373965 6615573384279158777015237)
                  ·
                    refine ⟨1240420009552342270690357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6615573384279158777015237 1240420009552342270690357)
                    ·
                      rfl

theorem cell23_7247128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_7247128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247128 prefixEnd_7247128 := by exact prefixLift 7247128
  have htrace : WordTrace (prefixWord ++ tailWord_7247128) baseStart_7247128 baseEnd_7247128 := by
    simpa [prefixWord, tailWord_7247128, baseEnd_7247128] using wordTrace_append hprefix tailTrace_7247128
  have hstable : (prefixWord ++ tailWord_7247128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247128).length < 2 ^ (prefixWord ++ tailWord_7247128).sum := by decide
  have hdescent : baseEnd_7247128 < baseStart_7247128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247212 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 2, 3, 2]
def baseStart_7247212 : Nat := 118140960795 + 7247212 * 2 ^ 59
def prefixEnd_7247212 : Nat := 4983230072969 + 3 ^ 40 * 7247212 * 2
def baseEnd_7247212 : Nat := 3721303161032004483420685

theorem tailTrace_7247212 : CollatzResearch.WordTrace tailWord_7247212 prefixEnd_7247212 3721303161032004483420685 := by
  unfold tailWord_7247212
  simp only [CollatzResearch.WordTrace]
  refine ⟨132163768510298062057183945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176218358013730749409578593 132163768510298062057183945)
  ·
    refine ⟨99122826382723546542887959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132163768510298062057183945 99122826382723546542887959)
    ·
      refine ⟨148684239574085319814331939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99122826382723546542887959 148684239574085319814331939)
      ·
        refine ⟨223026359361127979721497909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148684239574085319814331939 223026359361127979721497909)
        ·
          refine ⟨20908721190105748098890429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223026359361127979721497909 20908721190105748098890429)
          ·
            refine ⟨7840770446289655537083911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20908721190105748098890429 7840770446289655537083911)
            ·
              refine ⟨11761155669434483305625867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7840770446289655537083911 11761155669434483305625867)
              ·
                refine ⟨17641733504151724958438801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11761155669434483305625867 17641733504151724958438801)
                ·
                  refine ⟨13231300128113793718829101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17641733504151724958438801 13231300128113793718829101)
                  ·
                    refine ⟨4961737548042672644560913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13231300128113793718829101 4961737548042672644560913)
                    ·
                      refine ⟨3721303161032004483420685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4961737548042672644560913 3721303161032004483420685)
                      ·
                        rfl

theorem cell23_7247212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 3, 2].length) (baseStart_7247212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247212 prefixEnd_7247212 := by exact prefixLift 7247212
  have htrace : WordTrace (prefixWord ++ tailWord_7247212) baseStart_7247212 baseEnd_7247212 := by
    simpa [prefixWord, tailWord_7247212, baseEnd_7247212] using wordTrace_append hprefix tailTrace_7247212
  have hstable : (prefixWord ++ tailWord_7247212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247212).length < 2 ^ (prefixWord ++ tailWord_7247212).sum := by decide
  have hdescent : baseEnd_7247212 < baseStart_7247212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247218 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_7247218 : Nat := 118140960795 + 7247218 * 2 ^ 59
def prefixEnd_7247218 : Nat := 4983230072969 + 3 ^ 40 * 7247218 * 2
def baseEnd_7247218 : Nat := 1240435413971977153315219

theorem tailTrace_7247218 : CollatzResearch.WordTrace tailWord_7247218 prefixEnd_7247218 1240435413971977153315219 := by
  unfold tailWord_7247218
  simp only [CollatzResearch.WordTrace]
  refine ⟨66081938964643596784771577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176218503905716258092724205 66081938964643596784771577)
  ·
    refine ⟨49561454223482697588578683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66081938964643596784771577 49561454223482697588578683)
    ·
      refine ⟨74342181335224046382868025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49561454223482697588578683 74342181335224046382868025)
      ·
        refine ⟨55756636001418034787151019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74342181335224046382868025 55756636001418034787151019)
        ·
          refine ⟨83634954002127052180726529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55756636001418034787151019 83634954002127052180726529)
          ·
            refine ⟨62726215501595289135544897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83634954002127052180726529 62726215501595289135544897)
            ·
              refine ⟨47044661626196466851658673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62726215501595289135544897 47044661626196466851658673)
              ·
                refine ⟨35283496219647350138744005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47044661626196466851658673 35283496219647350138744005)
                ·
                  refine ⟨6615655541183878151014501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35283496219647350138744005 6615655541183878151014501)
                  ·
                    refine ⟨1240435413971977153315219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6615655541183878151014501 1240435413971977153315219)
                    ·
                      rfl

theorem cell23_7247218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_7247218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247218 prefixEnd_7247218 := by exact prefixLift 7247218
  have htrace : WordTrace (prefixWord ++ tailWord_7247218) baseStart_7247218 baseEnd_7247218 := by
    simpa [prefixWord, tailWord_7247218, baseEnd_7247218] using wordTrace_append hprefix tailTrace_7247218
  have hstable : (prefixWord ++ tailWord_7247218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247218).length < 2 ^ (prefixWord ++ tailWord_7247218).sum := by decide
  have hdescent : baseEnd_7247218 < baseStart_7247218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247225 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 1, 1, 4]
def baseStart_7247225 : Nat := 118140960795 + 7247225 * 2 ^ 59
def prefixEnd_7247225 : Nat := 4983230072969 + 3 ^ 40 * 7247225 * 2
def baseEnd_7247225 : Nat := 3721309836280512932558125

theorem tailTrace_7247225 : CollatzResearch.WordTrace tailWord_7247225 prefixEnd_7247225 3721309836280512932558125 := by
  unfold tailWord_7247225
  simp only [CollatzResearch.WordTrace]
  refine ⟨264328011169549027334591129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176218674113032684889727419 264328011169549027334591129)
  ·
    refine ⟨198246008377161770500943347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264328011169549027334591129 198246008377161770500943347)
    ·
      refine ⟨297369012565742655751415021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198246008377161770500943347 297369012565742655751415021)
      ·
        refine ⟨111513379712153495906780633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297369012565742655751415021 111513379712153495906780633)
        ·
          refine ⟨83635034784115121930085475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111513379712153495906780633 83635034784115121930085475)
          ·
            refine ⟨125452552176172682895128213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83635034784115121930085475 125452552176172682895128213)
            ·
              refine ⟨5880588383258094510709135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125452552176172682895128213 5880588383258094510709135)
              ·
                refine ⟨8820882574887141766063703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5880588383258094510709135 8820882574887141766063703)
                ·
                  refine ⟨13231323862330712649095555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8820882574887141766063703 13231323862330712649095555)
                  ·
                    refine ⟨19846985793496068973643333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13231323862330712649095555 19846985793496068973643333)
                    ·
                      refine ⟨3721309836280512932558125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19846985793496068973643333 3721309836280512932558125)
                      ·
                        rfl

theorem cell23_7247225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_7247225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247225 prefixEnd_7247225 := by exact prefixLift 7247225
  have htrace : WordTrace (prefixWord ++ tailWord_7247225) baseStart_7247225 baseEnd_7247225 := by
    simpa [prefixWord, tailWord_7247225, baseEnd_7247225] using wordTrace_append hprefix tailTrace_7247225
  have hstable : (prefixWord ++ tailWord_7247225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247225).length < 2 ^ (prefixWord ++ tailWord_7247225).sum := by decide
  have hdescent : baseEnd_7247225 < baseStart_7247225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247235 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 2, 4]
def baseStart_7247235 : Nat := 118140960795 + 7247235 * 2 ^ 59
def prefixEnd_7247235 : Nat := 4983230072969 + 3 ^ 40 * 7247235 * 2
def baseEnd_7247235 : Nat := 1240438323695685964477693

theorem tailTrace_7247235 : CollatzResearch.WordTrace tailWord_7247235 prefixEnd_7247235 1240438323695685964477693 := by
  unfold tailWord_7247235
  simp only [CollatzResearch.WordTrace]
  refine ⟨264328375899512799042455159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176218917266341866028303439 264328375899512799042455159)
  ·
    refine ⟨396492563849269198563682739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264328375899512799042455159 396492563849269198563682739)
    ·
      refine ⟨594738845773903797845524109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396492563849269198563682739 594738845773903797845524109)
      ·
        refine ⟨223027067165213924192071541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594738845773903797845524109 223027067165213924192071541)
        ·
          refine ⟨20908787546738805393006707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223027067165213924192071541 20908787546738805393006707)
          ·
            refine ⟨31363181320108208089510061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20908787546738805393006707 31363181320108208089510061)
            ·
              refine ⟨11761192995040578033566273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31363181320108208089510061 11761192995040578033566273)
              ·
                refine ⟨8820894746280433525174705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11761192995040578033566273 8820894746280433525174705)
                ·
                  refine ⟨6615671059710325143881029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8820894746280433525174705 6615671059710325143881029)
                  ·
                    refine ⟨1240438323695685964477693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6615671059710325143881029 1240438323695685964477693)
                    ·
                      rfl

theorem cell23_7247235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 4].length) (baseStart_7247235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247235 prefixEnd_7247235 := by exact prefixLift 7247235
  have htrace : WordTrace (prefixWord ++ tailWord_7247235) baseStart_7247235 baseEnd_7247235 := by
    simpa [prefixWord, tailWord_7247235, baseEnd_7247235] using wordTrace_append hprefix tailTrace_7247235
  have hstable : (prefixWord ++ tailWord_7247235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247235).length < 2 ^ (prefixWord ++ tailWord_7247235).sum := by decide
  have hdescent : baseEnd_7247235 < baseStart_7247235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247362 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7247362 : Nat := 118140960795 + 7247362 * 2 ^ 59
def prefixEnd_7247362 : Nat := 4983230072969 + 3 ^ 40 * 7247362 * 2
def baseEnd_7247362 : Nat := 3721380183130178896544995

theorem tailTrace_7247362 : CollatzResearch.WordTrace tailWord_7247362 prefixEnd_7247362 3721380183130178896544995 := by
  unfold tailWord_7247362
  simp only [CollatzResearch.WordTrace]
  refine ⟨66083251992513174933082085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176222005313368466488218893 66083251992513174933082085)
  ·
    refine ⟨12390609748596220299952891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66083251992513174933082085 12390609748596220299952891)
    ·
      refine ⟨18585914622894330449929337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12390609748596220299952891 18585914622894330449929337)
      ·
        refine ⟨13939435967170747837447003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18585914622894330449929337 13939435967170747837447003)
        ·
          refine ⟨20909153950756121756170505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13939435967170747837447003 20909153950756121756170505)
          ·
            refine ⟨15681865463067091317127879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20909153950756121756170505 15681865463067091317127879)
            ·
              refine ⟨23522798194600636975691819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15681865463067091317127879 23522798194600636975691819)
              ·
                refine ⟨35284197291900955463537729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23522798194600636975691819 35284197291900955463537729)
                ·
                  refine ⟨26463147968925716597653297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35284197291900955463537729 26463147968925716597653297)
                  ·
                    refine ⟨19847360976694287448239973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26463147968925716597653297 19847360976694287448239973)
                    ·
                      refine ⟨3721380183130178896544995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19847360976694287448239973 3721380183130178896544995)
                      ·
                        rfl

theorem cell23_7247362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7247362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247362 prefixEnd_7247362 := by exact prefixLift 7247362
  have htrace : WordTrace (prefixWord ++ tailWord_7247362) baseStart_7247362 baseEnd_7247362 := by
    simpa [prefixWord, tailWord_7247362, baseEnd_7247362] using wordTrace_append hprefix tailTrace_7247362
  have hstable : (prefixWord ++ tailWord_7247362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247362).length < 2 ^ (prefixWord ++ tailWord_7247362).sum := by decide
  have hdescent : baseEnd_7247362 < baseStart_7247362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247368 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 4, 5]
def baseStart_7247368 : Nat := 118140960795 + 7247368 * 2 ^ 59
def prefixEnd_7247368 : Nat := 4983230072969 + 3 ^ 40 * 7247368 * 2
def baseEnd_7247368 : Nat := 1240461088004701957689989

theorem tailTrace_7247368 : CollatzResearch.WordTrace tailWord_7247368 prefixEnd_7247368 1240461088004701957689989 := by
  unfold tailWord_7247368
  simp only [CollatzResearch.WordTrace]
  refine ⟨132166613404015481378523379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176222151205353975171364505 132166613404015481378523379)
  ·
    refine ⟨198249920106023222067785069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132166613404015481378523379 198249920106023222067785069)
    ·
      refine ⟨74343720039758708275419401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198249920106023222067785069 74343720039758708275419401)
      ·
        refine ⟨55757790029819031206564551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74343720039758708275419401 55757790029819031206564551)
        ·
          refine ⟨83636685044728546809846827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55757790029819031206564551 83636685044728546809846827)
          ·
            refine ⟨125455027567092820214770241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83636685044728546809846827 125455027567092820214770241)
            ·
              refine ⟨94091270675319615161077681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125455027567092820214770241 94091270675319615161077681)
              ·
                refine ⟨70568453006489711370808261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94091270675319615161077681 70568453006489711370808261)
                ·
                  refine ⟨13231584938716820882026549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70568453006489711370808261 13231584938716820882026549)
                  ·
                    refine ⟨1240461088004701957689989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13231584938716820882026549 1240461088004701957689989)
                    ·
                      rfl

theorem cell23_7247368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_7247368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247368 prefixEnd_7247368 := by exact prefixLift 7247368
  have htrace : WordTrace (prefixWord ++ tailWord_7247368) baseStart_7247368 baseEnd_7247368 := by
    simpa [prefixWord, tailWord_7247368, baseEnd_7247368] using wordTrace_append hprefix tailTrace_7247368
  have hstable : (prefixWord ++ tailWord_7247368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247368).length < 2 ^ (prefixWord ++ tailWord_7247368).sum := by decide
  have hdescent : baseEnd_7247368 < baseStart_7247368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247415 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 3, 4]
def baseStart_7247415 : Nat := 118140960795 + 7247415 * 2 ^ 59
def prefixEnd_7247415 : Nat := 4983230072969 + 3 ^ 40 * 7247415 * 2
def baseEnd_7247415 : Nat := 1240469132534955729727417

theorem tailTrace_7247415 : CollatzResearch.WordTrace tailWord_7247415 prefixEnd_7247415 1240469132534955729727417 := by
  unfold tailWord_7247415
  simp only [CollatzResearch.WordTrace]
  refine ⟨264334941038860689784007699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176223294025907126522671799 264334941038860689784007699)
  ·
    refine ⟨396502411558291034676011549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264334941038860689784007699 396502411558291034676011549)
    ·
      refine ⟨148688404334359138003504331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396502411558291034676011549 148688404334359138003504331)
      ·
        refine ⟨223032606501538707005256497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148688404334359138003504331 223032606501538707005256497)
        ·
          refine ⟨167274454876154030253942373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223032606501538707005256497 167274454876154030253942373)
          ·
            refine ⟨31363960289278880672614195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167274454876154030253942373 31363960289278880672614195)
            ·
              refine ⟨47045940433918321008921293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31363960289278880672614195 47045940433918321008921293)
              ·
                refine ⟨17642227662719370378345485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47045940433918321008921293 17642227662719370378345485)
                ·
                  refine ⟨6615835373519763891879557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17642227662719370378345485 6615835373519763891879557)
                  ·
                    refine ⟨1240469132534955729727417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6615835373519763891879557 1240469132534955729727417)
                    ·
                      rfl

theorem cell23_7247415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_7247415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247415 prefixEnd_7247415 := by exact prefixLift 7247415
  have htrace : WordTrace (prefixWord ++ tailWord_7247415) baseStart_7247415 baseEnd_7247415 := by
    simpa [prefixWord, tailWord_7247415, baseEnd_7247415] using wordTrace_append hprefix tailTrace_7247415
  have hstable : (prefixWord ++ tailWord_7247415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247415).length < 2 ^ (prefixWord ++ tailWord_7247415).sum := by decide
  have hdescent : baseEnd_7247415 < baseStart_7247415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247418 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_7247418 : Nat := 118140960795 + 7247418 * 2 ^ 59
def prefixEnd_7247418 : Nat := 4983230072969 + 3 ^ 40 * 7247418 * 2
def baseEnd_7247418 : Nat := 3721408938046830677444737

theorem tailTrace_7247418 : CollatzResearch.WordTrace tailWord_7247418 prefixEnd_7247418 3721408938046830677444737 := by
  unfold tailWord_7247418
  simp only [CollatzResearch.WordTrace]
  refine ⟨66083762614462455324091727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176223366971899880864244605 66083762614462455324091727)
  ·
    refine ⟨99125643921693682986137591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66083762614462455324091727 99125643921693682986137591)
    ·
      refine ⟨148688465882540524479206387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99125643921693682986137591 148688465882540524479206387)
      ·
        refine ⟨223032698823810786718809581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148688465882540524479206387 223032698823810786718809581)
        ·
          refine ⟨83637262058929045019553593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223032698823810786718809581 83637262058929045019553593)
          ·
            refine ⟨62727946544196783764665195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83637262058929045019553593 62727946544196783764665195)
            ·
              refine ⟨94091919816295175646997793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62727946544196783764665195 94091919816295175646997793)
              ·
                refine ⟨70568939862221381735248345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94091919816295175646997793 70568939862221381735248345)
                ·
                  refine ⟨52926704896666036301436259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70568939862221381735248345 52926704896666036301436259)
                  ·
                    refine ⟨79390057344999054452154389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52926704896666036301436259 79390057344999054452154389)
                    ·
                      refine ⟨3721408938046830677444737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79390057344999054452154389 3721408938046830677444737)
                      ·
                        rfl

theorem cell23_7247418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_7247418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247418 prefixEnd_7247418 := by exact prefixLift 7247418
  have htrace : WordTrace (prefixWord ++ tailWord_7247418) baseStart_7247418 baseEnd_7247418 := by
    simpa [prefixWord, tailWord_7247418, baseEnd_7247418] using wordTrace_append hprefix tailTrace_7247418
  have hstable : (prefixWord ++ tailWord_7247418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247418).length < 2 ^ (prefixWord ++ tailWord_7247418).sum := by decide
  have hdescent : baseEnd_7247418 < baseStart_7247418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247425 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_7247425 : Nat := 118140960795 + 7247425 * 2 ^ 59
def prefixEnd_7247425 : Nat := 4983230072969 + 3 ^ 40 * 7247425 * 2
def baseEnd_7247425 : Nat := 3721412532411412150057205

theorem tailTrace_7247425 : CollatzResearch.WordTrace tailWord_7247425 prefixEnd_7247425 3721412532411412150057205 := by
  unfold tailWord_7247425
  simp only [CollatzResearch.WordTrace]
  refine ⟨264335305768824461491871729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176223537179216307661247819 264335305768824461491871729)
  ·
    refine ⟨198251479326618346118903797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264335305768824461491871729 198251479326618346118903797)
    ·
      refine ⟨18586076186870469948647231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198251479326618346118903797 18586076186870469948647231)
      ·
        refine ⟨27879114280305704922970847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18586076186870469948647231 27879114280305704922970847)
        ·
          refine ⟨41818671420458557384456271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27879114280305704922970847 41818671420458557384456271)
          ·
            refine ⟨62728007130687836076684407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41818671420458557384456271 62728007130687836076684407)
            ·
              refine ⟨94092010696031754115026611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62728007130687836076684407 94092010696031754115026611)
              ·
                refine ⟨141138016044047631172539917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94092010696031754115026611 141138016044047631172539917)
                ·
                  refine ⟨52926756016517861689702469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141138016044047631172539917 52926756016517861689702469)
                  ·
                    refine ⟨9923766753097099066819213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52926756016517861689702469 9923766753097099066819213)
                    ·
                      refine ⟨3721412532411412150057205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9923766753097099066819213 3721412532411412150057205)
                      ·
                        rfl

theorem cell23_7247425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_7247425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247425 prefixEnd_7247425 := by exact prefixLift 7247425
  have htrace : WordTrace (prefixWord ++ tailWord_7247425) baseStart_7247425 baseEnd_7247425 := by
    simpa [prefixWord, tailWord_7247425, baseEnd_7247425] using wordTrace_append hprefix tailTrace_7247425
  have hstable : (prefixWord ++ tailWord_7247425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247425).length < 2 ^ (prefixWord ++ tailWord_7247425).sum := by decide
  have hdescent : baseEnd_7247425 < baseStart_7247425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247466 : List Nat := [3, 1, 3, 2, 1, 3, 3, 2, 1, 4]
def baseStart_7247466 : Nat := 118140960795 + 7247466 * 2 ^ 59
def prefixEnd_7247466 : Nat := 4983230072969 + 3 ^ 40 * 7247466 * 2
def baseEnd_7247466 : Nat := 1240477861706082163214839

theorem tailTrace_7247466 : CollatzResearch.WordTrace tailWord_7247466 prefixEnd_7247466 1240477861706082163214839 := by
  unfold tailWord_7247466
  simp only [CollatzResearch.WordTrace]
  refine ⟨66084200290418981373528563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176224534107783950329409501 66084200290418981373528563)
  ·
    refine ⟨99126300435628472060292845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66084200290418981373528563 99126300435628472060292845)
    ·
      refine ⟨37172362663360677022609817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99126300435628472060292845 37172362663360677022609817)
      ·
        refine ⟨27879271997520507766957363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37172362663360677022609817 27879271997520507766957363)
        ·
          refine ⟨41818907996280761650436045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27879271997520507766957363 41818907996280761650436045)
          ·
            refine ⟨15682090498605285618913517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41818907996280761650436045 15682090498605285618913517)
            ·
              refine ⟨5880783936976982107092569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15682090498605285618913517 5880783936976982107092569)
              ·
                refine ⟨4410587952732736580319427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880783936976982107092569 4410587952732736580319427)
                ·
                  refine ⟨6615881929099104870479141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410587952732736580319427 6615881929099104870479141)
                  ·
                    refine ⟨1240477861706082163214839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6615881929099104870479141 1240477861706082163214839)
                    ·
                      rfl

theorem cell23_7247466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_7247466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247466 prefixEnd_7247466 := by exact prefixLift 7247466
  have htrace : WordTrace (prefixWord ++ tailWord_7247466) baseStart_7247466 baseEnd_7247466 := by
    simpa [prefixWord, tailWord_7247466, baseEnd_7247466] using wordTrace_append hprefix tailTrace_7247466
  have hstable : (prefixWord ++ tailWord_7247466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247466).length < 2 ^ (prefixWord ++ tailWord_7247466).sum := by decide
  have hdescent : baseEnd_7247466 < baseStart_7247466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247468 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_7247468 : Nat := 118140960795 + 7247468 * 2 ^ 59
def prefixEnd_7247468 : Nat := 4983230072969 + 3 ^ 40 * 7247468 * 2
def baseEnd_7247468 : Nat := 3721434612079555481819507

theorem tailTrace_7247468 : CollatzResearch.WordTrace tailWord_7247468 prefixEnd_7247468 3721434612079555481819507 := by
  unfold tailWord_7247468
  simp only [CollatzResearch.WordTrace]
  refine ⟨132168437053834339917843529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176224582738445786557124705 132168437053834339917843529)
  ·
    refine ⟨99126327790375754938382647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132168437053834339917843529 99126327790375754938382647)
    ·
      refine ⟨148689491685563632407573971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99126327790375754938382647 148689491685563632407573971)
      ·
        refine ⟨223034237528345448611360957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148689491685563632407573971 223034237528345448611360957)
        ·
          refine ⟨83637839073129543229260359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223034237528345448611360957 83637839073129543229260359)
          ·
            refine ⟨125456758609694314843890539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83637839073129543229260359 125456758609694314843890539)
            ·
              refine ⟨188185137914541472265835809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125456758609694314843890539 188185137914541472265835809)
              ·
                refine ⟨141138853435906104199376857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188185137914541472265835809 141138853435906104199376857)
                ·
                  refine ⟨105854140076929578149532643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141138853435906104199376857 105854140076929578149532643)
                  ·
                    refine ⟨158781210115394367224298965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105854140076929578149532643 158781210115394367224298965)
                    ·
                      refine ⟨3721434612079555481819507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158781210115394367224298965 3721434612079555481819507)
                      ·
                        rfl

theorem cell23_7247468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_7247468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247468 prefixEnd_7247468 := by exact prefixLift 7247468
  have htrace : WordTrace (prefixWord ++ tailWord_7247468) baseStart_7247468 baseEnd_7247468 := by
    simpa [prefixWord, tailWord_7247468, baseEnd_7247468] using wordTrace_append hprefix tailTrace_7247468
  have hstable : (prefixWord ++ tailWord_7247468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247468).length < 2 ^ (prefixWord ++ tailWord_7247468).sum := by decide
  have hdescent : baseEnd_7247468 < baseStart_7247468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247492 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_7247492 : Nat := 118140960795 + 7247492 * 2 ^ 59
def prefixEnd_7247492 : Nat := 4983230072969 + 3 ^ 40 * 7247492 * 2
def baseEnd_7247492 : Nat := 1240482311871754462639799

theorem tailTrace_7247492 : CollatzResearch.WordTrace tailWord_7247492 prefixEnd_7247492 1240482311871754462639799 := by
  unfold tailWord_7247492
  simp only [CollatzResearch.WordTrace]
  refine ⟨132168874729790865967280365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176225166306387821289707153 132168874729790865967280365)
  ·
    refine ⟨49563328023671574737730137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132168874729790865967280365 49563328023671574737730137)
    ·
      refine ⟨37172496017753681053297603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49563328023671574737730137 37172496017753681053297603)
      ·
        refine ⟨55758744026630521579946405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37172496017753681053297603 55758744026630521579946405)
        ·
          refine ⟨10454764504993222796239951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55758744026630521579946405 10454764504993222796239951)
          ·
            refine ⟨15682146757489834194359927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10454764504993222796239951 15682146757489834194359927)
            ·
              refine ⟨23523220136234751291539891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15682146757489834194359927 23523220136234751291539891)
              ·
                refine ⟨35284830204352126937309837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23523220136234751291539891 35284830204352126937309837)
                ·
                  refine ⟨13231811326632047601491189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35284830204352126937309837 13231811326632047601491189)
                  ·
                    refine ⟨1240482311871754462639799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13231811326632047601491189 1240482311871754462639799)
                    ·
                      rfl

theorem cell23_7247492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_7247492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247492 prefixEnd_7247492 := by exact prefixLift 7247492
  have htrace : WordTrace (prefixWord ++ tailWord_7247492) baseStart_7247492 baseEnd_7247492 := by
    simpa [prefixWord, tailWord_7247492, baseEnd_7247492] using wordTrace_append hprefix tailTrace_7247492
  have hstable : (prefixWord ++ tailWord_7247492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247492).length < 2 ^ (prefixWord ++ tailWord_7247492).sum := by decide
  have hdescent : baseEnd_7247492 < baseStart_7247492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247505 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 4, 4]
def baseStart_7247505 : Nat := 118140960795 + 7247505 * 2 ^ 59
def prefixEnd_7247505 : Nat := 4983230072969 + 3 ^ 40 * 7247505 * 2
def baseEnd_7247505 : Nat := 1240484536954590612352279

theorem tailTrace_7247505 : CollatzResearch.WordTrace tailWord_7247505 prefixEnd_7247505 1240484536954590612352279 := by
  unfold tailWord_7247505
  simp only [CollatzResearch.WordTrace]
  refine ⟨264338223608534635154783969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176225482405689756769855979 264338223608534635154783969)
  ·
    refine ⟨198253667706400976366087977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264338223608534635154783969 198253667706400976366087977)
    ·
      refine ⟨148690250779800732274565983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198253667706400976366087977 148690250779800732274565983)
      ·
        refine ⟨223035376169701098411848975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148690250779800732274565983 223035376169701098411848975)
        ·
          refine ⟨334553064254551647617773463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223035376169701098411848975 334553064254551647617773463)
          ·
            refine ⟨501829596381827471426660195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334553064254551647617773463 501829596381827471426660195)
            ·
              refine ⟨752744394572741207139990293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501829596381827471426660195 752744394572741207139990293)
              ·
                refine ⟨35284893495597244084687045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 752744394572741207139990293 35284893495597244084687045)
                ·
                  refine ⟨6615917530424483265878821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35284893495597244084687045 6615917530424483265878821)
                  ·
                    refine ⟨1240484536954590612352279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6615917530424483265878821 1240484536954590612352279)
                    ·
                      rfl

theorem cell23_7247505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_7247505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247505 prefixEnd_7247505 := by exact prefixLift 7247505
  have htrace : WordTrace (prefixWord ++ tailWord_7247505) baseStart_7247505 baseEnd_7247505 := by
    simpa [prefixWord, tailWord_7247505, baseEnd_7247505] using wordTrace_append hprefix tailTrace_7247505
  have hstable : (prefixWord ++ tailWord_7247505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247505).length < 2 ^ (prefixWord ++ tailWord_7247505).sum := by decide
  have hdescent : baseEnd_7247505 < baseStart_7247505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247595 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 2, 6]
def baseStart_7247595 : Nat := 118140960795 + 7247595 * 2 ^ 59
def prefixEnd_7247595 : Nat := 4983230072969 + 3 ^ 40 * 7247595 * 2
def baseEnd_7247595 : Nat := 1240499941374225494977141

theorem tailTrace_7247595 : CollatzResearch.WordTrace tailWord_7247595 prefixEnd_7247595 1240499941374225494977141 := by
  unfold tailWord_7247595
  simp only [CollatzResearch.WordTrace]
  refine ⟨264341506178208580525560239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176227670785472387017040159 264341506178208580525560239)
  ·
    refine ⟨396512259267312870788340359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264341506178208580525560239 396512259267312870788340359)
    ·
      refine ⟨594768388900969306182510539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396512259267312870788340359 594768388900969306182510539)
      ·
        refine ⟨892152583351453959273765809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594768388900969306182510539 892152583351453959273765809)
        ·
          refine ⟨669114437513590469455324357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 892152583351453959273765809 669114437513590469455324357)
          ·
            refine ⟨125458957033798213022873317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 669114437513590469455324357 125458957033798213022873317)
            ·
              refine ⟨23523554443837164941788747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125458957033798213022873317 23523554443837164941788747)
              ·
                refine ⟨35285331665755747412683121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23523554443837164941788747 35285331665755747412683121)
                ·
                  refine ⟨26463998749316810559512341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35285331665755747412683121 26463998749316810559512341)
                  ·
                    refine ⟨1240499941374225494977141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26463998749316810559512341 1240499941374225494977141)
                    ·
                      rfl

theorem cell23_7247595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 6].length) (baseStart_7247595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247595 prefixEnd_7247595 := by exact prefixLift 7247595
  have htrace : WordTrace (prefixWord ++ tailWord_7247595) baseStart_7247595 baseEnd_7247595 := by
    simpa [prefixWord, tailWord_7247595, baseEnd_7247595] using wordTrace_append hprefix tailTrace_7247595
  have hstable : (prefixWord ++ tailWord_7247595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247595).length < 2 ^ (prefixWord ++ tailWord_7247595).sum := by decide
  have hdescent : baseEnd_7247595 < baseStart_7247595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247606 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_7247606 : Nat := 118140960795 + 7247606 * 2 ^ 59
def prefixEnd_7247606 : Nat := 4983230072969 + 3 ^ 40 * 7247606 * 2
def baseEnd_7247606 : Nat := 3721505472409875941893873

theorem tailTrace_7247606 : CollatzResearch.WordTrace tailWord_7247606 prefixEnd_7247606 3721505472409875941893873 := by
  unfold tailWord_7247606
  simp only [CollatzResearch.WordTrace]
  refine ⟨16521369211323045587763167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176227938254112486269473781 16521369211323045587763167)
  ·
    refine ⟨24782053816984568381644751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16521369211323045587763167 24782053816984568381644751)
    ·
      refine ⟨37173080725476852572467127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24782053816984568381644751 37173080725476852572467127)
      ·
        refine ⟨55759621088215278858700691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37173080725476852572467127 55759621088215278858700691)
        ·
          refine ⟨83639431632322918288051037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55759621088215278858700691 83639431632322918288051037)
          ·
            refine ⟨31364786862121094358019139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83639431632322918288051037 31364786862121094358019139)
            ·
              refine ⟨47047180293181641537028709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31364786862121094358019139 47047180293181641537028709)
              ·
                refine ⟨8821346304971557788192883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47047180293181641537028709 8821346304971557788192883)
                ·
                  refine ⟨13232019457457336682289325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8821346304971557788192883 13232019457457336682289325)
                  ·
                    refine ⟨4962007296546501255858497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13232019457457336682289325 4962007296546501255858497)
                    ·
                      refine ⟨3721505472409875941893873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962007296546501255858497 3721505472409875941893873)
                      ·
                        rfl

theorem cell23_7247606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_7247606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247606 prefixEnd_7247606 := by exact prefixLift 7247606
  have htrace : WordTrace (prefixWord ++ tailWord_7247606) baseStart_7247606 baseEnd_7247606 := by
    simpa [prefixWord, tailWord_7247606, baseEnd_7247606] using wordTrace_append hprefix tailTrace_7247606
  have hstable : (prefixWord ++ tailWord_7247606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247606).length < 2 ^ (prefixWord ++ tailWord_7247606).sum := by decide
  have hdescent : baseEnd_7247606 < baseStart_7247606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247615 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 4]
def baseStart_7247615 : Nat := 118140960795 + 7247615 * 2 ^ 59
def prefixEnd_7247615 : Nat := 4983230072969 + 3 ^ 40 * 7247615 * 2
def baseEnd_7247615 : Nat := 3721510093735766406681331

theorem tailTrace_7247615 : CollatzResearch.WordTrace tailWord_7247615 prefixEnd_7247615 3721510093735766406681331 := by
  unfold tailWord_7247615
  simp only [CollatzResearch.WordTrace]
  refine ⟨264342235638136123941288299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176228157092090749294192199 264342235638136123941288299)
  ·
    refine ⟨396513353457204185911932449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264342235638136123941288299 396513353457204185911932449)
    ·
      refine ⟨297385015092903139433949337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396513353457204185911932449 297385015092903139433949337)
      ·
        refine ⟨223038761319677354575462003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297385015092903139433949337 223038761319677354575462003)
        ·
          refine ⟨334558141979516031863193005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223038761319677354575462003 334558141979516031863193005)
          ·
            refine ⟨125459303242318511948697377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334558141979516031863193005 125459303242318511948697377)
            ·
              refine ⟨94094477431738883961523033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125459303242318511948697377 94094477431738883961523033)
              ·
                refine ⟨70570858073804162971142275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94094477431738883961523033 70570858073804162971142275)
                ·
                  refine ⟨105856287110706244456713413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70570858073804162971142275 105856287110706244456713413)
                  ·
                    refine ⟨19848053833257420835633765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105856287110706244456713413 19848053833257420835633765)
                    ·
                      refine ⟨3721510093735766406681331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19848053833257420835633765 3721510093735766406681331)
                      ·
                        rfl

theorem cell23_7247615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_7247615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247615 prefixEnd_7247615 := by exact prefixLift 7247615
  have htrace : WordTrace (prefixWord ++ tailWord_7247615) baseStart_7247615 baseEnd_7247615 := by
    simpa [prefixWord, tailWord_7247615, baseEnd_7247615] using wordTrace_append hprefix tailTrace_7247615
  have hstable : (prefixWord ++ tailWord_7247615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247615).length < 2 ^ (prefixWord ++ tailWord_7247615).sum := by decide
  have hdescent : baseEnd_7247615 < baseStart_7247615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247619 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 4, 2, 2]
def baseStart_7247619 : Nat := 118140960795 + 7247619 * 2 ^ 59
def prefixEnd_7247619 : Nat := 4983230072969 + 3 ^ 40 * 7247619 * 2
def baseEnd_7247619 : Nat := 3721512147658384391031313

theorem tailTrace_7247619 : CollatzResearch.WordTrace tailWord_7247619 prefixEnd_7247619 3721512147658384391031313 := by
  unfold tailWord_7247619
  simp only [CollatzResearch.WordTrace]
  refine ⟨264342381530121632624433911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176228254353414421749622607 264342381530121632624433911)
  ·
    refine ⟨396513572295182448936650867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264342381530121632624433911 396513572295182448936650867)
    ·
      refine ⟨594770358442773673404976301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396513572295182448936650867 594770358442773673404976301)
      ·
        refine ⟨223038884416040127526866113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594770358442773673404976301 223038884416040127526866113)
        ·
          refine ⟨167279163312030095645149585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223038884416040127526866113 167279163312030095645149585)
          ·
            refine ⟨125459372484022571733862189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167279163312030095645149585 125459372484022571733862189)
            ·
              refine ⟨47047264681508464400198321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125459372484022571733862189 47047264681508464400198321)
              ·
                refine ⟨35285448511131348300148741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47047264681508464400198321 35285448511131348300148741)
                ·
                  refine ⟨6616021595837127806277889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35285448511131348300148741 6616021595837127806277889)
                  ·
                    refine ⟨4962016196877845854708417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6616021595837127806277889 4962016196877845854708417)
                    ·
                      refine ⟨3721512147658384391031313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962016196877845854708417 3721512147658384391031313)
                      ·
                        rfl

theorem cell23_7247619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 2, 2].length) (baseStart_7247619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247619 prefixEnd_7247619 := by exact prefixLift 7247619
  have htrace : WordTrace (prefixWord ++ tailWord_7247619) baseStart_7247619 baseEnd_7247619 := by
    simpa [prefixWord, tailWord_7247619, baseEnd_7247619] using wordTrace_append hprefix tailTrace_7247619
  have hstable : (prefixWord ++ tailWord_7247619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247619).length < 2 ^ (prefixWord ++ tailWord_7247619).sum := by decide
  have hdescent : baseEnd_7247619 < baseStart_7247619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247642 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 7]
def baseStart_7247642 : Nat := 118140960795 + 7247642 * 2 ^ 59
def prefixEnd_7247642 : Nat := 4983230072969 + 3 ^ 40 * 7247642 * 2
def baseEnd_7247642 : Nat := 413502661968159755671523

theorem tailTrace_7247642 : CollatzResearch.WordTrace tailWord_7247642 prefixEnd_7247642 413502661968159755671523 := by
  unfold tailWord_7247642
  simp only [CollatzResearch.WordTrace]
  refine ⟨66085805102259576888130295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176228813606025538368347453 66085805102259576888130295)
  ·
    refine ⟨99128707653389365332195443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66085805102259576888130295 99128707653389365332195443)
    ·
      refine ⟨148693061480084047998293165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99128707653389365332195443 148693061480084047998293165)
      ·
        refine ⟨55759898055031517999359937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148693061480084047998293165 55759898055031517999359937)
        ·
          refine ⟨41819923541273638499519953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55759898055031517999359937 41819923541273638499519953)
          ·
            refine ⟨31364942655955228874639965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41819923541273638499519953 31364942655955228874639965)
            ·
              refine ⟨11761853495983210827989987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31364942655955228874639965 11761853495983210827989987)
              ·
                refine ⟨17642780243974816241984981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11761853495983210827989987 17642780243974816241984981)
                ·
                  refine ⟨413502661968159755671523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17642780243974816241984981 413502661968159755671523)
                  ·
                    rfl

theorem cell23_7247642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_7247642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247642 prefixEnd_7247642 := by exact prefixLift 7247642
  have htrace : WordTrace (prefixWord ++ tailWord_7247642) baseStart_7247642 baseEnd_7247642 := by
    simpa [prefixWord, tailWord_7247642, baseEnd_7247642] using wordTrace_append hprefix tailTrace_7247642
  have hstable : (prefixWord ++ tailWord_7247642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247642).length < 2 ^ (prefixWord ++ tailWord_7247642).sum := by decide
  have hdescent : baseEnd_7247642 < baseStart_7247642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247653 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 2, 2, 2]
def baseStart_7247653 : Nat := 118140960795 + 7247653 * 2 ^ 59
def prefixEnd_7247653 : Nat := 4983230072969 + 3 ^ 40 * 7247653 * 2
def baseEnd_7247653 : Nat := 3721529606000637258006157

theorem tailTrace_7247653 : CollatzResearch.WordTrace tailWord_7247653 prefixEnd_7247653 3721529606000637258006157 := by
  unfold tailWord_7247653
  simp only [CollatzResearch.WordTrace]
  refine ⟨264343621611998456431171613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176229081074665637620781075 264343621611998456431171613)
  ·
    refine ⟨99128858104499421161689355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264343621611998456431171613 99128858104499421161689355)
    ·
      refine ⟨148693287156749131742534033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99128858104499421161689355 148693287156749131742534033)
      ·
        refine ⟨111519965367561848806900525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148693287156749131742534033 111519965367561848806900525)
        ·
          refine ⟨41819987012835693302587697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111519965367561848806900525 41819987012835693302587697)
          ·
            refine ⟨31364990259626769976940773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41819987012835693302587697 31364990259626769976940773)
            ·
              refine ⟨5880935673680019370676395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31364990259626769976940773 5880935673680019370676395)
              ·
                refine ⟨8821403510520029056014593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5880935673680019370676395 8821403510520029056014593)
                ·
                  refine ⟨6616052632890021792010945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8821403510520029056014593 6616052632890021792010945)
                  ·
                    refine ⟨4962039474667516344008209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6616052632890021792010945 4962039474667516344008209)
                    ·
                      refine ⟨3721529606000637258006157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962039474667516344008209 3721529606000637258006157)
                      ·
                        rfl

theorem cell23_7247653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_7247653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247653 prefixEnd_7247653 := by exact prefixLift 7247653
  have htrace : WordTrace (prefixWord ++ tailWord_7247653) baseStart_7247653 baseEnd_7247653 := by
    simpa [prefixWord, tailWord_7247653, baseEnd_7247653] using wordTrace_append hprefix tailTrace_7247653
  have hstable : (prefixWord ++ tailWord_7247653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247653).length < 2 ^ (prefixWord ++ tailWord_7247653).sum := by decide
  have hdescent : baseEnd_7247653 < baseStart_7247653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247672 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 2, 5]
def baseStart_7247672 : Nat := 118140960795 + 7247672 * 2 ^ 59
def prefixEnd_7247672 : Nat := 4983230072969 + 3 ^ 40 * 7247672 * 2
def baseEnd_7247672 : Nat := 1240513120711024227889523

theorem tailTrace_7247672 : CollatzResearch.WordTrace tailWord_7247672 prefixEnd_7247672 1240513120711024227889523 := by
  unfold tailWord_7247672
  simp only [CollatzResearch.WordTrace]
  refine ⟨132172157299464811338056635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176229543065953081784075513 132172157299464811338056635)
  ·
    refine ⟨198258235949197217007084953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132172157299464811338056635 198258235949197217007084953)
    ·
      refine ⟨148693676961897912755313715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198258235949197217007084953 148693676961897912755313715)
      ·
        refine ⟨223040515442846869132970573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148693676961897912755313715 223040515442846869132970573)
        ·
          refine ⟨83640193291067575924863965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223040515442846869132970573 83640193291067575924863965)
          ·
            refine ⟨31365072484150340971823987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83640193291067575924863965 31365072484150340971823987)
            ·
              refine ⟨47047608726225511457735981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31365072484150340971823987 47047608726225511457735981)
              ·
                refine ⟨17642853272334566796650993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47047608726225511457735981 17642853272334566796650993)
                ·
                  refine ⟨13232139954250925097488245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17642853272334566796650993 13232139954250925097488245)
                  ·
                    refine ⟨1240513120711024227889523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13232139954250925097488245 1240513120711024227889523)
                    ·
                      rfl

theorem cell23_7247672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_7247672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247672 prefixEnd_7247672 := by exact prefixLift 7247672
  have htrace : WordTrace (prefixWord ++ tailWord_7247672) baseStart_7247672 baseEnd_7247672 := by
    simpa [prefixWord, tailWord_7247672, baseEnd_7247672] using wordTrace_append hprefix tailTrace_7247672
  have hstable : (prefixWord ++ tailWord_7247672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247672).length < 2 ^ (prefixWord ++ tailWord_7247672).sum := by decide
  have hdescent : baseEnd_7247672 < baseStart_7247672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247693 : List Nat := [1, 6, 1, 2, 1, 1, 4, 2, 5]
def baseStart_7247693 : Nat := 118140960795 + 7247693 * 2 ^ 59
def prefixEnd_7247693 : Nat := 4983230072969 + 3 ^ 40 * 7247693 * 2
def baseEnd_7247693 : Nat := 413505571691868566833997

theorem tailTrace_7247693 : CollatzResearch.WordTrace tailWord_7247693 prefixEnd_7247693 413505571691868566833997 := by
  unfold tailWord_7247693
  simp only [CollatzResearch.WordTrace]
  refine ⟨264345080531853543262627733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176230053687902362175085155 264345080531853543262627733)
  ·
    refine ⟨12391175649930634840435675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 264345080531853543262627733 12391175649930634840435675)
    ·
      refine ⟨18586763474895952260653513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12391175649930634840435675 18586763474895952260653513)
      ·
        refine ⟨13940072606171964195490135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18586763474895952260653513 13940072606171964195490135)
        ·
          refine ⟨20910108909257946293235203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13940072606171964195490135 20910108909257946293235203)
          ·
            refine ⟨31365163363886919439852805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20910108909257946293235203 31365163363886919439852805)
            ·
              refine ⟨5880968130728797394972401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31365163363886919439852805 5880968130728797394972401)
              ·
                refine ⟨4410726098046598046229301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5880968130728797394972401 4410726098046598046229301)
                ·
                  refine ⟨413505571691868566833997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4410726098046598046229301 413505571691868566833997)
                  ·
                    rfl

theorem cell23_7247693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_7247693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247693 prefixEnd_7247693 := by exact prefixLift 7247693
  have htrace : WordTrace (prefixWord ++ tailWord_7247693) baseStart_7247693 baseEnd_7247693 := by
    simpa [prefixWord, tailWord_7247693, baseEnd_7247693] using wordTrace_append hprefix tailTrace_7247693
  have hstable : (prefixWord ++ tailWord_7247693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247693).length < 2 ^ (prefixWord ++ tailWord_7247693).sum := by decide
  have hdescent : baseEnd_7247693 < baseStart_7247693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247719 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 3, 4]
def baseStart_7247719 : Nat := 118140960795 + 7247719 * 2 ^ 59
def prefixEnd_7247719 : Nat := 4983230072969 + 3 ^ 40 * 7247719 * 2
def baseEnd_7247719 : Nat := 1240521165241277999926951

theorem tailTrace_7247719 : CollatzResearch.WordTrace tailWord_7247719 prefixEnd_7247719 1240521165241277999926951 := by
  unfold tailWord_7247719
  simp only [CollatzResearch.WordTrace]
  refine ⟨264346028829759349703074211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176230685886506233135382807 264346028829759349703074211)
  ·
    refine ⟨396519043244639024554611317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264346028829759349703074211 396519043244639024554611317)
    ·
      refine ⟨37173660304184908551994811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 396519043244639024554611317 37173660304184908551994811)
      ·
        refine ⟨55760490456277362827992217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37173660304184908551994811 55760490456277362827992217)
        ·
          refine ⟨41820367842208022120994163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55760490456277362827992217 41820367842208022120994163)
          ·
            refine ⟨62730551763312033181491245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41820367842208022120994163 62730551763312033181491245)
            ·
              refine ⟨23523956911242012443059217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62730551763312033181491245 23523956911242012443059217)
              ·
                refine ⟨17642967683431509332294413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23523956911242012443059217 17642967683431509332294413)
                ·
                  refine ⟨6616112881286815999610405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17642967683431509332294413 6616112881286815999610405)
                  ·
                    refine ⟨1240521165241277999926951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6616112881286815999610405 1240521165241277999926951)
                    ·
                      rfl

theorem cell23_7247719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_7247719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247719 prefixEnd_7247719 := by exact prefixLift 7247719
  have htrace : WordTrace (prefixWord ++ tailWord_7247719) baseStart_7247719 baseEnd_7247719 := by
    simpa [prefixWord, tailWord_7247719, baseEnd_7247719] using wordTrace_append hprefix tailTrace_7247719
  have hstable : (prefixWord ++ tailWord_7247719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247719).length < 2 ^ (prefixWord ++ tailWord_7247719).sum := by decide
  have hdescent : baseEnd_7247719 < baseStart_7247719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247726 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_7247726 : Nat := 118140960795 + 7247726 * 2 ^ 59
def prefixEnd_7247726 : Nat := 4983230072969 + 3 ^ 40 * 7247726 * 2
def baseEnd_7247726 : Nat := 3721567090088415472393321

theorem tailTrace_7247726 : CollatzResearch.WordTrace tailWord_7247726 prefixEnd_7247726 3721567090088415472393321 := by
  unfold tailWord_7247726
  simp only [CollatzResearch.WordTrace]
  refine ⟨33043285517591748737322379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176230856093822659932386021 33043285517591748737322379)
  ·
    refine ⟨49564928276387623105983569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33043285517591748737322379 49564928276387623105983569)
    ·
      refine ⟨37173696207290717329487677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49564928276387623105983569 37173696207290717329487677)
      ·
        refine ⟨13940136077734018998557879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37173696207290717329487677 13940136077734018998557879)
        ·
          refine ⟨20910204116601028497836819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13940136077734018998557879 20910204116601028497836819)
          ·
            refine ⟨31365306174901542746755229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20910204116601028497836819 31365306174901542746755229)
            ·
              refine ⟨11761989815588078530033211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31365306174901542746755229 11761989815588078530033211)
              ·
                refine ⟨17642984723382117795049817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11761989815588078530033211 17642984723382117795049817)
                ·
                  refine ⟨13232238542536588346287363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17642984723382117795049817 13232238542536588346287363)
                  ·
                    refine ⟨19848357813804882519431045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13232238542536588346287363 19848357813804882519431045)
                    ·
                      refine ⟨3721567090088415472393321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19848357813804882519431045 3721567090088415472393321)
                      ·
                        rfl

theorem cell23_7247726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_7247726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247726 prefixEnd_7247726 := by exact prefixLift 7247726
  have htrace : WordTrace (prefixWord ++ tailWord_7247726) baseStart_7247726 baseEnd_7247726 := by
    simpa [prefixWord, tailWord_7247726, baseEnd_7247726] using wordTrace_append hprefix tailTrace_7247726
  have hstable : (prefixWord ++ tailWord_7247726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247726).length < 2 ^ (prefixWord ++ tailWord_7247726).sum := by decide
  have hdescent : baseEnd_7247726 < baseStart_7247726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247769 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 1, 5, 2]
def baseStart_7247769 : Nat := 118140960795 + 7247769 * 2 ^ 59
def prefixEnd_7247769 : Nat := 4983230072969 + 3 ^ 40 * 7247769 * 2
def baseEnd_7247769 : Nat := 3721589169756558804155623

theorem tailTrace_7247769 : CollatzResearch.WordTrace tailWord_7247769 prefixEnd_7247769 3721589169756558804155623 := by
  unfold tailWord_7247769
  simp only [CollatzResearch.WordTrace]
  refine ⟨264347852479578208242394361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176231901653052138828262907 264347852479578208242394361)
  ·
    refine ⟨198260889359683656181795771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264347852479578208242394361 198260889359683656181795771)
    ·
      refine ⟨297391334039525484272693657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198260889359683656181795771 297391334039525484272693657)
      ·
        refine ⟨223043500529644113204520243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297391334039525484272693657 223043500529644113204520243)
        ·
          refine ⟨334565250794466169806780365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223043500529644113204520243 334565250794466169806780365)
          ·
            refine ⟨125461969047924813677542637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334565250794466169806780365 125461969047924813677542637)
            ·
              refine ⟨47048238392971805129078489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125461969047924813677542637 47048238392971805129078489)
              ·
                refine ⟨35286178794728853846808867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47048238392971805129078489 35286178794728853846808867)
                ·
                  refine ⟨52929268192093280770213301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35286178794728853846808867 52929268192093280770213301)
                  ·
                    refine ⟨4962118893008745072207497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52929268192093280770213301 4962118893008745072207497)
                    ·
                      refine ⟨3721589169756558804155623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962118893008745072207497 3721589169756558804155623)
                      ·
                        rfl

theorem cell23_7247769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 5, 2].length) (baseStart_7247769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247769 prefixEnd_7247769 := by exact prefixLift 7247769
  have htrace : WordTrace (prefixWord ++ tailWord_7247769) baseStart_7247769 baseEnd_7247769 := by
    simpa [prefixWord, tailWord_7247769, baseEnd_7247769] using wordTrace_append hprefix tailTrace_7247769
  have hstable : (prefixWord ++ tailWord_7247769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247769).length < 2 ^ (prefixWord ++ tailWord_7247769).sum := by decide
  have hdescent : baseEnd_7247769 < baseStart_7247769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247819 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 3]
def baseStart_7247819 : Nat := 118140960795 + 7247819 * 2 ^ 59
def prefixEnd_7247819 : Nat := 4983230072969 + 3 ^ 40 * 7247819 * 2
def baseEnd_7247819 : Nat := 3721614843789283608530393

theorem tailTrace_7247819 : CollatzResearch.WordTrace tailWord_7247819 prefixEnd_7247819 3721614843789283608530393 := by
  unfold tailWord_7247819
  simp only [CollatzResearch.WordTrace]
  refine ⟨264349676129397066781714511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176233117419598044521143007 264349676129397066781714511)
  ·
    refine ⟨396524514194095600172571767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264349676129397066781714511 396524514194095600172571767)
    ·
      refine ⟨594786771291143400258857651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396524514194095600172571767 594786771291143400258857651)
      ·
        refine ⟨892180156936715100388286477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594786771291143400258857651 892180156936715100388286477)
        ·
          refine ⟨334567558851268162645607429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 892180156936715100388286477 334567558851268162645607429)
          ·
            refine ⟨62731417284612780496051393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334567558851268162645607429 62731417284612780496051393)
            ·
              refine ⟨47048562963459585372038545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62731417284612780496051393 47048562963459585372038545)
              ·
                refine ⟨35286422222594689029028909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47048562963459585372038545 35286422222594689029028909)
                ·
                  refine ⟨13232408333473008385885841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35286422222594689029028909 13232408333473008385885841)
                  ·
                    refine ⟨9924306250104756289414381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13232408333473008385885841 9924306250104756289414381)
                    ·
                      refine ⟨3721614843789283608530393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9924306250104756289414381 3721614843789283608530393)
                      ·
                        rfl

theorem cell23_7247819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 3].length) (baseStart_7247819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247819 prefixEnd_7247819 := by exact prefixLift 7247819
  have htrace : WordTrace (prefixWord ++ tailWord_7247819) baseStart_7247819 baseEnd_7247819 := by
    simpa [prefixWord, tailWord_7247819, baseEnd_7247819] using wordTrace_append hprefix tailTrace_7247819
  have hstable : (prefixWord ++ tailWord_7247819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247819).length < 2 ^ (prefixWord ++ tailWord_7247819).sum := by decide
  have hdescent : baseEnd_7247819 < baseStart_7247819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247829 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7247829 : Nat := 118140960795 + 7247829 * 2 ^ 59
def prefixEnd_7247829 : Nat := 4983230072969 + 3 ^ 40 * 7247829 * 2
def baseEnd_7247829 : Nat := 3721619978595828569405347

theorem tailTrace_7247829 : CollatzResearch.WordTrace tailWord_7247829 prefixEnd_7247829 3721619978595828569405347 := by
  unfold tailWord_7247829
  simp only [CollatzResearch.WordTrace]
  refine ⟨264350040859360838489578541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176233360572907225659719027 264350040859360838489578541)
  ·
    refine ⟨99131265322260314433591953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264350040859360838489578541 99131265322260314433591953)
    ·
      refine ⟨74348448991695235825193965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99131265322260314433591953 74348448991695235825193965)
      ·
        refine ⟨27880668371885713434447737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74348448991695235825193965 27880668371885713434447737)
        ·
          refine ⟨20910501278914285075835803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27880668371885713434447737 20910501278914285075835803)
          ·
            refine ⟨31365751918371427613753705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20910501278914285075835803 31365751918371427613753705)
            ·
              refine ⟨23524313938778570710315279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31365751918371427613753705 23524313938778570710315279)
              ·
                refine ⟨35286470908167856065472919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23524313938778570710315279 35286470908167856065472919)
                ·
                  refine ⟨52929706362251784098209379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35286470908167856065472919 52929706362251784098209379)
                  ·
                    refine ⟨79394559543377676147314069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52929706362251784098209379 79394559543377676147314069)
                    ·
                      refine ⟨3721619978595828569405347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79394559543377676147314069 3721619978595828569405347)
                      ·
                        rfl

theorem cell23_7247829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7247829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247829 prefixEnd_7247829 := by exact prefixLift 7247829
  have htrace : WordTrace (prefixWord ++ tailWord_7247829) baseStart_7247829 baseEnd_7247829 := by
    simpa [prefixWord, tailWord_7247829, baseEnd_7247829] using wordTrace_append hprefix tailTrace_7247829
  have hstable : (prefixWord ++ tailWord_7247829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247829).length < 2 ^ (prefixWord ++ tailWord_7247829).sum := by decide
  have hdescent : baseEnd_7247829 < baseStart_7247829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247830 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_7247830 : Nat := 118140960795 + 7247830 * 2 ^ 59
def prefixEnd_7247830 : Nat := 4983230072969 + 3 ^ 40 * 7247830 * 2
def baseEnd_7247830 : Nat := 1240540164025494355164281

theorem tailTrace_7247830 : CollatzResearch.WordTrace tailWord_7247830 prefixEnd_7247830 1240540164025494355164281 := by
  unfold tailWord_7247830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16521879833272325978772809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176233384888238143773576629 16521879833272325978772809)
  ·
    refine ⟨12391409874954244484079607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16521879833272325978772809 12391409874954244484079607)
    ·
      refine ⟨18587114812431366726119411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12391409874954244484079607 18587114812431366726119411)
      ·
        refine ⟨27880672218647050089179117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18587114812431366726119411 27880672218647050089179117)
        ·
          refine ⟨10455252081992643783442169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27880672218647050089179117 10455252081992643783442169)
          ·
            refine ⟨7841439061494482837581627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10455252081992643783442169 7841439061494482837581627)
            ·
              refine ⟨11762158592241724256372441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841439061494482837581627 11762158592241724256372441)
              ·
                refine ⟨8821618944181293192279331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11762158592241724256372441 8821618944181293192279331)
                ·
                  refine ⟨13232428416271939788418997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8821618944181293192279331 13232428416271939788418997)
                  ·
                    refine ⟨1240540164025494355164281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13232428416271939788418997 1240540164025494355164281)
                    ·
                      rfl

theorem cell23_7247830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_7247830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247830 prefixEnd_7247830 := by exact prefixLift 7247830
  have htrace : WordTrace (prefixWord ++ tailWord_7247830) baseStart_7247830 baseEnd_7247830 := by
    simpa [prefixWord, tailWord_7247830, baseEnd_7247830] using wordTrace_append hprefix tailTrace_7247830
  have hstable : (prefixWord ++ tailWord_7247830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247830).length < 2 ^ (prefixWord ++ tailWord_7247830).sum := by decide
  have hdescent : baseEnd_7247830 < baseStart_7247830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247833 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 4]
def baseStart_7247833 : Nat := 118140960795 + 7247833 * 2 ^ 59
def prefixEnd_7247833 : Nat := 4983230072969 + 3 ^ 40 * 7247833 * 2
def baseEnd_7247833 : Nat := 3721622032518446553755329

theorem tailTrace_7247833 : CollatzResearch.WordTrace tailWord_7247833 prefixEnd_7247833 3721622032518446553755329 := by
  unfold tailWord_7247833
  simp only [CollatzResearch.WordTrace]
  refine ⟨264350186751346347172724153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176233457834230898115149435 264350186751346347172724153)
  ·
    refine ⟨198262640063509760379543115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264350186751346347172724153 198262640063509760379543115)
    ·
      refine ⟨297393960095264640569314673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198262640063509760379543115 297393960095264640569314673)
      ·
        refine ⟨223045470071448480426986005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297393960095264640569314673 223045470071448480426986005)
        ·
          refine ⟨10455256409599147520014969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 223045470071448480426986005 10455256409599147520014969)
          ·
            refine ⟨7841442307199360640011227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10455256409599147520014969 7841442307199360640011227)
            ·
              refine ⟨11762163460799040960016841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841442307199360640011227 11762163460799040960016841)
              ·
                refine ⟨8821622595599280720012631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11762163460799040960016841 8821622595599280720012631)
                ·
                  refine ⟨13232433893398921080018947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8821622595599280720012631 13232433893398921080018947)
                  ·
                    refine ⟨19848650840098381620028421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13232433893398921080018947 19848650840098381620028421)
                    ·
                      refine ⟨3721622032518446553755329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19848650840098381620028421 3721622032518446553755329)
                      ·
                        rfl

theorem cell23_7247833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_7247833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247833 prefixEnd_7247833 := by exact prefixLift 7247833
  have htrace : WordTrace (prefixWord ++ tailWord_7247833) baseStart_7247833 baseEnd_7247833 := by
    simpa [prefixWord, tailWord_7247833, baseEnd_7247833] using wordTrace_append hprefix tailTrace_7247833
  have hstable : (prefixWord ++ tailWord_7247833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247833).length < 2 ^ (prefixWord ++ tailWord_7247833).sum := by decide
  have hdescent : baseEnd_7247833 < baseStart_7247833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247850 : List Nat := [3, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_7247850 : Nat := 118140960795 + 7247850 * 2 ^ 59
def prefixEnd_7247850 : Nat := 4983230072969 + 3 ^ 40 * 7247850 * 2
def baseEnd_7247850 : Nat := 3721630761689572987242751

theorem tailTrace_7247850 : CollatzResearch.WordTrace tailWord_7247850 prefixEnd_7247850 3721630761689572987242751 := by
  unfold tailWord_7247850
  simp only [CollatzResearch.WordTrace]
  refine ⟨66087701698071189769023251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176233871194856506050728669 66087701698071189769023251)
  ·
    refine ⟨99131552547106784653534877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66087701698071189769023251 99131552547106784653534877)
    ·
      refine ⟨37174332205165044245075579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99131552547106784653534877 37174332205165044245075579)
      ·
        refine ⟨55761498307747566367613369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37174332205165044245075579 55761498307747566367613369)
        ·
          refine ⟨41821123730810674775710027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55761498307747566367613369 41821123730810674775710027)
          ·
            refine ⟨62731685596216012163565041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41821123730810674775710027 62731685596216012163565041)
            ·
              refine ⟨47048764197162009122673781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62731685596216012163565041 47048764197162009122673781)
              ·
                refine ⟨4410821643483938355250667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47048764197162009122673781 4410821643483938355250667)
                ·
                  refine ⟨6616232465225907532876001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4410821643483938355250667 6616232465225907532876001)
                  ·
                    refine ⟨4962174348919430649657001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6616232465225907532876001 4962174348919430649657001)
                    ·
                      refine ⟨3721630761689572987242751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962174348919430649657001 3721630761689572987242751)
                      ·
                        rfl

theorem cell23_7247850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_7247850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247850 prefixEnd_7247850 := by exact prefixLift 7247850
  have htrace : WordTrace (prefixWord ++ tailWord_7247850) baseStart_7247850 baseEnd_7247850 := by
    simpa [prefixWord, tailWord_7247850, baseEnd_7247850] using wordTrace_append hprefix tailTrace_7247850
  have hstable : (prefixWord ++ tailWord_7247850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247850).length < 2 ^ (prefixWord ++ tailWord_7247850).sum := by decide
  have hdescent : baseEnd_7247850 < baseStart_7247850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247852 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_7247852 : Nat := 118140960795 + 7247852 * 2 ^ 59
def prefixEnd_7247852 : Nat := 4983230072969 + 3 ^ 40 * 7247852 * 2
def baseEnd_7247852 : Nat := 1240543929550293993139247

theorem tailTrace_7247852 : CollatzResearch.WordTrace tailWord_7247852 prefixEnd_7247852 1240543929550293993139247 := by
  unfold tailWord_7247852
  simp only [CollatzResearch.WordTrace]
  refine ⟨132175439869138756708832905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176233919825518342278443873 132175439869138756708832905)
  ·
    refine ⟨99131579901854067531624679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132175439869138756708832905 99131579901854067531624679)
    ·
      refine ⟨148697369852781101297437019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99131579901854067531624679 148697369852781101297437019)
      ·
        refine ⟨223046054779171651946155529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148697369852781101297437019 223046054779171651946155529)
        ·
          refine ⟨167284541084378738959616647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223046054779171651946155529 167284541084378738959616647)
          ·
            refine ⟨250926811626568108439424971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167284541084378738959616647 250926811626568108439424971)
            ·
              refine ⟨376390217439852162659137457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250926811626568108439424971 376390217439852162659137457)
              ·
                refine ⟨282292663079889121994353093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376390217439852162659137457 282292663079889121994353093)
                ·
                  refine ⟨52929874327479210373941205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282292663079889121994353093 52929874327479210373941205)
                  ·
                    refine ⟨1240543929550293993139247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52929874327479210373941205 1240543929550293993139247)
                    ·
                      rfl

theorem cell23_7247852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_7247852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247852 prefixEnd_7247852 := by exact prefixLift 7247852
  have htrace : WordTrace (prefixWord ++ tailWord_7247852) baseStart_7247852 baseEnd_7247852 := by
    simpa [prefixWord, tailWord_7247852, baseEnd_7247852] using wordTrace_append hprefix tailTrace_7247852
  have hstable : (prefixWord ++ tailWord_7247852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247852).length < 2 ^ (prefixWord ++ tailWord_7247852).sum := by decide
  have hdescent : baseEnd_7247852 < baseStart_7247852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247939 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 3]
def baseStart_7247939 : Nat := 118140960795 + 7247939 * 2 ^ 59
def prefixEnd_7247939 : Nat := 4983230072969 + 3 ^ 40 * 7247939 * 2
def baseEnd_7247939 : Nat := 3721676461467823139029841

theorem tailTrace_7247939 : CollatzResearch.WordTrace tailWord_7247939 prefixEnd_7247939 3721676461467823139029841 := by
  unfold tailWord_7247939
  simp only [CollatzResearch.WordTrace]
  refine ⟨264354052888962327276082871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176236035259308218184055247 264354052888962327276082871)
  ·
    refine ⟨396531079333443490914124307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264354052888962327276082871 396531079333443490914124307)
    ·
      refine ⟨594796619000165236371186461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396531079333443490914124307 594796619000165236371186461)
      ·
        refine ⟨223048732125061963639194923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594796619000165236371186461 223048732125061963639194923)
        ·
          refine ⟨334573098187592945458792385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223048732125061963639194923 334573098187592945458792385)
          ·
            refine ⟨250929823640694709094094289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334573098187592945458792385 250929823640694709094094289)
            ·
              refine ⟨188197367730521031820570717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250929823640694709094094289 188197367730521031820570717)
              ·
                refine ⟨70574012898945386932714019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188197367730521031820570717 70574012898945386932714019)
                ·
                  refine ⟨105861019348418080399071029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70574012898945386932714019 105861019348418080399071029)
                  ·
                    refine ⟨9924470563914195037412909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105861019348418080399071029 9924470563914195037412909)
                    ·
                      refine ⟨3721676461467823139029841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9924470563914195037412909 3721676461467823139029841)
                      ·
                        rfl

theorem cell23_7247939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_7247939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247939 prefixEnd_7247939 := by exact prefixLift 7247939
  have htrace : WordTrace (prefixWord ++ tailWord_7247939) baseStart_7247939 baseEnd_7247939 := by
    simpa [prefixWord, tailWord_7247939, baseEnd_7247939] using wordTrace_append hprefix tailTrace_7247939
  have hstable : (prefixWord ++ tailWord_7247939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247939).length < 2 ^ (prefixWord ++ tailWord_7247939).sum := by decide
  have hdescent : baseEnd_7247939 < baseStart_7247939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247959 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 1, 7]
def baseStart_7247959 : Nat := 118140960795 + 7247959 * 2 ^ 59
def prefixEnd_7247959 : Nat := 4983230072969 + 3 ^ 40 * 7247959 * 2
def baseEnd_7247959 : Nat := 1240562243693637686926583

theorem tailTrace_7247959 : CollatzResearch.WordTrace tailWord_7247959 prefixEnd_7247959 1240562243693637686926583 := by
  unfold tailWord_7247959
  simp only [CollatzResearch.WordTrace]
  refine ⟨264354782348889870691810931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176236521565926580461207287 264354782348889870691810931)
  ·
    refine ⟨396532173523334806037716397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264354782348889870691810931 396532173523334806037716397)
    ·
      refine ⟨148699565071250552264143649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396532173523334806037716397 148699565071250552264143649)
      ·
        refine ⟨111524673803437914198107737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148699565071250552264143649 111524673803437914198107737)
        ·
          refine ⟨83643505352578435648580803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111524673803437914198107737 83643505352578435648580803)
          ·
            refine ⟨125465258028867653472871205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83643505352578435648580803 125465258028867653472871205)
            ·
              refine ⟨23524735880412685026163351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125465258028867653472871205 23524735880412685026163351)
              ·
                refine ⟨35287103820619027539245027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23524735880412685026163351 35287103820619027539245027)
                ·
                  refine ⟨52930655730928541308867541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35287103820619027539245027 52930655730928541308867541)
                  ·
                    refine ⟨1240562243693637686926583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52930655730928541308867541 1240562243693637686926583)
                    ·
                      rfl

theorem cell23_7247959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_7247959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247959 prefixEnd_7247959 := by exact prefixLift 7247959
  have htrace : WordTrace (prefixWord ++ tailWord_7247959) baseStart_7247959 baseEnd_7247959 := by
    simpa [prefixWord, tailWord_7247959, baseEnd_7247959] using wordTrace_append hprefix tailTrace_7247959
  have hstable : (prefixWord ++ tailWord_7247959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247959).length < 2 ^ (prefixWord ++ tailWord_7247959).sum := by decide
  have hdescent : baseEnd_7247959 < baseStart_7247959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247969 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_7247969 : Nat := 118140960795 + 7247969 * 2 ^ 59
def prefixEnd_7247969 : Nat := 4983230072969 + 3 ^ 40 * 7247969 * 2
def baseEnd_7247969 : Nat := 3721691865887458021654703

theorem tailTrace_7247969 : CollatzResearch.WordTrace tailWord_7247969 prefixEnd_7247969 3721691865887458021654703 := by
  unfold tailWord_7247969
  simp only [CollatzResearch.WordTrace]
  refine ⟨264355147078853642399674961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176236764719235761599783307 264355147078853642399674961)
  ·
    refine ⟨198266360309140231799756221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264355147078853642399674961 198266360309140231799756221)
    ·
      refine ⟨74349885115927586924908583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198266360309140231799756221 74349885115927586924908583)
      ·
        refine ⟨111524827673891380387362875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74349885115927586924908583 111524827673891380387362875)
        ·
          refine ⟨167287241510837070581044313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111524827673891380387362875 167287241510837070581044313)
          ·
            refine ⟨125465431133127802935783235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167287241510837070581044313 125465431133127802935783235)
            ·
              refine ⟨188198146699691704403674853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125465431133127802935783235 188198146699691704403674853)
              ·
                refine ⟨35287152506192194575689035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188198146699691704403674853 35287152506192194575689035)
                ·
                  refine ⟨52930728759288291863533553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35287152506192194575689035 52930728759288291863533553)
                  ·
                    refine ⟨39698046569466218897650165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52930728759288291863533553 39698046569466218897650165)
                    ·
                      refine ⟨3721691865887458021654703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39698046569466218897650165 3721691865887458021654703)
                      ·
                        rfl

theorem cell23_7247969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_7247969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247969 prefixEnd_7247969 := by exact prefixLift 7247969
  have htrace : WordTrace (prefixWord ++ tailWord_7247969) baseStart_7247969 baseEnd_7247969 := by
    simpa [prefixWord, tailWord_7247969, baseEnd_7247969] using wordTrace_append hprefix tailTrace_7247969
  have hstable : (prefixWord ++ tailWord_7247969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247969).length < 2 ^ (prefixWord ++ tailWord_7247969).sum := by decide
  have hdescent : baseEnd_7247969 < baseStart_7247969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7247986 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_7247986 : Nat := 118140960795 + 7247986 * 2 ^ 59
def prefixEnd_7247986 : Nat := 4983230072969 + 3 ^ 40 * 7247986 * 2
def baseEnd_7247986 : Nat := 3721700595058584455142125

theorem tailTrace_7247986 : CollatzResearch.WordTrace tailWord_7247986 prefixEnd_7247986 3721700595058584455142125 := by
  unfold tailWord_7247986
  simp only [CollatzResearch.WordTrace]
  refine ⟨66088941779948013575760953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176237178079861369535362541 66088941779948013575760953)
  ·
    refine ⟨49566706334961010181820715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66088941779948013575760953 49566706334961010181820715)
    ·
      refine ⟨74350059502441515272731073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49566706334961010181820715 74350059502441515272731073)
      ·
        refine ⟨55762544626831136454548305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74350059502441515272731073 55762544626831136454548305)
        ·
          refine ⟨41821908470123352340911229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55762544626831136454548305 41821908470123352340911229)
          ·
            refine ⟨15683215676296257127841711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41821908470123352340911229 15683215676296257127841711)
            ·
              refine ⟨23524823514444385691762567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15683215676296257127841711 23524823514444385691762567)
              ·
                refine ⟨35287235271666578537643851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23524823514444385691762567 35287235271666578537643851)
                ·
                  refine ⟨52930852907499867806465777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35287235271666578537643851 52930852907499867806465777)
                  ·
                    refine ⟨39698139680624900854849333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52930852907499867806465777 39698139680624900854849333)
                    ·
                      refine ⟨3721700595058584455142125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39698139680624900854849333 3721700595058584455142125)
                      ·
                        rfl

theorem cell23_7247986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_7247986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7247986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7247986 prefixEnd_7247986 := by exact prefixLift 7247986
  have htrace : WordTrace (prefixWord ++ tailWord_7247986) baseStart_7247986 baseEnd_7247986 := by
    simpa [prefixWord, tailWord_7247986, baseEnd_7247986] using wordTrace_append hprefix tailTrace_7247986
  have hstable : (prefixWord ++ tailWord_7247986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7247986).length < 2 ^ (prefixWord ++ tailWord_7247986).sum := by decide
  have hdescent : baseEnd_7247986 < baseStart_7247986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7247986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248033 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_7248033 : Nat := 118140960795 + 7248033 * 2 ^ 59
def prefixEnd_7248033 : Nat := 4983230072969 + 3 ^ 40 * 7248033 * 2
def baseEnd_7248033 : Nat := 3721724728649345771254409

theorem tailTrace_7248033 : CollatzResearch.WordTrace tailWord_7248033 prefixEnd_7248033 3721724728649345771254409 := by
  unfold tailWord_7248033
  simp only [CollatzResearch.WordTrace]
  refine ⟨264357481350621781330004753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176238320900414520886669835 264357481350621781330004753)
  ·
    refine ⟨198268111012966335997503565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264357481350621781330004753 198268111012966335997503565)
    ·
      refine ⟨74350541629862375999063837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198268111012966335997503565 74350541629862375999063837)
      ·
        refine ⟨27881453111198390999648939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74350541629862375999063837 27881453111198390999648939)
        ·
          refine ⟨41822179666797586499473409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27881453111198390999648939 41822179666797586499473409)
          ·
            refine ⟨31366634750098189874605057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41822179666797586499473409 31366634750098189874605057)
            ·
              refine ⟨23524976062573642405953793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31366634750098189874605057 23524976062573642405953793)
              ·
                refine ⟨17643732046930231804465345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23524976062573642405953793 17643732046930231804465345)
                ·
                  refine ⟨13232799035197673853349009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17643732046930231804465345 13232799035197673853349009)
                  ·
                    refine ⟨9924599276398255390011757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13232799035197673853349009 9924599276398255390011757)
                    ·
                      refine ⟨3721724728649345771254409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9924599276398255390011757 3721724728649345771254409)
                      ·
                        rfl

theorem cell23_7248033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_7248033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248033 prefixEnd_7248033 := by exact prefixLift 7248033
  have htrace : WordTrace (prefixWord ++ tailWord_7248033) baseStart_7248033 baseEnd_7248033 := by
    simpa [prefixWord, tailWord_7248033, baseEnd_7248033] using wordTrace_append hprefix tailTrace_7248033
  have hstable : (prefixWord ++ tailWord_7248033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248033).length < 2 ^ (prefixWord ++ tailWord_7248033).sum := by decide
  have hdescent : baseEnd_7248033 < baseStart_7248033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248059 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 7]
def baseStart_7248059 : Nat := 118140960795 + 7248059 * 2 ^ 59
def prefixEnd_7248059 : Nat := 4983230072969 + 3 ^ 40 * 7248059 * 2
def baseEnd_7248059 : Nat := 3721738079146362669529289

theorem tailTrace_7248059 : CollatzResearch.WordTrace tailWord_7248059 prefixEnd_7248059 3721738079146362669529289 := by
  unfold tailWord_7248059
  simp only [CollatzResearch.WordTrace]
  refine ⟨264358429648527587770451231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176238953099018391846967487 264358429648527587770451231)
  ·
    refine ⟨396537644472791381655676847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264358429648527587770451231 396537644472791381655676847)
    ·
      refine ⟨594806466709187072483515271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396537644472791381655676847 594806466709187072483515271)
      ·
        refine ⟨892209700063780608725272907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594806466709187072483515271 892209700063780608725272907)
        ·
          refine ⟨1338314550095670913087909361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892209700063780608725272907 1338314550095670913087909361)
          ·
            refine ⟨1003735912571753184815932021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338314550095670913087909361 1003735912571753184815932021)
            ·
              refine ⟨94100241803601861076493627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1003735912571753184815932021 94100241803601861076493627)
              ·
                refine ⟨141150362705402791614740441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94100241803601861076493627 141150362705402791614740441)
                ·
                  refine ⟨105862772029052093711055331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141150362705402791614740441 105862772029052093711055331)
                  ·
                    refine ⟨158794158043578140566582997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105862772029052093711055331 158794158043578140566582997)
                    ·
                      refine ⟨3721738079146362669529289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158794158043578140566582997 3721738079146362669529289)
                      ·
                        rfl

theorem cell23_7248059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_7248059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248059 prefixEnd_7248059 := by exact prefixLift 7248059
  have htrace : WordTrace (prefixWord ++ tailWord_7248059) baseStart_7248059 baseEnd_7248059 := by
    simpa [prefixWord, tailWord_7248059, baseEnd_7248059] using wordTrace_append hprefix tailTrace_7248059
  have hstable : (prefixWord ++ tailWord_7248059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248059).length < 2 ^ (prefixWord ++ tailWord_7248059).sum := by decide
  have hdescent : baseEnd_7248059 < baseStart_7248059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248073 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 2, 3, 2]
def baseStart_7248073 : Nat := 118140960795 + 7248073 * 2 ^ 59
def prefixEnd_7248073 : Nat := 4983230072969 + 3 ^ 40 * 7248073 * 2
def baseEnd_7248073 : Nat := 3721745267875525614754225

theorem tailTrace_7248073 : CollatzResearch.WordTrace tailWord_7248073 prefixEnd_7248073 3721745267875525614754225 := by
  unfold tailWord_7248073
  simp only [CollatzResearch.WordTrace]
  refine ⟨264358940270476868161460873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176239293513651245440973915 264358940270476868161460873)
  ·
    refine ⟨198269205202857651121095655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264358940270476868161460873 198269205202857651121095655)
    ·
      refine ⟨297403807804286476681643483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198269205202857651121095655 297403807804286476681643483)
      ·
        refine ⟨446105711706429715022465225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297403807804286476681643483 446105711706429715022465225)
        ·
          refine ⟨334579283779822286266848919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446105711706429715022465225 334579283779822286266848919)
          ·
            refine ⟨501868925669733429400273379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334579283779822286266848919 501868925669733429400273379)
            ·
              refine ⟨752803388504600144100410069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501868925669733429400273379 752803388504600144100410069)
              ·
                refine ⟨17643829418076565877353361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 752803388504600144100410069 17643829418076565877353361)
                ·
                  refine ⟨13232872063557424408015021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17643829418076565877353361 13232872063557424408015021)
                  ·
                    refine ⟨4962327023834034153005633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13232872063557424408015021 4962327023834034153005633)
                    ·
                      refine ⟨3721745267875525614754225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962327023834034153005633 3721745267875525614754225)
                      ·
                        rfl

theorem cell23_7248073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 3, 2].length) (baseStart_7248073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248073 prefixEnd_7248073 := by exact prefixLift 7248073
  have htrace : WordTrace (prefixWord ++ tailWord_7248073) baseStart_7248073 baseEnd_7248073 := by
    simpa [prefixWord, tailWord_7248073, baseEnd_7248073] using wordTrace_append hprefix tailTrace_7248073
  have hstable : (prefixWord ++ tailWord_7248073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248073).length < 2 ^ (prefixWord ++ tailWord_7248073).sum := by decide
  have hdescent : baseEnd_7248073 < baseStart_7248073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248113 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 2, 4]
def baseStart_7248113 : Nat := 118140960795 + 7248113 * 2 ^ 59
def prefixEnd_7248113 : Nat := 4983230072969 + 3 ^ 40 * 7248113 * 2
def baseEnd_7248113 : Nat := 1240588602367235152751347

theorem tailTrace_7248113 : CollatzResearch.WordTrace tailWord_7248113 prefixEnd_7248113 1240588602367235152751347 := by
  unfold tailWord_7248113
  simp only [CollatzResearch.WordTrace]
  refine ⟨264360399190331954992916993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176240266126887969995277995 264360399190331954992916993)
  ·
    refine ⟨198270299392748966244687745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264360399190331954992916993 198270299392748966244687745)
    ·
      refine ⟨148702724544561724683515809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198270299392748966244687745 148702724544561724683515809)
      ·
        refine ⟨111527043408421293512636857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148702724544561724683515809 111527043408421293512636857)
        ·
          refine ⟨83645282556315970134477643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111527043408421293512636857 83645282556315970134477643)
          ·
            refine ⟨125467923834473955201716465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83645282556315970134477643 125467923834473955201716465)
            ·
              refine ⟨94100942875855466401287349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125467923834473955201716465 94100942875855466401287349)
              ·
                refine ⟨8821963394611449975120689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94100942875855466401287349 8821963394611449975120689)
                ·
                  refine ⟨6616472545958587481340517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8821963394611449975120689 6616472545958587481340517)
                  ·
                    refine ⟨1240588602367235152751347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6616472545958587481340517 1240588602367235152751347)
                    ·
                      rfl

theorem cell23_7248113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_7248113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248113 prefixEnd_7248113 := by exact prefixLift 7248113
  have htrace : WordTrace (prefixWord ++ tailWord_7248113) baseStart_7248113 baseEnd_7248113 := by
    simpa [prefixWord, tailWord_7248113, baseEnd_7248113] using wordTrace_append hprefix tailTrace_7248113
  have hstable : (prefixWord ++ tailWord_7248113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248113).length < 2 ^ (prefixWord ++ tailWord_7248113).sum := by decide
  have hdescent : baseEnd_7248113 < baseStart_7248113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248130 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_7248130 : Nat := 118140960795 + 7248130 * 2 ^ 59
def prefixEnd_7248130 : Nat := 4983230072969 + 3 ^ 40 * 7248130 * 2
def baseEnd_7248130 : Nat := 1240591512090943963913821

theorem tailTrace_7248130 : CollatzResearch.WordTrace tailWord_7248130 prefixEnd_7248130 1240591512090943963913821 := by
  unfold tailWord_7248130
  simp only [CollatzResearch.WordTrace]
  refine ⟨66090254807817591724071461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176240679487513577930857229 66090254807817591724071461)
  ·
    refine ⟨12391922776465798448263399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66090254807817591724071461 12391922776465798448263399)
    ·
      refine ⟨18587884164698697672395099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12391922776465798448263399 18587884164698697672395099)
      ·
        refine ⟨27881826247048046508592649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18587884164698697672395099 27881826247048046508592649)
        ·
          refine ⟨20911369685286034881444487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27881826247048046508592649 20911369685286034881444487)
          ·
            refine ⟨31367054527929052322166731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20911369685286034881444487 31367054527929052322166731)
            ·
              refine ⟨47050581791893578483250097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31367054527929052322166731 47050581791893578483250097)
              ·
                refine ⟨35287936343920183862437573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47050581791893578483250097 35287936343920183862437573)
                ·
                  refine ⟨6616488064485034474207045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35287936343920183862437573 6616488064485034474207045)
                  ·
                    refine ⟨1240591512090943963913821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6616488064485034474207045 1240591512090943963913821)
                    ·
                      rfl

theorem cell23_7248130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_7248130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248130 prefixEnd_7248130 := by exact prefixLift 7248130
  have htrace : WordTrace (prefixWord ++ tailWord_7248130) baseStart_7248130 baseEnd_7248130 := by
    simpa [prefixWord, tailWord_7248130, baseEnd_7248130] using wordTrace_append hprefix tailTrace_7248130
  have hstable : (prefixWord ++ tailWord_7248130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248130).length < 2 ^ (prefixWord ++ tailWord_7248130).sum := by decide
  have hdescent : baseEnd_7248130 < baseStart_7248130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248154 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2]
def baseStart_7248154 : Nat := 118140960795 + 7248154 * 2 ^ 59
def prefixEnd_7248154 : Nat := 4983230072969 + 3 ^ 40 * 7248154 * 2
def baseEnd_7248154 : Nat := 3721786859808539797841353

theorem tailTrace_7248154 : CollatzResearch.WordTrace tailWord_7248154 prefixEnd_7248154 3721786859808539797841353 := by
  unfold tailWord_7248154
  simp only [CollatzResearch.WordTrace]
  refine ⟨66090473645795854748789879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176241263055455612663439677 66090473645795854748789879)
  ·
    refine ⟨99135710468693782123184819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66090473645795854748789879 99135710468693782123184819)
    ·
      refine ⟨148703565703040673184777229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99135710468693782123184819 148703565703040673184777229)
      ·
        refine ⟨55763837138640252444291461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148703565703040673184777229 55763837138640252444291461)
        ·
          refine ⟨10455719463495047333304649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55763837138640252444291461 10455719463495047333304649)
          ·
            refine ⟨7841789597621285499978487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10455719463495047333304649 7841789597621285499978487)
            ·
              refine ⟨11762684396431928249967731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841789597621285499978487 11762684396431928249967731)
              ·
                refine ⟨17644026594647892374951597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11762684396431928249967731 17644026594647892374951597)
                ·
                  refine ⟨6616509972992959640606849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17644026594647892374951597 6616509972992959640606849)
                  ·
                    refine ⟨4962382479744719730455137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6616509972992959640606849 4962382479744719730455137)
                    ·
                      refine ⟨3721786859808539797841353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962382479744719730455137 3721786859808539797841353)
                      ·
                        rfl

theorem cell23_7248154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_7248154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248154 prefixEnd_7248154 := by exact prefixLift 7248154
  have htrace : WordTrace (prefixWord ++ tailWord_7248154) baseStart_7248154 baseEnd_7248154 := by
    simpa [prefixWord, tailWord_7248154, baseEnd_7248154] using wordTrace_append hprefix tailTrace_7248154
  have hstable : (prefixWord ++ tailWord_7248154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248154).length < 2 ^ (prefixWord ++ tailWord_7248154).sum := by decide
  have hdescent : baseEnd_7248154 < baseStart_7248154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248156 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_7248156 : Nat := 118140960795 + 7248156 * 2 ^ 59
def prefixEnd_7248156 : Nat := 4983230072969 + 3 ^ 40 * 7248156 * 2
def baseEnd_7248156 : Nat := 1240595962256616263338781

theorem tailTrace_7248156 : CollatzResearch.WordTrace tailWord_7248156 prefixEnd_7248156 1240595962256616263338781 := by
  unfold tailWord_7248156
  simp only [CollatzResearch.WordTrace]
  refine ⟨132180983764588086668366161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176241311686117448891154881 132180983764588086668366161)
  ·
    refine ⟨99135737823441065001274621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132180983764588086668366161 99135737823441065001274621)
    ·
      refine ⟨37175901683790399375477983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99135737823441065001274621 37175901683790399375477983)
      ·
        refine ⟨55763852525685599063216975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37175901683790399375477983 55763852525685599063216975)
        ·
          refine ⟨83645778788528398594825463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55763852525685599063216975 83645778788528398594825463)
          ·
            refine ⟨125468668182792597892238195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83645778788528398594825463 125468668182792597892238195)
            ·
              refine ⟨188203002274188896838357293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125468668182792597892238195 188203002274188896838357293)
              ·
                refine ⟨70576125852820836314383985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188203002274188896838357293 70576125852820836314383985)
                ·
                  refine ⟨52932094389615627235787989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70576125852820836314383985 52932094389615627235787989)
                  ·
                    refine ⟨1240595962256616263338781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52932094389615627235787989 1240595962256616263338781)
                    ·
                      rfl

theorem cell23_7248156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_7248156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248156 prefixEnd_7248156 := by exact prefixLift 7248156
  have htrace : WordTrace (prefixWord ++ tailWord_7248156) baseStart_7248156 baseEnd_7248156 := by
    simpa [prefixWord, tailWord_7248156, baseEnd_7248156] using wordTrace_append hprefix tailTrace_7248156
  have hstable : (prefixWord ++ tailWord_7248156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248156).length < 2 ^ (prefixWord ++ tailWord_7248156).sum := by decide
  have hdescent : baseEnd_7248156 < baseStart_7248156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248176 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 4]
def baseStart_7248176 : Nat := 118140960795 + 7248176 * 2 ^ 59
def prefixEnd_7248176 : Nat := 4983230072969 + 3 ^ 40 * 7248176 * 2
def baseEnd_7248176 : Nat := 3721798156382938711766251

theorem tailTrace_7248176 : CollatzResearch.WordTrace tailWord_7248176 prefixEnd_7248176 3721798156382938711766251 := by
  unfold tailWord_7248176
  simp only [CollatzResearch.WordTrace]
  refine ⟨132181348494551858376230191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176241797992735811168306921 132181348494551858376230191)
  ·
    refine ⟨198272022741827787564345287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132181348494551858376230191 198272022741827787564345287)
    ·
      refine ⟨297408034112741681346517931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198272022741827787564345287 297408034112741681346517931)
      ·
        refine ⟨446112051169112522019776897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297408034112741681346517931 446112051169112522019776897)
        ·
          refine ⟨334584038376834391514832673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446112051169112522019776897 334584038376834391514832673)
          ·
            refine ⟨250938028782625793636124505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334584038376834391514832673 250938028782625793636124505)
            ·
              refine ⟨188203521586969345227093379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250938028782625793636124505 188203521586969345227093379)
              ·
                refine ⟨282305282380454017840640069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188203521586969345227093379 282305282380454017840640069)
                ·
                  refine ⟨52932240446335128345120013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282305282380454017840640069 52932240446335128345120013)
                  ·
                    refine ⟨19849590167375673129420005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52932240446335128345120013 19849590167375673129420005)
                    ·
                      refine ⟨3721798156382938711766251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19849590167375673129420005 3721798156382938711766251)
                      ·
                        rfl

theorem cell23_7248176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_7248176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248176 prefixEnd_7248176 := by exact prefixLift 7248176
  have htrace : WordTrace (prefixWord ++ tailWord_7248176) baseStart_7248176 baseEnd_7248176 := by
    simpa [prefixWord, tailWord_7248176, baseEnd_7248176] using wordTrace_append hprefix tailTrace_7248176
  have hstable : (prefixWord ++ tailWord_7248176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248176).length < 2 ^ (prefixWord ++ tailWord_7248176).sum := by decide
  have hdescent : baseEnd_7248176 < baseStart_7248176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248227 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 2, 2, 2]
def baseStart_7248227 : Nat := 118140960795 + 7248227 * 2 ^ 59
def prefixEnd_7248227 : Nat := 4983230072969 + 3 ^ 40 * 7248227 * 2
def baseEnd_7248227 : Nat := 3721824343896318012228517

theorem tailTrace_7248227 : CollatzResearch.WordTrace tailWord_7248227 prefixEnd_7248227 3721824343896318012228517 := by
  unfold tailWord_7248227
  simp only [CollatzResearch.WordTrace]
  refine ⟨264364557111918952462566935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176243038074612634975044623 264364557111918952462566935)
  ·
    refine ⟨396546835667878428693850403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264364557111918952462566935 396546835667878428693850403)
    ·
      refine ⟨594820253501817643040775605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396546835667878428693850403 594820253501817643040775605)
      ·
        refine ⟨55764398765795404035072713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 594820253501817643040775605 55764398765795404035072713)
        ·
          refine ⟨41823299074346553026304535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55764398765795404035072713 41823299074346553026304535)
          ·
            refine ⟨62734948611519829539456803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41823299074346553026304535 62734948611519829539456803)
            ·
              refine ⟨94102422917279744309185205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62734948611519829539456803 94102422917279744309185205)
              ·
                refine ⟨8822102148494976028986113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94102422917279744309185205 8822102148494976028986113)
                ·
                  refine ⟨6616576611371232021739585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8822102148494976028986113 6616576611371232021739585)
                  ·
                    refine ⟨4962432458528424016304689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6616576611371232021739585 4962432458528424016304689)
                    ·
                      refine ⟨3721824343896318012228517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962432458528424016304689 3721824343896318012228517)
                      ·
                        rfl

theorem cell23_7248227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_7248227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248227 prefixEnd_7248227 := by exact prefixLift 7248227
  have htrace : WordTrace (prefixWord ++ tailWord_7248227) baseStart_7248227 baseEnd_7248227 := by
    simpa [prefixWord, tailWord_7248227, baseEnd_7248227] using wordTrace_append hprefix tailTrace_7248227
  have hstable : (prefixWord ++ tailWord_7248227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248227).length < 2 ^ (prefixWord ++ tailWord_7248227).sum := by decide
  have hdescent : baseEnd_7248227 < baseStart_7248227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248263 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 4, 5]
def baseStart_7248263 : Nat := 118140960795 + 7248263 * 2 ^ 59
def prefixEnd_7248263 : Nat := 4983230072969 + 3 ^ 40 * 7248263 * 2
def baseEnd_7248263 : Nat := 1240614276399959957126117

theorem tailTrace_7248263 : CollatzResearch.WordTrace tailWord_7248263 prefixEnd_7248263 1240614276399959957126117 := by
  unfold tailWord_7248263
  simp only [CollatzResearch.WordTrace]
  refine ⟨264365870139788530610877443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176243913426525687073918295 264365870139788530610877443)
  ·
    refine ⟨396548805209682795916316165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264365870139788530610877443 396548805209682795916316165)
    ·
      refine ⟨74352900976815524234309281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396548805209682795916316165 74352900976815524234309281)
      ·
        refine ⟨55764675732611643175731961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74352900976815524234309281 55764675732611643175731961)
        ·
          refine ⟨41823506799458732381798971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55764675732611643175731961 41823506799458732381798971)
          ·
            refine ⟨62735260199188098572698457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41823506799458732381798971 62735260199188098572698457)
            ·
              refine ⟨47051445149391073929523843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62735260199188098572698457 47051445149391073929523843)
              ·
                refine ⟨70577167724086610894285765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47051445149391073929523843 70577167724086610894285765)
                ·
                  refine ⟨13233218948266239542678581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70577167724086610894285765 13233218948266239542678581)
                  ·
                    refine ⟨1240614276399959957126117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13233218948266239542678581 1240614276399959957126117)
                    ·
                      rfl

theorem cell23_7248263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_7248263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248263 prefixEnd_7248263 := by exact prefixLift 7248263
  have htrace : WordTrace (prefixWord ++ tailWord_7248263) baseStart_7248263 baseEnd_7248263 := by
    simpa [prefixWord, tailWord_7248263, baseEnd_7248263] using wordTrace_append hprefix tailTrace_7248263
  have hstable : (prefixWord ++ tailWord_7248263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248263).length < 2 ^ (prefixWord ++ tailWord_7248263).sum := by decide
  have hdescent : baseEnd_7248263 < baseStart_7248263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248301 : List Nat := [1, 5, 2, 2, 3, 1, 1, 3, 5]
def baseStart_7248301 : Nat := 118140960795 + 7248301 * 2 ^ 59
def prefixEnd_7248301 : Nat := 4983230072969 + 3 ^ 40 * 7248301 * 2
def baseEnd_7248301 : Nat := 413540260162750080300353

theorem tailTrace_7248301 : CollatzResearch.WordTrace tailWord_7248301 prefixEnd_7248301 413540260162750080300353 := by
  unfold tailWord_7248301
  simp only [CollatzResearch.WordTrace]
  refine ⟨264367256113650863100760757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176244837409100575400507171 264367256113650863100760757)
  ·
    refine ⟨24784430260654768415696321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264367256113650863100760757 24784430260654768415696321)
    ·
      refine ⟨18588322695491076311772241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24784430260654768415696321 18588322695491076311772241)
      ·
        refine ⟨13941242021618307233829181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18588322695491076311772241 13941242021618307233829181)
        ·
          refine ⟨5227965758106865212685943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13941242021618307233829181 5227965758106865212685943)
          ·
            refine ⟨7841948637160297819028915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5227965758106865212685943 7841948637160297819028915)
            ·
              refine ⟨11762922955740446728543373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841948637160297819028915 11762922955740446728543373)
              ·
                refine ⟨4411096108402667523203765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11762922955740446728543373 4411096108402667523203765)
                ·
                  refine ⟨413540260162750080300353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4411096108402667523203765 413540260162750080300353)
                  ·
                    rfl

theorem cell23_7248301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_7248301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248301 prefixEnd_7248301 := by exact prefixLift 7248301
  have htrace : WordTrace (prefixWord ++ tailWord_7248301) baseStart_7248301 baseEnd_7248301 := by
    simpa [prefixWord, tailWord_7248301, baseEnd_7248301] using wordTrace_append hprefix tailTrace_7248301
  have hstable : (prefixWord ++ tailWord_7248301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248301).length < 2 ^ (prefixWord ++ tailWord_7248301).sum := by decide
  have hdescent : baseEnd_7248301 < baseStart_7248301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248323 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 6]
def baseStart_7248323 : Nat := 118140960795 + 7248323 * 2 ^ 59
def prefixEnd_7248323 : Nat := 4983230072969 + 3 ^ 40 * 7248323 * 2
def baseEnd_7248323 : Nat := 413541515337683292958675

theorem tailTrace_7248323 : CollatzResearch.WordTrace tailWord_7248323 prefixEnd_7248323 413541515337683292958675 := by
  unfold tailWord_7248323
  simp only [CollatzResearch.WordTrace]
  refine ⟨264368058519571160858061623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176245372346380773905374415 264368058519571160858061623)
  ·
    refine ⟨396552087779356741287092435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264368058519571160858061623 396552087779356741287092435)
    ·
      refine ⟨594828131669035111930638653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396552087779356741287092435 594828131669035111930638653)
      ·
        refine ⟨223060549375888166973989495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594828131669035111930638653 223060549375888166973989495)
        ·
          refine ⟨334590824063832250460984243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223060549375888166973989495 334590824063832250460984243)
          ·
            refine ⟨501886236095748375691476365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334590824063832250460984243 501886236095748375691476365)
            ·
              refine ⟨188207338535905640884303637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501886236095748375691476365 188207338535905640884303637)
              ·
                refine ⟨8822218993870576916451733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188207338535905640884303637 8822218993870576916451733)
                ·
                  refine ⟨413541515337683292958675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8822218993870576916451733 413541515337683292958675)
                  ·
                    rfl

theorem cell23_7248323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 6].length) (baseStart_7248323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248323 prefixEnd_7248323 := by exact prefixLift 7248323
  have htrace : WordTrace (prefixWord ++ tailWord_7248323) baseStart_7248323 baseEnd_7248323 := by
    simpa [prefixWord, tailWord_7248323, baseEnd_7248323] using wordTrace_append hprefix tailTrace_7248323
  have hstable : (prefixWord ++ tailWord_7248323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248323).length < 2 ^ (prefixWord ++ tailWord_7248323).sum := by decide
  have hdescent : baseEnd_7248323 < baseStart_7248323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248327 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 3, 4]
def baseStart_7248327 : Nat := 118140960795 + 7248327 * 2 ^ 59
def prefixEnd_7248327 : Nat := 4983230072969 + 3 ^ 40 * 7248327 * 2
def baseEnd_7248327 : Nat := 1240625230653922540326019

theorem tailTrace_7248327 : CollatzResearch.WordTrace tailWord_7248327 prefixEnd_7248327 1240625230653922540326019 := by
  unfold tailWord_7248327
  simp only [CollatzResearch.WordTrace]
  refine ⟨264368204411556669541207235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176245469607704446360804823 264368204411556669541207235)
  ·
    refine ⟨396552306617335004311810853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264368204411556669541207235 396552306617335004311810853)
    ·
      refine ⟨74353557490750313308464535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396552306617335004311810853 74353557490750313308464535)
      ·
        refine ⟨111530336236125469962696803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74353557490750313308464535 111530336236125469962696803)
        ·
          refine ⟨167295504354188204944045205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111530336236125469962696803 167295504354188204944045205)
          ·
            refine ⟨7841976766602572106752119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167295504354188204944045205 7841976766602572106752119)
            ·
              refine ⟨11762965149903858160128179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7841976766602572106752119 11762965149903858160128179)
              ·
                refine ⟨17644447724855787240192269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11762965149903858160128179 17644447724855787240192269)
                ·
                  refine ⟨6616667896820920215072101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17644447724855787240192269 6616667896820920215072101)
                  ·
                    refine ⟨1240625230653922540326019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6616667896820920215072101 1240625230653922540326019)
                    ·
                      rfl

theorem cell23_7248327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_7248327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248327 prefixEnd_7248327 := by exact prefixLift 7248327
  have htrace : WordTrace (prefixWord ++ tailWord_7248327) baseStart_7248327 baseEnd_7248327 := by
    simpa [prefixWord, tailWord_7248327, baseEnd_7248327] using wordTrace_append hprefix tailTrace_7248327
  have hstable : (prefixWord ++ tailWord_7248327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248327).length < 2 ^ (prefixWord ++ tailWord_7248327).sum := by decide
  have hdescent : baseEnd_7248327 < baseStart_7248327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248377 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 2, 3, 2]
def baseStart_7248377 : Nat := 118140960795 + 7248377 * 2 ^ 59
def prefixEnd_7248377 : Nat := 4983230072969 + 3 ^ 40 * 7248377 * 2
def baseEnd_7248377 : Nat := 3721901365994492425352827

theorem tailTrace_7248377 : CollatzResearch.WordTrace tailWord_7248377 prefixEnd_7248377 3721901365994492425352827 := by
  unfold tailWord_7248377
  simp only [CollatzResearch.WordTrace]
  refine ⟨264370028061375528080527385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176246685374250352053684923 264370028061375528080527385)
  ·
    refine ⟨198277521046031646060395539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264370028061375528080527385 198277521046031646060395539)
    ·
      refine ⟨297416281569047469090593309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198277521046031646060395539 297416281569047469090593309)
      ·
        refine ⟨111531105588392800908972491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297416281569047469090593309 111531105588392800908972491)
        ·
          refine ⟨167296658382589201363458737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111531105588392800908972491 167296658382589201363458737)
          ·
            refine ⟨125472493786941901022594053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167296658382589201363458737 125472493786941901022594053)
            ·
              refine ⟨23526092585051606441736385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125472493786941901022594053 23526092585051606441736385)
              ·
                refine ⟨17644569438788704831302289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23526092585051606441736385 17644569438788704831302289)
                ·
                  refine ⟨13233427079091528623476717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17644569438788704831302289 13233427079091528623476717)
                  ·
                    refine ⟨4962535154659323233803769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13233427079091528623476717 4962535154659323233803769)
                    ·
                      refine ⟨3721901365994492425352827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962535154659323233803769 3721901365994492425352827)
                      ·
                        rfl

theorem cell23_7248377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_7248377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248377 prefixEnd_7248377 := by exact prefixLift 7248377
  have htrace : WordTrace (prefixWord ++ tailWord_7248377) baseStart_7248377 baseEnd_7248377 := by
    simpa [prefixWord, tailWord_7248377, baseEnd_7248377] using wordTrace_append hprefix tailTrace_7248377
  have hstable : (prefixWord ++ tailWord_7248377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248377).length < 2 ^ (prefixWord ++ tailWord_7248377).sum := by decide
  have hdescent : baseEnd_7248377 < baseStart_7248377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248383 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 3, 6]
def baseStart_7248383 : Nat := 118140960795 + 7248383 * 2 ^ 59
def prefixEnd_7248383 : Nat := 4983230072969 + 3 ^ 40 * 7248383 * 2
def baseEnd_7248383 : Nat := 1240634815626139800625933

theorem tailTrace_7248383 : CollatzResearch.WordTrace tailWord_7248383 prefixEnd_7248383 1240634815626139800625933 := by
  unfold tailWord_7248383
  simp only [CollatzResearch.WordTrace]
  refine ⟨264370246899353791105245803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176246831266235860736830535 264370246899353791105245803)
  ·
    refine ⟨396555370349030686657868705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264370246899353791105245803 396555370349030686657868705)
    ·
      refine ⟨297416527761773014993401529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396555370349030686657868705 297416527761773014993401529)
      ·
        refine ⟨223062395821329761245051147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297416527761773014993401529 223062395821329761245051147)
        ·
          refine ⟨334593593731994641867576721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223062395821329761245051147 334593593731994641867576721)
          ·
            refine ⟨250945195298995981400682541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334593593731994641867576721 250945195298995981400682541)
            ·
              refine ⟨94104448237123493025255953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250945195298995981400682541 94104448237123493025255953)
              ·
                refine ⟨70578336177842619768941965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94104448237123493025255953 70578336177842619768941965)
                ·
                  refine ⟨26466876066690982413353237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70578336177842619768941965 26466876066690982413353237)
                  ·
                    refine ⟨1240634815626139800625933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26466876066690982413353237 1240634815626139800625933)
                    ·
                      rfl

theorem cell23_7248383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_7248383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248383 prefixEnd_7248383 := by exact prefixLift 7248383
  have htrace : WordTrace (prefixWord ++ tailWord_7248383) baseStart_7248383 baseEnd_7248383 := by
    simpa [prefixWord, tailWord_7248383, baseEnd_7248383] using wordTrace_append hprefix tailTrace_7248383
  have hstable : (prefixWord ++ tailWord_7248383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248383).length < 2 ^ (prefixWord ++ tailWord_7248383).sum := by decide
  have hdescent : baseEnd_7248383 < baseStart_7248383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248424 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_7248424 : Nat := 118140960795 + 7248424 * 2 ^ 59
def prefixEnd_7248424 : Nat := 4983230072969 + 3 ^ 40 * 7248424 * 2
def baseEnd_7248424 : Nat := 3721925499585253741465111

theorem tailTrace_7248424 : CollatzResearch.WordTrace tailWord_7248424 prefixEnd_7248424 3721925499585253741465111 := by
  unfold tailWord_7248424
  simp only [CollatzResearch.WordTrace]
  refine ⟨132185871146102627553744163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176247828194803503404992217 132185871146102627553744163)
  ·
    refine ⟨198278806719153941330616245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132185871146102627553744163 198278806719153941330616245)
    ·
      refine ⟨18588638129920681999745273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198278806719153941330616245 18588638129920681999745273)
      ·
        refine ⟨13941478597440511499808955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18588638129920681999745273 13941478597440511499808955)
        ·
          refine ⟨20912217896160767249713433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13941478597440511499808955 20912217896160767249713433)
          ·
            refine ⟨15684163422120575437285075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20912217896160767249713433 15684163422120575437285075)
            ·
              refine ⟨23526245133180863155927613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15684163422120575437285075 23526245133180863155927613)
              ·
                refine ⟨8822341924942823683472855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23526245133180863155927613 8822341924942823683472855)
                ·
                  refine ⟨13233512887414235525209283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8822341924942823683472855 13233512887414235525209283)
                  ·
                    refine ⟨19850269331121353287813925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13233512887414235525209283 19850269331121353287813925)
                    ·
                      refine ⟨3721925499585253741465111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19850269331121353287813925 3721925499585253741465111)
                      ·
                        rfl

theorem cell23_7248424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_7248424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248424 prefixEnd_7248424 := by exact prefixLift 7248424
  have htrace : WordTrace (prefixWord ++ tailWord_7248424) baseStart_7248424 baseEnd_7248424 := by
    simpa [prefixWord, tailWord_7248424, baseEnd_7248424] using wordTrace_append hprefix tailTrace_7248424
  have hstable : (prefixWord ++ tailWord_7248424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248424).length < 2 ^ (prefixWord ++ tailWord_7248424).sum := by decide
  have hdescent : baseEnd_7248424 < baseStart_7248424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248441 : List Nat := [1, 2, 1, 5, 1, 1, 1, 6, 1, 2, 2]
def baseStart_7248441 : Nat := 118140960795 + 7248441 * 2 ^ 59
def prefixEnd_7248441 : Nat := 4983230072969 + 3 ^ 40 * 7248441 * 2
def baseEnd_7248441 : Nat := 3721934228756380174952533

theorem tailTrace_7248441 : CollatzResearch.WordTrace tailWord_7248441 prefixEnd_7248441 3721934228756380174952533 := by
  unfold tailWord_7248441
  simp only [CollatzResearch.WordTrace]
  refine ⟨264372362333143667010857177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176248241555429111340571451 264372362333143667010857177)
  ·
    refine ⟨198279271749857750258142883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264372362333143667010857177 198279271749857750258142883)
    ·
      refine ⟨297418907624786625387214325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198279271749857750258142883 297418907624786625387214325)
      ·
        refine ⟨27883022589823746130051343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 297418907624786625387214325 27883022589823746130051343)
        ·
          refine ⟨41824533884735619195077015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27883022589823746130051343 41824533884735619195077015)
          ·
            refine ⟨62736800827103428792615523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41824533884735619195077015 62736800827103428792615523)
            ·
              refine ⟨94105201240655143188923285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62736800827103428792615523 94105201240655143188923285)
              ·
                refine ⟨4411181308155709836980779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94105201240655143188923285 4411181308155709836980779)
                ·
                  refine ⟨6616771962233564755471169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411181308155709836980779 6616771962233564755471169)
                  ·
                    refine ⟨4962578971675173566603377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6616771962233564755471169 4962578971675173566603377)
                    ·
                      refine ⟨3721934228756380174952533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962578971675173566603377 3721934228756380174952533)
                      ·
                        rfl

theorem cell23_7248441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_7248441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248441 prefixEnd_7248441 := by exact prefixLift 7248441
  have htrace : WordTrace (prefixWord ++ tailWord_7248441) baseStart_7248441 baseEnd_7248441 := by
    simpa [prefixWord, tailWord_7248441, baseEnd_7248441] using wordTrace_append hprefix tailTrace_7248441
  have hstable : (prefixWord ++ tailWord_7248441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248441).length < 2 ^ (prefixWord ++ tailWord_7248441).sum := by decide
  have hdescent : baseEnd_7248441 < baseStart_7248441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248443 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 6, 7]
def baseStart_7248443 : Nat := 118140960795 + 7248443 * 2 ^ 59
def prefixEnd_7248443 : Nat := 4983230072969 + 3 ^ 40 * 7248443 * 2
def baseEnd_7248443 : Nat := 1240645085239229722375841

theorem tailTrace_7248443 : CollatzResearch.WordTrace tailWord_7248443 prefixEnd_7248443 1240645085239229722375841 := by
  unfold tailWord_7248443
  simp only [CollatzResearch.WordTrace]
  refine ⟨264372435279136421352429983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176248290186090947568286655 264372435279136421352429983)
  ·
    refine ⟨396558652918704632028644975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264372435279136421352429983 396558652918704632028644975)
    ·
      refine ⟨594837979378056948042967463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396558652918704632028644975 594837979378056948042967463)
      ·
        refine ⟨892256969067085422064451195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594837979378056948042967463 892256969067085422064451195)
        ·
          refine ⟨1338385453600628133096676793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892256969067085422064451195 1338385453600628133096676793)
          ·
            refine ⟨1003789090200471099822507595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338385453600628133096676793 1003789090200471099822507595)
            ·
              refine ⟨1505683635300706649733761393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003789090200471099822507595 1505683635300706649733761393)
              ·
                refine ⟨1129262726475529987300321045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1505683635300706649733761393 1129262726475529987300321045)
                ·
                  refine ⟨52934190303540468154702549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1129262726475529987300321045 52934190303540468154702549)
                  ·
                    refine ⟨1240645085239229722375841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52934190303540468154702549 1240645085239229722375841)
                    ·
                      rfl

theorem cell23_7248443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 7].length) (baseStart_7248443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248443 prefixEnd_7248443 := by exact prefixLift 7248443
  have htrace : WordTrace (prefixWord ++ tailWord_7248443) baseStart_7248443 baseEnd_7248443 := by
    simpa [prefixWord, tailWord_7248443, baseEnd_7248443] using wordTrace_append hprefix tailTrace_7248443
  have hstable : (prefixWord ++ tailWord_7248443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248443).length < 2 ^ (prefixWord ++ tailWord_7248443).sum := by decide
  have hdescent : baseEnd_7248443 < baseStart_7248443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248454 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7248454 : Nat := 118140960795 + 7248454 * 2 ^ 59
def prefixEnd_7248454 : Nat := 4983230072969 + 3 ^ 40 * 7248454 * 2
def baseEnd_7248454 : Nat := 3721940904004888624089973

theorem tailTrace_7248454 : CollatzResearch.WordTrace tailWord_7248454 prefixEnd_7248454 3721940904004888624089973 := by
  unfold tailWord_7248454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8261651140065517819721263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176248557654731046820720277 8261651140065517819721263)
  ·
    refine ⟨12392476710098276729581895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8261651140065517819721263 12392476710098276729581895)
    ·
      refine ⟨18588715065147415094372843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12392476710098276729581895 18588715065147415094372843)
      ·
        refine ⟨27883072597721122641559265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18588715065147415094372843 27883072597721122641559265)
        ·
          refine ⟨20912304448290841981169449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27883072597721122641559265 20912304448290841981169449)
          ·
            refine ⟨15684228336218131485877087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20912304448290841981169449 15684228336218131485877087)
            ·
              refine ⟨23526342504327197228815631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15684228336218131485877087 23526342504327197228815631)
              ·
                refine ⟨35289513756490795843223447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23526342504327197228815631 35289513756490795843223447)
                ·
                  refine ⟨52934270634736193764835171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35289513756490795843223447 52934270634736193764835171)
                  ·
                    refine ⟨79401405952104290647252757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52934270634736193764835171 79401405952104290647252757)
                    ·
                      refine ⟨3721940904004888624089973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79401405952104290647252757 3721940904004888624089973)
                      ·
                        rfl

theorem cell23_7248454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7248454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248454 prefixEnd_7248454 := by exact prefixLift 7248454
  have htrace : WordTrace (prefixWord ++ tailWord_7248454) baseStart_7248454 baseEnd_7248454 := by
    simpa [prefixWord, tailWord_7248454, baseEnd_7248454] using wordTrace_append hprefix tailTrace_7248454
  have hstable : (prefixWord ++ tailWord_7248454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248454).length < 2 ^ (prefixWord ++ tailWord_7248454).sum := by decide
  have hdescent : baseEnd_7248454 < baseStart_7248454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248461 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_7248461 : Nat := 118140960795 + 7248461 * 2 ^ 59
def prefixEnd_7248461 : Nat := 4983230072969 + 3 ^ 40 * 7248461 * 2
def baseEnd_7248461 : Nat := 3721944498369470096702441

theorem tailTrace_7248461 : CollatzResearch.WordTrace tailWord_7248461 prefixEnd_7248461 3721944498369470096702441 := by
  unfold tailWord_7248461
  simp only [CollatzResearch.WordTrace]
  refine ⟨264373091793071210426585237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176248727862047473617723491 264373091793071210426585237)
  ·
    refine ⟨12392488677800212988746183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 264373091793071210426585237 12392488677800212988746183)
    ·
      refine ⟨18588733016700319483119275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12392488677800212988746183 18588733016700319483119275)
      ·
        refine ⟨27883099525050479224678913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18588733016700319483119275 27883099525050479224678913)
        ·
          refine ⟨20912324643787859418509185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27883099525050479224678913 20912324643787859418509185)
          ·
            refine ⟨15684243482840894563881889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20912324643787859418509185 15684243482840894563881889)
            ·
              refine ⟨11763182612130670922911417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15684243482840894563881889 11763182612130670922911417)
              ·
                refine ⟨8822386959098003192183563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11763182612130670922911417 8822386959098003192183563)
                ·
                  refine ⟨13233580438647004788275345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8822386959098003192183563 13233580438647004788275345)
                  ·
                    refine ⟨9925185328985253591206509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13233580438647004788275345 9925185328985253591206509)
                    ·
                      refine ⟨3721944498369470096702441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9925185328985253591206509 3721944498369470096702441)
                      ·
                        rfl

theorem cell23_7248461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_7248461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248461 prefixEnd_7248461 := by exact prefixLift 7248461
  have htrace : WordTrace (prefixWord ++ tailWord_7248461) baseStart_7248461 baseEnd_7248461 := by
    simpa [prefixWord, tailWord_7248461, baseEnd_7248461] using wordTrace_append hprefix tailTrace_7248461
  have hstable : (prefixWord ++ tailWord_7248461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248461).length < 2 ^ (prefixWord ++ tailWord_7248461).sum := by decide
  have hdescent : baseEnd_7248461 < baseStart_7248461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248478 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7248478 : Nat := 118140960795 + 7248478 * 2 ^ 59
def prefixEnd_7248478 : Nat := 4983230072969 + 3 ^ 40 * 7248478 * 2
def baseEnd_7248478 : Nat := 3721953227540596530189863

theorem tailTrace_7248478 : CollatzResearch.WordTrace tailWord_7248478 prefixEnd_7248478 3721953227540596530189863 := by
  unfold tailWord_7248478
  simp only [CollatzResearch.WordTrace]
  refine ⟨33046713979251202791244261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176249141222673081553302725 33046713979251202791244261)
  ·
    refine ⟨6196258871109600523358299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33046713979251202791244261 6196258871109600523358299)
    ·
      refine ⟨9294388306664400785037449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6196258871109600523358299 9294388306664400785037449)
      ·
        refine ⟨6970791229998300588778087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9294388306664400785037449 6970791229998300588778087)
        ·
          refine ⟨10456186844997450883167131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6970791229998300588778087 10456186844997450883167131)
          ·
            refine ⟨15684280267496176324750697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10456186844997450883167131 15684280267496176324750697)
            ·
              refine ⟨11763210200622132243563023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15684280267496176324750697 11763210200622132243563023)
              ·
                refine ⟨17644815300933198365344535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11763210200622132243563023 17644815300933198365344535)
                ·
                  refine ⟨26467222951399797548016803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17644815300933198365344535 26467222951399797548016803)
                  ·
                    refine ⟨39700834427099696322025205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26467222951399797548016803 39700834427099696322025205)
                    ·
                      refine ⟨3721953227540596530189863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39700834427099696322025205 3721953227540596530189863)
                      ·
                        rfl

theorem cell23_7248478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7248478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248478 prefixEnd_7248478 := by exact prefixLift 7248478
  have htrace : WordTrace (prefixWord ++ tailWord_7248478) baseStart_7248478 baseEnd_7248478 := by
    simpa [prefixWord, tailWord_7248478, baseEnd_7248478] using wordTrace_append hprefix tailTrace_7248478
  have hstable : (prefixWord ++ tailWord_7248478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248478).length < 2 ^ (prefixWord ++ tailWord_7248478).sum := by decide
  have hdescent : baseEnd_7248478 < baseStart_7248478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248484 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 1, 3, 2]
def baseStart_7248484 : Nat := 118140960795 + 7248484 * 2 ^ 59
def prefixEnd_7248484 : Nat := 4983230072969 + 3 ^ 40 * 7248484 * 2
def baseEnd_7248484 : Nat := 3721956308424523506714835

theorem tailTrace_7248484 : CollatzResearch.WordTrace tailWord_7248484 prefixEnd_7248484 3721956308424523506714835 := by
  unfold tailWord_7248484
  simp only [CollatzResearch.WordTrace]
  refine ⟨132186965335993942677336253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176249287114658590236448337 132186965335993942677336253)
  ·
    refine ⟨49570112000997728504001095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132186965335993942677336253 49570112000997728504001095)
    ·
      refine ⟨74355168001496592756001643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49570112000997728504001095 74355168001496592756001643)
      ·
        refine ⟨111532752002244889134002465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74355168001496592756001643 111532752002244889134002465)
        ·
          refine ⟨83649564001683666850501849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111532752002244889134002465 83649564001683666850501849)
          ·
            refine ⟨62737173001262750137876387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83649564001683666850501849 62737173001262750137876387)
            ·
              refine ⟨94105759501894125206814581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62737173001262750137876387 94105759501894125206814581)
              ·
                refine ⟨8822414953302574238138867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94105759501894125206814581 8822414953302574238138867)
                ·
                  refine ⟨13233622429953861357208301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8822414953302574238138867 13233622429953861357208301)
                  ·
                    refine ⟨4962608411232698008953113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13233622429953861357208301 4962608411232698008953113)
                    ·
                      refine ⟨3721956308424523506714835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962608411232698008953113 3721956308424523506714835)
                      ·
                        rfl

theorem cell23_7248484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_7248484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248484 prefixEnd_7248484 := by exact prefixLift 7248484
  have htrace : WordTrace (prefixWord ++ tailWord_7248484) baseStart_7248484 baseEnd_7248484 := by
    simpa [prefixWord, tailWord_7248484, baseEnd_7248484] using wordTrace_append hprefix tailTrace_7248484
  have hstable : (prefixWord ++ tailWord_7248484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248484).length < 2 ^ (prefixWord ++ tailWord_7248484).sum := by decide
  have hdescent : baseEnd_7248484 < baseStart_7248484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248537 : List Nat := [1, 2, 1, 2, 1, 2, 4, 5, 5]
def baseStart_7248537 : Nat := 118140960795 + 7248537 * 2 ^ 59
def prefixEnd_7248537 : Nat := 4983230072969 + 3 ^ 40 * 7248537 * 2
def baseEnd_7248537 : Nat := 413553724766579088816899

theorem tailTrace_7248537 : CollatzResearch.WordTrace tailWord_7248537 prefixEnd_7248537 413553724766579088816899 := by
  unfold tailWord_7248537
  simp only [CollatzResearch.WordTrace]
  refine ⟨264375863740795875406351865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176250575827197250270901243 264375863740795875406351865)
  ·
    refine ⟨198281897805596906554763899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264375863740795875406351865 198281897805596906554763899)
    ·
      refine ⟨297422846708395359832145849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198281897805596906554763899 297422846708395359832145849)
      ·
        refine ⟨223067135031296519874109387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297422846708395359832145849 223067135031296519874109387)
        ·
          refine ⟨334600702546944779811164081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223067135031296519874109387 334600702546944779811164081)
          ·
            refine ⟨250950526910208584858373061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334600702546944779811164081 250950526910208584858373061)
            ·
              refine ⟨47053223795664109660944949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250950526910208584858373061 47053223795664109660944949)
              ·
                refine ⟨4411239730843510280713589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47053223795664109660944949 4411239730843510280713589)
                ·
                  refine ⟨413553724766579088816899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4411239730843510280713589 413553724766579088816899)
                  ·
                    rfl

theorem cell23_7248537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 5].length) (baseStart_7248537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248537 prefixEnd_7248537 := by exact prefixLift 7248537
  have htrace : WordTrace (prefixWord ++ tailWord_7248537) baseStart_7248537 baseEnd_7248537 := by
    simpa [prefixWord, tailWord_7248537, baseEnd_7248537] using wordTrace_append hprefix tailTrace_7248537
  have hstable : (prefixWord ++ tailWord_7248537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248537).length < 2 ^ (prefixWord ++ tailWord_7248537).sum := by decide
  have hdescent : baseEnd_7248537 < baseStart_7248537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248574 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_7248574 : Nat := 118140960795 + 7248574 * 2 ^ 59
def prefixEnd_7248574 : Nat := 4983230072969 + 3 ^ 40 * 7248574 * 2
def baseEnd_7248574 : Nat := 3722002521683428154589421

theorem tailTrace_7248574 : CollatzResearch.WordTrace tailWord_7248574 prefixEnd_7248574 3722002521683428154589421 := by
  unfold tailWord_7248574
  simp only [CollatzResearch.WordTrace]
  refine ⟨33047151655207728840681097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176251475494441220483632517 33047151655207728840681097)
  ·
    refine ⟨24785363741405796630510823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33047151655207728840681097 24785363741405796630510823)
    ·
      refine ⟨37178045612108694945766235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24785363741405796630510823 37178045612108694945766235)
      ·
        refine ⟨55767068418163042418649353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37178045612108694945766235 55767068418163042418649353)
        ·
          refine ⟨41825301313622281813987015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55767068418163042418649353 41825301313622281813987015)
          ·
            refine ⟨62737951970433422720980523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41825301313622281813987015 62737951970433422720980523)
            ·
              refine ⟨94106927955650134081470785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62737951970433422720980523 94106927955650134081470785)
              ·
                refine ⟨70580195966737600561103089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94106927955650134081470785 70580195966737600561103089)
                ·
                  refine ⟨52935146975053200420827317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70580195966737600561103089 52935146975053200420827317)
                  ·
                    refine ⟨4962670028911237539452561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52935146975053200420827317 4962670028911237539452561)
                    ·
                      refine ⟨3722002521683428154589421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962670028911237539452561 3722002521683428154589421)
                      ·
                        rfl

theorem cell23_7248574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_7248574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248574 prefixEnd_7248574 := by exact prefixLift 7248574
  have htrace : WordTrace (prefixWord ++ tailWord_7248574) baseStart_7248574 baseEnd_7248574 := by
    simpa [prefixWord, tailWord_7248574, baseEnd_7248574] using wordTrace_append hprefix tailTrace_7248574
  have hstable : (prefixWord ++ tailWord_7248574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248574).length < 2 ^ (prefixWord ++ tailWord_7248574).sum := by decide
  have hdescent : baseEnd_7248574 < baseStart_7248574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248584 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 2, 5]
def baseStart_7248584 : Nat := 118140960795 + 7248584 * 2 ^ 59
def prefixEnd_7248584 : Nat := 4983230072969 + 3 ^ 40 * 7248584 * 2
def baseEnd_7248584 : Nat := 1240669218829991038488125

theorem tailTrace_7248584 : CollatzResearch.WordTrace tailWord_7248584 prefixEnd_7248584 1240669218829991038488125 := by
  unfold tailWord_7248584
  simp only [CollatzResearch.WordTrace]
  refine ⟨132188788985812801216656403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176251718647750401622208537 132188788985812801216656403)
  ·
    refine ⟨198283183478719201824984605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132188788985812801216656403 198283183478719201824984605)
    ·
      refine ⟨74356193804519700684369227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198283183478719201824984605 74356193804519700684369227)
      ·
        refine ⟨111534290706779551026553841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74356193804519700684369227 111534290706779551026553841)
        ·
          refine ⟨83650718030084663269915381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111534290706779551026553841 83650718030084663269915381)
          ·
            refine ⟨7842254815320437181554567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83650718030084663269915381 7842254815320437181554567)
            ·
              refine ⟨11763382222980655772331851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7842254815320437181554567 11763382222980655772331851)
              ·
                refine ⟨17645073334470983658497777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11763382222980655772331851 17645073334470983658497777)
                ·
                  refine ⟨13233805000853237743873333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17645073334470983658497777 13233805000853237743873333)
                  ·
                    refine ⟨1240669218829991038488125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13233805000853237743873333 1240669218829991038488125)
                    ·
                      rfl

theorem cell23_7248584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_7248584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248584 prefixEnd_7248584 := by exact prefixLift 7248584
  have htrace : WordTrace (prefixWord ++ tailWord_7248584) baseStart_7248584 baseEnd_7248584 := by
    simpa [prefixWord, tailWord_7248584, baseEnd_7248584] using wordTrace_append hprefix tailTrace_7248584
  have hstable : (prefixWord ++ tailWord_7248584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248584).length < 2 ^ (prefixWord ++ tailWord_7248584).sum := by decide
  have hdescent : baseEnd_7248584 < baseStart_7248584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248637 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_7248637 : Nat := 118140960795 + 7248637 * 2 ^ 59
def prefixEnd_7248637 : Nat := 4983230072969 + 3 ^ 40 * 7248637 * 2
def baseEnd_7248637 : Nat := 3722034870964661408101631

theorem tailTrace_7248637 : CollatzResearch.WordTrace tailWord_7248637 prefixEnd_7248637 3722034870964661408101631 := by
  unfold tailWord_7248637
  simp only [CollatzResearch.WordTrace]
  refine ⟨264379511040433592484992165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176253007360289061656661443 264379511040433592484992165)
  ·
    refine ⟨49571158320081298590936031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264379511040433592484992165 49571158320081298590936031)
    ·
      refine ⟨74356737480121947886404047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49571158320081298590936031 74356737480121947886404047)
      ·
        refine ⟨111535106220182921829606071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74356737480121947886404047 111535106220182921829606071)
        ·
          refine ⟨167302659330274382744409107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111535106220182921829606071 167302659330274382744409107)
          ·
            refine ⟨250953988995411574116613661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167302659330274382744409107 250953988995411574116613661)
            ·
              refine ⟨94107745873279340293730123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250953988995411574116613661 94107745873279340293730123)
              ·
                refine ⟨141161618809919010440595185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94107745873279340293730123 141161618809919010440595185)
                ·
                  refine ⟨105871214107439257830446389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141161618809919010440595185 105871214107439257830446389)
                  ·
                    refine ⟨9925426322572430421604349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105871214107439257830446389 9925426322572430421604349)
                    ·
                      refine ⟨3722034870964661408101631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9925426322572430421604349 3722034870964661408101631)
                      ·
                        rfl

theorem cell23_7248637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_7248637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248637 prefixEnd_7248637 := by exact prefixLift 7248637
  have htrace : WordTrace (prefixWord ++ tailWord_7248637) baseStart_7248637 baseEnd_7248637 := by
    simpa [prefixWord, tailWord_7248637, baseEnd_7248637] using wordTrace_append hprefix tailTrace_7248637
  have hstable : (prefixWord ++ tailWord_7248637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248637).length < 2 ^ (prefixWord ++ tailWord_7248637).sum := by decide
  have hdescent : baseEnd_7248637 < baseStart_7248637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248648 : List Nat := [2, 1, 3, 2, 2, 4, 1, 3, 1, 4]
def baseStart_7248648 : Nat := 118140960795 + 7248648 * 2 ^ 59
def prefixEnd_7248648 : Nat := 4983230072969 + 3 ^ 40 * 7248648 * 2
def baseEnd_7248648 : Nat := 1240680173083953621688027

theorem tailTrace_7248648 : CollatzResearch.WordTrace tailWord_7248648 prefixEnd_7248648 1240680173083953621688027 := by
  unfold tailWord_7248648
  simp only [CollatzResearch.WordTrace]
  refine ⟨132189956121696870681821299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176253274828929160909095065 132189956121696870681821299)
  ·
    refine ⟨198284934182545306022731949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132189956121696870681821299 198284934182545306022731949)
    ·
      refine ⟨74356850318454489758524481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198284934182545306022731949 74356850318454489758524481)
      ·
        refine ⟨55767637738840867318893361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74356850318454489758524481 55767637738840867318893361)
        ·
          refine ⟨41825728304130650489170021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55767637738840867318893361 41825728304130650489170021)
          ·
            refine ⟨7842324057024496966719379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41825728304130650489170021 7842324057024496966719379)
            ·
              refine ⟨11763486085536745450079069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7842324057024496966719379 11763486085536745450079069)
              ·
                refine ⟨4411307282076279543779651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11763486085536745450079069 4411307282076279543779651)
                ·
                  refine ⟨6616960923114419315669477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411307282076279543779651 6616960923114419315669477)
                  ·
                    refine ⟨1240680173083953621688027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6616960923114419315669477 1240680173083953621688027)
                    ·
                      rfl

theorem cell23_7248648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_7248648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248648 prefixEnd_7248648 := by exact prefixLift 7248648
  have htrace : WordTrace (prefixWord ++ tailWord_7248648) baseStart_7248648 baseEnd_7248648 := by
    simpa [prefixWord, tailWord_7248648, baseEnd_7248648] using wordTrace_append hprefix tailTrace_7248648
  have hstable : (prefixWord ++ tailWord_7248648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248648).length < 2 ^ (prefixWord ++ tailWord_7248648).sum := by decide
  have hdescent : baseEnd_7248648 < baseStart_7248648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248658 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_7248658 : Nat := 118140960795 + 7248658 * 2 ^ 59
def prefixEnd_7248658 : Nat := 4983230072969 + 3 ^ 40 * 7248658 * 2
def baseEnd_7248658 : Nat := 3722045654058405825939035

theorem tailTrace_7248658 : CollatzResearch.WordTrace tailWord_7248658 prefixEnd_7248658 3722045654058405825939035 := by
  unfold tailWord_7248658
  simp only [CollatzResearch.WordTrace]
  refine ⟨66095069243339378267876657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176253517982238342047671085 66095069243339378267876657)
  ·
    refine ⟨49571301932504533700907493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66095069243339378267876657 49571301932504533700907493)
    ·
      refine ⟨9294619112344600068920155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49571301932504533700907493 9294619112344600068920155)
      ·
        refine ⟨13941928668516900103380233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9294619112344600068920155 13941928668516900103380233)
        ·
          refine ⟨10456446501387675077535175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13941928668516900103380233 10456446501387675077535175)
          ·
            refine ⟨15684669752081512616302763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10456446501387675077535175 15684669752081512616302763)
            ·
              refine ⟨23527004628122268924454145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15684669752081512616302763 23527004628122268924454145)
              ·
                refine ⟨17645253471091701693340609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23527004628122268924454145 17645253471091701693340609)
                ·
                  refine ⟨13233940103318776270005457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17645253471091701693340609 13233940103318776270005457)
                  ·
                    refine ⟨9925455077489082202504093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13233940103318776270005457 9925455077489082202504093)
                    ·
                      refine ⟨3722045654058405825939035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9925455077489082202504093 3722045654058405825939035)
                      ·
                        rfl

theorem cell23_7248658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_7248658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248658 prefixEnd_7248658 := by exact prefixLift 7248658
  have htrace : WordTrace (prefixWord ++ tailWord_7248658) baseStart_7248658 baseEnd_7248658 := by
    simpa [prefixWord, tailWord_7248658, baseEnd_7248658] using wordTrace_append hprefix tailTrace_7248658
  have hstable : (prefixWord ++ tailWord_7248658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248658).length < 2 ^ (prefixWord ++ tailWord_7248658).sum := by decide
  have hdescent : baseEnd_7248658 < baseStart_7248658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248671 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 3, 1, 3]
def baseStart_7248671 : Nat := 118140960795 + 7248671 * 2 ^ 59
def prefixEnd_7248671 : Nat := 4983230072969 + 3 ^ 40 * 7248671 * 2
def baseEnd_7248671 : Nat := 3722052329306914275076475

theorem tailTrace_7248671 : CollatzResearch.WordTrace tailWord_7248671 prefixEnd_7248671 3722052329306914275076475 := by
  unfold tailWord_7248671
  simp only [CollatzResearch.WordTrace]
  refine ⟨264380751122310416291729867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176253834081540277527819911 264380751122310416291729867)
  ·
    refine ⟨396571126683465624437594801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264380751122310416291729867 396571126683465624437594801)
    ·
      refine ⟨297428345012599218328196101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396571126683465624437594801 297428345012599218328196101)
      ·
        refine ⟨55767814689862353436536769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297428345012599218328196101 55767814689862353436536769)
        ·
          refine ⟨41825861017396765077402577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55767814689862353436536769 41825861017396765077402577)
          ·
            refine ⟨31369395763047573808051933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41825861017396765077402577 31369395763047573808051933)
            ·
              refine ⟨11763523411142840178019475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31369395763047573808051933 11763523411142840178019475)
              ·
                refine ⟨17645285116714260267029213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11763523411142840178019475 17645285116714260267029213)
                ·
                  refine ⟨6616981918767847600135955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17645285116714260267029213 6616981918767847600135955)
                  ·
                    refine ⟨9925472878151771400203933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6616981918767847600135955 9925472878151771400203933)
                    ·
                      refine ⟨3722052329306914275076475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9925472878151771400203933 3722052329306914275076475)
                      ·
                        rfl

theorem cell23_7248671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_7248671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248671 prefixEnd_7248671 := by exact prefixLift 7248671
  have htrace : WordTrace (prefixWord ++ tailWord_7248671) baseStart_7248671 baseEnd_7248671 := by
    simpa [prefixWord, tailWord_7248671, baseEnd_7248671] using wordTrace_append hprefix tailTrace_7248671
  have hstable : (prefixWord ++ tailWord_7248671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248671).length < 2 ^ (prefixWord ++ tailWord_7248671).sum := by decide
  have hdescent : baseEnd_7248671 < baseStart_7248671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248691 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 1, 5]
def baseStart_7248691 : Nat := 118140960795 + 7248691 * 2 ^ 59
def prefixEnd_7248691 : Nat := 4983230072969 + 3 ^ 40 * 7248691 * 2
def baseEnd_7248691 : Nat := 1240687532973334732275461

theorem tailTrace_7248691 : CollatzResearch.WordTrace tailWord_7248691 prefixEnd_7248691 1240687532973334732275461 := by
  unfold tailWord_7248691
  simp only [CollatzResearch.WordTrace]
  refine ⟨264381480582237959707457927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176254320388158639804971951 264381480582237959707457927)
  ·
    refine ⟨396572220873356939561186891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264381480582237959707457927 396572220873356939561186891)
    ·
      refine ⟨594858331310035409341780337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396572220873356939561186891 594858331310035409341780337)
      ·
        refine ⟨446143748482526557006335253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594858331310035409341780337 446143748482526557006335253)
        ·
          refine ⟨20912988210118432359671965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 446143748482526557006335253 20912988210118432359671965)
          ·
            refine ⟨7842370578794412134876987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20912988210118432359671965 7842370578794412134876987)
            ·
              refine ⟨11763555868191618202315481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7842370578794412134876987 11763555868191618202315481)
              ·
                refine ⟨8822666901143713651736611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11763555868191618202315481 8822666901143713651736611)
                ·
                  refine ⟨13234000351715570477604917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8822666901143713651736611 13234000351715570477604917)
                  ·
                    refine ⟨1240687532973334732275461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13234000351715570477604917 1240687532973334732275461)
                    ·
                      rfl

theorem cell23_7248691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 5].length) (baseStart_7248691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248691 prefixEnd_7248691 := by exact prefixLift 7248691
  have htrace : WordTrace (prefixWord ++ tailWord_7248691) baseStart_7248691 baseEnd_7248691 := by
    simpa [prefixWord, tailWord_7248691, baseEnd_7248691] using wordTrace_append hprefix tailTrace_7248691
  have hstable : (prefixWord ++ tailWord_7248691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248691).length < 2 ^ (prefixWord ++ tailWord_7248691).sum := by decide
  have hdescent : baseEnd_7248691 < baseStart_7248691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248698 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2]
def baseStart_7248698 : Nat := 118140960795 + 7248698 * 2 ^ 59
def prefixEnd_7248698 : Nat := 4983230072969 + 3 ^ 40 * 7248698 * 2
def baseEnd_7248698 : Nat := 3722066193284585669438851

theorem tailTrace_7248698 : CollatzResearch.WordTrace tailWord_7248698 prefixEnd_7248698 3722066193284585669438851 := by
  unfold tailWord_7248698
  simp only [CollatzResearch.WordTrace]
  refine ⟨66095433973303149975740687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176254490595475066601975165 66095433973303149975740687)
  ·
    refine ⟨99143150959954724963611031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66095433973303149975740687 99143150959954724963611031)
    ·
      refine ⟨148714726439932087445416547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99143150959954724963611031 148714726439932087445416547)
      ·
        refine ⟨223072089659898131168124821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148714726439932087445416547 223072089659898131168124821)
        ·
          refine ⟨10456504202807724898505851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 223072089659898131168124821 10456504202807724898505851)
          ·
            refine ⟨15684756304211587347758777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10456504202807724898505851 15684756304211587347758777)
            ·
              refine ⟨11763567228158690510819083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15684756304211587347758777 11763567228158690510819083)
              ·
                refine ⟨17645350842238035766228625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11763567228158690510819083 17645350842238035766228625)
                ·
                  refine ⟨13234013131678526824671469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17645350842238035766228625 13234013131678526824671469)
                  ·
                    refine ⟨4962754924379447559251801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13234013131678526824671469 4962754924379447559251801)
                    ·
                      refine ⟨3722066193284585669438851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962754924379447559251801 3722066193284585669438851)
                      ·
                        rfl

theorem cell23_7248698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2].length) (baseStart_7248698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248698 prefixEnd_7248698 := by exact prefixLift 7248698
  have htrace : WordTrace (prefixWord ++ tailWord_7248698) baseStart_7248698 baseEnd_7248698 := by
    simpa [prefixWord, tailWord_7248698, baseEnd_7248698] using wordTrace_append hprefix tailTrace_7248698
  have hstable : (prefixWord ++ tailWord_7248698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248698).length < 2 ^ (prefixWord ++ tailWord_7248698).sum := by decide
  have hdescent : baseEnd_7248698 < baseStart_7248698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248778 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_7248778 : Nat := 118140960795 + 7248778 * 2 ^ 59
def prefixEnd_7248778 : Nat := 4983230072969 + 3 ^ 40 * 7248778 * 2
def baseEnd_7248778 : Nat := 3722107271736945356438483

theorem tailTrace_7248778 : CollatzResearch.WordTrace tailWord_7248778 prefixEnd_7248778 3722107271736945356438483 := by
  unfold tailWord_7248778
  simp only [CollatzResearch.WordTrace]
  refine ⟨66096163433230693391468747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176256435821948515710583325 66096163433230693391468747)
  ·
    refine ⟨99144245149846040087203121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66096163433230693391468747 99144245149846040087203121)
    ·
      refine ⟨74358183862384530065402341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99144245149846040087203121 74358183862384530065402341)
      ·
        refine ⟨13942159474197099387262939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74358183862384530065402341 13942159474197099387262939)
        ·
          refine ⟨20913239211295649080894409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13942159474197099387262939 20913239211295649080894409)
          ·
            refine ⟨15684929408471736810670807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20913239211295649080894409 15684929408471736810670807)
            ·
              refine ⟨23527394112707605216006211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15684929408471736810670807 23527394112707605216006211)
              ·
                refine ⟨35291091169061407824009317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23527394112707605216006211 35291091169061407824009317)
                ·
                  refine ⟨6617079594199013967001747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35291091169061407824009317 6617079594199013967001747)
                  ·
                    refine ⟨9925619391298520950502621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6617079594199013967001747 9925619391298520950502621)
                    ·
                      refine ⟨3722107271736945356438483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9925619391298520950502621 3722107271736945356438483)
                      ·
                        rfl

theorem cell23_7248778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_7248778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248778 prefixEnd_7248778 := by exact prefixLift 7248778
  have htrace : WordTrace (prefixWord ++ tailWord_7248778) baseStart_7248778 baseEnd_7248778 := by
    simpa [prefixWord, tailWord_7248778, baseEnd_7248778] using wordTrace_append hprefix tailTrace_7248778
  have hstable : (prefixWord ++ tailWord_7248778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248778).length < 2 ^ (prefixWord ++ tailWord_7248778).sum := by decide
  have hdescent : baseEnd_7248778 < baseStart_7248778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248787 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 5]
def baseStart_7248787 : Nat := 118140960795 + 7248787 * 2 ^ 59
def prefixEnd_7248787 : Nat := 4983230072969 + 3 ^ 40 * 7248787 * 2
def baseEnd_7248787 : Nat := 3722111893062835821225941

theorem tailTrace_7248787 : CollatzResearch.WordTrace tailWord_7248787 prefixEnd_7248787 3722111893062835821225941 := by
  unfold tailWord_7248787
  simp only [CollatzResearch.WordTrace]
  refine ⟨264384981989890168102952615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176256654659926778735301743 264384981989890168102952615)
  ·
    refine ⟨396577472984835252154428923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264384981989890168102952615 396577472984835252154428923)
    ·
      refine ⟨594866209477252878231643385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396577472984835252154428923 594866209477252878231643385)
      ·
        refine ⟨446149657107939658673732539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594866209477252878231643385 446149657107939658673732539)
        ·
          refine ⟨669224485661909488010598809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446149657107939658673732539 669224485661909488010598809)
          ·
            refine ⟨501918364246432116007949107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669224485661909488010598809 501918364246432116007949107)
            ·
              refine ⟨752877546369648174011923661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501918364246432116007949107 752877546369648174011923661)
              ·
                refine ⟨282329079888618065254471373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 752877546369648174011923661 282329079888618065254471373)
                ·
                  refine ⟨105873404958231774470426765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282329079888618065254471373 105873404958231774470426765)
                  ·
                    refine ⟨39702526859336915426410037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105873404958231774470426765 39702526859336915426410037)
                    ·
                      refine ⟨3722111893062835821225941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39702526859336915426410037 3722111893062835821225941)
                      ·
                        rfl

theorem cell23_7248787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_7248787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248787 prefixEnd_7248787 := by exact prefixLift 7248787
  have htrace : WordTrace (prefixWord ++ tailWord_7248787) baseStart_7248787 baseEnd_7248787 := by
    simpa [prefixWord, tailWord_7248787, baseEnd_7248787] using wordTrace_append hprefix tailTrace_7248787
  have hstable : (prefixWord ++ tailWord_7248787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248787).length < 2 ^ (prefixWord ++ tailWord_7248787).sum := by decide
  have hdescent : baseEnd_7248787 < baseStart_7248787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248804 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_7248804 : Nat := 118140960795 + 7248804 * 2 ^ 59
def prefixEnd_7248804 : Nat := 4983230072969 + 3 ^ 40 * 7248804 * 2
def baseEnd_7248804 : Nat := 3722120622233962254713363

theorem tailTrace_7248804 : CollatzResearch.WordTrace tailWord_7248804 prefixEnd_7248804 3722120622233962254713363 := by
  unfold tailWord_7248804
  simp only [CollatzResearch.WordTrace]
  refine ⟨132192801015414290003160733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176257068020552386670880977 132192801015414290003160733)
  ·
    refine ⟨49572300380780358751185275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132192801015414290003160733 49572300380780358751185275)
    ·
      refine ⟨74358450571170538126777913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49572300380780358751185275 74358450571170538126777913)
      ·
        refine ⟨55768837928377903595083435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74358450571170538126777913 55768837928377903595083435)
        ·
          refine ⟨83653256892566855392625153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55768837928377903595083435 83653256892566855392625153)
          ·
            refine ⟨62739942669425141544468865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83653256892566855392625153 62739942669425141544468865)
            ·
              refine ⟨47054957002068856158351649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62739942669425141544468865 47054957002068856158351649)
              ·
                refine ⟨35291217751551642118763737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47054957002068856158351649 35291217751551642118763737)
                ·
                  refine ⟨26468413313663731589072803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35291217751551642118763737 26468413313663731589072803)
                  ·
                    refine ⟨39702619970495597383609205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26468413313663731589072803 39702619970495597383609205)
                    ·
                      refine ⟨3722120622233962254713363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39702619970495597383609205 3722120622233962254713363)
                      ·
                        rfl

theorem cell23_7248804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_7248804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248804 prefixEnd_7248804 := by exact prefixLift 7248804
  have htrace : WordTrace (prefixWord ++ tailWord_7248804) baseStart_7248804 baseEnd_7248804 := by
    simpa [prefixWord, tailWord_7248804, baseEnd_7248804] using wordTrace_append hprefix tailTrace_7248804
  have hstable : (prefixWord ++ tailWord_7248804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248804).length < 2 ^ (prefixWord ++ tailWord_7248804).sum := by decide
  have hdescent : baseEnd_7248804 < baseStart_7248804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248827 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 8]
def baseStart_7248827 : Nat := 118140960795 + 7248827 * 2 ^ 59
def prefixEnd_7248827 : Nat := 4983230072969 + 3 ^ 40 * 7248827 * 2
def baseEnd_7248827 : Nat := 3722132432289015664725757

theorem tailTrace_7248827 : CollatzResearch.WordTrace tailWord_7248827 prefixEnd_7248827 3722132432289015664725757 := by
  unfold tailWord_7248827
  simp only [CollatzResearch.WordTrace]
  refine ⟨264386440909745254934408735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176257627273163503289605823 264386440909745254934408735)
  ·
    refine ⟨396579661364617882401613103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264386440909745254934408735 396579661364617882401613103)
    ·
      refine ⟨594869492046926823602419655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396579661364617882401613103 594869492046926823602419655)
      ·
        refine ⟨892304238070390235403629483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594869492046926823602419655 892304238070390235403629483)
        ·
          refine ⟨1338456357105585353105444225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892304238070390235403629483 1338456357105585353105444225)
          ·
            refine ⟨1003842267829189014829083169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338456357105585353105444225 1003842267829189014829083169)
            ·
              refine ⟨752881700871891761121812377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1003842267829189014829083169 752881700871891761121812377)
              ·
                refine ⟨564661275653918820841359283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752881700871891761121812377 564661275653918820841359283)
                ·
                  refine ⟨846991913480878231262038925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564661275653918820841359283 846991913480878231262038925)
                  ·
                    refine ⟨317621967555329336723264597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846991913480878231262038925 317621967555329336723264597)
                    ·
                      refine ⟨3722132432289015664725757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 317621967555329336723264597 3722132432289015664725757)
                      ·
                        rfl

theorem cell23_7248827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_7248827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248827 prefixEnd_7248827 := by exact prefixLift 7248827
  have htrace : WordTrace (prefixWord ++ tailWord_7248827) baseStart_7248827 baseEnd_7248827 := by
    simpa [prefixWord, tailWord_7248827, baseEnd_7248827] using wordTrace_append hprefix tailTrace_7248827
  have hstable : (prefixWord ++ tailWord_7248827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248827).length < 2 ^ (prefixWord ++ tailWord_7248827).sum := by decide
  have hdescent : baseEnd_7248827 < baseStart_7248827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248852 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_7248852 : Nat := 118140960795 + 7248852 * 2 ^ 59
def prefixEnd_7248852 : Nat := 4983230072969 + 3 ^ 40 * 7248852 * 2
def baseEnd_7248852 : Nat := 3722145269305378066913143

theorem tailTrace_7248852 : CollatzResearch.WordTrace tailWord_7248852 prefixEnd_7248852 3722145269305378066913143 := by
  unfold tailWord_7248852
  simp only [CollatzResearch.WordTrace]
  refine ⟨132193676367327342102034405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176258235156436456136045873 132193676367327342102034405)
  ·
    refine ⟨24786314318873876644131451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132193676367327342102034405 24786314318873876644131451)
    ·
      refine ⟨37179471478310814966197177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24786314318873876644131451 37179471478310814966197177)
      ·
        refine ⟨27884603608733111224647883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37179471478310814966197177 27884603608733111224647883)
        ·
          refine ⟨41826905413099666836971825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27884603608733111224647883 41826905413099666836971825)
          ·
            refine ⟨31370179059824750127728869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41826905413099666836971825 31370179059824750127728869)
            ·
              refine ⟨5881908573717140648949163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31370179059824750127728869 5881908573717140648949163)
              ·
                refine ⟨8822862860575710973423745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5881908573717140648949163 8822862860575710973423745)
                ·
                  refine ⟨6617147145431783230067809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8822862860575710973423745 6617147145431783230067809)
                  ·
                    refine ⟨4962860359073837422550857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6617147145431783230067809 4962860359073837422550857)
                    ·
                      refine ⟨3722145269305378066913143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962860359073837422550857 3722145269305378066913143)
                      ·
                        rfl

theorem cell23_7248852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_7248852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248852 prefixEnd_7248852 := by exact prefixLift 7248852
  have htrace : WordTrace (prefixWord ++ tailWord_7248852) baseStart_7248852 baseEnd_7248852 := by
    simpa [prefixWord, tailWord_7248852, baseEnd_7248852] using wordTrace_append hprefix tailTrace_7248852
  have hstable : (prefixWord ++ tailWord_7248852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248852).length < 2 ^ (prefixWord ++ tailWord_7248852).sum := by decide
  have hdescent : baseEnd_7248852 < baseStart_7248852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248871 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 2, 5]
def baseStart_7248871 : Nat := 118140960795 + 7248871 * 2 ^ 59
def prefixEnd_7248871 : Nat := 4983230072969 + 3 ^ 40 * 7248871 * 2
def baseEnd_7248871 : Nat := 1240718341812604497525185

theorem tailTrace_7248871 : CollatzResearch.WordTrace tailWord_7248871 prefixEnd_7248871 1240718341812604497525185 := by
  unfold tailWord_7248871
  simp only [CollatzResearch.WordTrace]
  refine ⟨264388045721585850449010467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176258697147723900299340311 264388045721585850449010467)
  ·
    refine ⟨396582068582378775673515701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264388045721585850449010467 396582068582378775673515701)
    ·
      refine ⟨37179568929598010219392097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 396582068582378775673515701 37179568929598010219392097)
      ·
        refine ⟨27884676697198507664544073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37179568929598010219392097 27884676697198507664544073)
        ·
          refine ⟨20913507522898880748408055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27884676697198507664544073 20913507522898880748408055)
          ·
            refine ⟨31370261284348321122612083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20913507522898880748408055 31370261284348321122612083)
            ·
              refine ⟨47055391926522481683918125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31370261284348321122612083 47055391926522481683918125)
              ·
                refine ⟨17645771972445930631469297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47055391926522481683918125 17645771972445930631469297)
                ·
                  refine ⟨13234328979334447973601973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17645771972445930631469297 13234328979334447973601973)
                  ·
                    refine ⟨1240718341812604497525185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13234328979334447973601973 1240718341812604497525185)
                    ·
                      rfl

theorem cell23_7248871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_7248871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248871 prefixEnd_7248871 := by exact prefixLift 7248871
  have htrace : WordTrace (prefixWord ++ tailWord_7248871) baseStart_7248871 baseEnd_7248871 := by
    simpa [prefixWord, tailWord_7248871, baseEnd_7248871] using wordTrace_append hprefix tailTrace_7248871
  have hstable : (prefixWord ++ tailWord_7248871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248871).length < 2 ^ (prefixWord ++ tailWord_7248871).sum := by decide
  have hdescent : baseEnd_7248871 < baseStart_7248871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248891 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 2, 4, 2]
def baseStart_7248891 : Nat := 118140960795 + 7248891 * 2 ^ 59
def prefixEnd_7248891 : Nat := 4983230072969 + 3 ^ 40 * 7248891 * 2
def baseEnd_7248891 : Nat := 3722165295050903414325463

theorem tailTrace_7248891 : CollatzResearch.WordTrace tailWord_7248891 prefixEnd_7248891 3722165295050903414325463 := by
  unfold tailWord_7248891
  simp only [CollatzResearch.WordTrace]
  refine ⟨264388775181513393864738527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176259183454342262576492351 264388775181513393864738527)
  ·
    refine ⟨396583162772270090797107791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264388775181513393864738527 396583162772270090797107791)
    ·
      refine ⟨594874744158405136195661687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396583162772270090797107791 594874744158405136195661687)
      ·
        refine ⟨892312116237607704293492531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594874744158405136195661687 892312116237607704293492531)
        ·
          refine ⟨1338468174356411556440238797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892312116237607704293492531 1338468174356411556440238797)
          ·
            refine ⟨501925565383654333665089549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1338468174356411556440238797 501925565383654333665089549)
            ·
              refine ⟨188222087018870375124408581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501925565383654333665089549 188222087018870375124408581)
              ·
                refine ⟨35291641316038195335826609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188222087018870375124408581 35291641316038195335826609)
                ·
                  refine ⟨26468730987028646501869957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35291641316038195335826609 26468730987028646501869957)
                  ·
                    refine ⟨4962887060067871219100617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26468730987028646501869957 4962887060067871219100617)
                    ·
                      refine ⟨3722165295050903414325463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962887060067871219100617 3722165295050903414325463)
                      ·
                        rfl

theorem cell23_7248891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 4, 2].length) (baseStart_7248891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248891 prefixEnd_7248891 := by exact prefixLift 7248891
  have htrace : WordTrace (prefixWord ++ tailWord_7248891) baseStart_7248891 baseEnd_7248891 := by
    simpa [prefixWord, tailWord_7248891, baseEnd_7248891] using wordTrace_append hprefix tailTrace_7248891
  have hstable : (prefixWord ++ tailWord_7248891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248891).length < 2 ^ (prefixWord ++ tailWord_7248891).sum := by decide
  have hdescent : baseEnd_7248891 < baseStart_7248891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248901 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 3, 4]
def baseStart_7248901 : Nat := 118140960795 + 7248901 * 2 ^ 59
def prefixEnd_7248901 : Nat := 4983230072969 + 3 ^ 40 * 7248901 * 2
def baseEnd_7248901 : Nat := 1240723476619149458400139

theorem tailTrace_7248901 : CollatzResearch.WordTrace tailWord_7248901 prefixEnd_7248901 1240723476619149458400139 := by
  unfold tailWord_7248901
  simp only [CollatzResearch.WordTrace]
  refine ⟨264389139911477165572602557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176259426607651443715068371 264389139911477165572602557)
  ·
    refine ⟨99145927466803937089725959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264389139911477165572602557 99145927466803937089725959)
    ·
      refine ⟨148718891200205905634588939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99145927466803937089725959 148718891200205905634588939)
      ·
        refine ⟨223078336800308858451883409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148718891200205905634588939 223078336800308858451883409)
        ·
          refine ⟨167308752600231643838912557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223078336800308858451883409 167308752600231643838912557)
          ·
            refine ⟨62740782225086866439592209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167308752600231643838912557 62740782225086866439592209)
            ·
              refine ⟨47055586668815149829694157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62740782225086866439592209 47055586668815149829694157)
              ·
                refine ⟨17645845000805681186135309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47055586668815149829694157 17645845000805681186135309)
                ·
                  refine ⟨6617191875302130444800741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17645845000805681186135309 6617191875302130444800741)
                  ·
                    refine ⟨1240723476619149458400139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617191875302130444800741 1240723476619149458400139)
                    ·
                      rfl

theorem cell23_7248901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_7248901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248901 prefixEnd_7248901 := by exact prefixLift 7248901
  have htrace : WordTrace (prefixWord ++ tailWord_7248901) baseStart_7248901 baseEnd_7248901 := by
    simpa [prefixWord, tailWord_7248901, baseEnd_7248901] using wordTrace_append hprefix tailTrace_7248901
  have hstable : (prefixWord ++ tailWord_7248901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248901).length < 2 ^ (prefixWord ++ tailWord_7248901).sum := by decide
  have hdescent : baseEnd_7248901 < baseStart_7248901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248908 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 2, 4, 2]
def baseStart_7248908 : Nat := 118140960795 + 7248908 * 2 ^ 59
def prefixEnd_7248908 : Nat := 4983230072969 + 3 ^ 40 * 7248908 * 2
def baseEnd_7248908 : Nat := 3722174024222029847812885

theorem tailTrace_7248908 : CollatzResearch.WordTrace tailWord_7248908 prefixEnd_7248908 3722174024222029847812885 := by
  unfold tailWord_7248908
  simp only [CollatzResearch.WordTrace]
  refine ⟨132194697611225902884053689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176259596814967870512071585 132194697611225902884053689)
  ·
    refine ⟨99146023208419427163040267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132194697611225902884053689 99146023208419427163040267)
    ·
      refine ⟨148719034812629140744560401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99146023208419427163040267 148719034812629140744560401)
      ·
        refine ⟨111539276109471855558420301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148719034812629140744560401 111539276109471855558420301)
        ·
          refine ⟨41827228541051945834407613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111539276109471855558420301 41827228541051945834407613)
          ·
            refine ⟨15685210702894479687902855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41827228541051945834407613 15685210702894479687902855)
            ·
              refine ⟨23527816054341719531854283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15685210702894479687902855 23527816054341719531854283)
              ·
                refine ⟨35291724081512579297781425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23527816054341719531854283 35291724081512579297781425)
                ·
                  refine ⟨26468793061134434473336069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35291724081512579297781425 26468793061134434473336069)
                  ·
                    refine ⟨4962898698962706463750513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26468793061134434473336069 4962898698962706463750513)
                    ·
                      refine ⟨3722174024222029847812885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4962898698962706463750513 3722174024222029847812885)
                      ·
                        rfl

theorem cell23_7248908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_7248908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248908 prefixEnd_7248908 := by exact prefixLift 7248908
  have htrace : WordTrace (prefixWord ++ tailWord_7248908) baseStart_7248908 baseEnd_7248908 := by
    simpa [prefixWord, tailWord_7248908, baseEnd_7248908] using wordTrace_append hprefix tailTrace_7248908
  have hstable : (prefixWord ++ tailWord_7248908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248908).length < 2 ^ (prefixWord ++ tailWord_7248908).sum := by decide
  have hdescent : baseEnd_7248908 < baseStart_7248908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248925 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_7248925 : Nat := 118140960795 + 7248925 * 2 ^ 59
def prefixEnd_7248925 : Nat := 4983230072969 + 3 ^ 40 * 7248925 * 2
def baseEnd_7248925 : Nat := 3722182753393156281300307

theorem tailTrace_7248925 : CollatzResearch.WordTrace tailWord_7248925 prefixEnd_7248925 3722182753393156281300307 := by
  unfold tailWord_7248925
  simp only [CollatzResearch.WordTrace]
  refine ⟨264390015263390217671476229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176260010175593478447650819 264390015263390217671476229)
  ·
    refine ⟨49573127861885665813401793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264390015263390217671476229 49573127861885665813401793)
    ·
      refine ⟨37179845896414249360051345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49573127861885665813401793 37179845896414249360051345)
      ·
        refine ⟨27884884422310687020038509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37179845896414249360051345 27884884422310687020038509)
        ·
          refine ⟨10456831658366507632514441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27884884422310687020038509 10456831658366507632514441)
          ·
            refine ⟨7842623743774880724385831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10456831658366507632514441 7842623743774880724385831)
            ·
              refine ⟨11763935615662321086578747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7842623743774880724385831 11763935615662321086578747)
              ·
                refine ⟨17645903423493481629868121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11763935615662321086578747 17645903423493481629868121)
                ·
                  refine ⟨13234427567620111222401091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17645903423493481629868121 13234427567620111222401091)
                  ·
                    refine ⟨19851641351430166833601637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13234427567620111222401091 19851641351430166833601637)
                    ·
                      refine ⟨3722182753393156281300307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19851641351430166833601637 3722182753393156281300307)
                      ·
                        rfl

theorem cell23_7248925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_7248925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248925 prefixEnd_7248925 := by exact prefixLift 7248925
  have htrace : WordTrace (prefixWord ++ tailWord_7248925) baseStart_7248925 baseEnd_7248925 := by
    simpa [prefixWord, tailWord_7248925, baseEnd_7248925] using wordTrace_append hprefix tailTrace_7248925
  have hstable : (prefixWord ++ tailWord_7248925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248925).length < 2 ^ (prefixWord ++ tailWord_7248925).sum := by decide
  have hdescent : baseEnd_7248925 < baseStart_7248925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248948 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 8]
def baseStart_7248948 : Nat := 118140960795 + 7248948 * 2 ^ 59
def prefixEnd_7248948 : Nat := 4983230072969 + 3 ^ 40 * 7248948 * 2
def baseEnd_7248948 : Nat := 413577173716467743479189

theorem tailTrace_7248948 : CollatzResearch.WordTrace tailWord_7248948 prefixEnd_7248948 413577173716467743479189 := by
  unfold tailWord_7248948
  simp only [CollatzResearch.WordTrace]
  refine ⟨132195427071153446299781749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176260569428204595066375665 132195427071153446299781749)
  ·
    refine ⟨12393321287920635590604539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132195427071153446299781749 12393321287920635590604539)
    ·
      refine ⟨18589981931880953385906809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12393321287920635590604539 18589981931880953385906809)
      ·
        refine ⟨13942486448910715039430107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18589981931880953385906809 13942486448910715039430107)
        ·
          refine ⟨20913729673366072559145161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13942486448910715039430107 20913729673366072559145161)
          ·
            refine ⟨15685297255024554419358871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20913729673366072559145161 15685297255024554419358871)
            ·
              refine ⟨23527945882536831629038307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15685297255024554419358871 23527945882536831629038307)
              ·
                refine ⟨35291918823805247443557461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23527945882536831629038307 35291918823805247443557461)
                ·
                  refine ⟨413577173716467743479189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35291918823805247443557461 413577173716467743479189)
                  ·
                    rfl

theorem cell23_7248948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_7248948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248948 prefixEnd_7248948 := by exact prefixLift 7248948
  have htrace : WordTrace (prefixWord ++ tailWord_7248948) baseStart_7248948 baseEnd_7248948 := by
    simpa [prefixWord, tailWord_7248948, baseEnd_7248948] using wordTrace_append hprefix tailTrace_7248948
  have hstable : (prefixWord ++ tailWord_7248948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248948).length < 2 ^ (prefixWord ++ tailWord_7248948).sum := by decide
  have hdescent : baseEnd_7248948 < baseStart_7248948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248978 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_7248978 : Nat := 118140960795 + 7248978 * 2 ^ 59
def prefixEnd_7248978 : Nat := 4983230072969 + 3 ^ 40 * 7248978 * 2
def baseEnd_7248978 : Nat := 1240736655955948191312521

theorem tailTrace_7248978 : CollatzResearch.WordTrace tailWord_7248978 prefixEnd_7248978 1240736655955948191312521 := by
  unfold tailWord_7248978
  simp only [CollatzResearch.WordTrace]
  refine ⟨66097987083049551930788897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176261298888132138482103725 66097987083049551930788897)
  ·
    refine ⟨49573490312287163948091673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66097987083049551930788897 49573490312287163948091673)
    ·
      refine ⟨37180117734215372961068755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49573490312287163948091673 37180117734215372961068755)
      ·
        refine ⟨55770176601323059441603133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37180117734215372961068755 55770176601323059441603133)
        ·
          refine ⟨20913816225496147290601175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55770176601323059441603133 20913816225496147290601175)
          ·
            refine ⟨31370724338244220935901763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20913816225496147290601175 31370724338244220935901763)
            ·
              refine ⟨47056086507366331403852645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31370724338244220935901763 47056086507366331403852645)
              ·
                refine ⟨8823016220131187138222371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47056086507366331403852645 8823016220131187138222371)
                ·
                  refine ⟨13234524330196780707333557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8823016220131187138222371 13234524330196780707333557)
                  ·
                    refine ⟨1240736655955948191312521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13234524330196780707333557 1240736655955948191312521)
                    ·
                      rfl

theorem cell23_7248978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_7248978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248978 prefixEnd_7248978 := by exact prefixLift 7248978
  have htrace : WordTrace (prefixWord ++ tailWord_7248978) baseStart_7248978 baseEnd_7248978 := by
    simpa [prefixWord, tailWord_7248978, baseEnd_7248978] using wordTrace_append hprefix tailTrace_7248978
  have hstable : (prefixWord ++ tailWord_7248978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248978).length < 2 ^ (prefixWord ++ tailWord_7248978).sum := by decide
  have hdescent : baseEnd_7248978 < baseStart_7248978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7248991 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 6, 4]
def baseStart_7248991 : Nat := 118140960795 + 7248991 * 2 ^ 59
def prefixEnd_7248991 : Nat := 4983230072969 + 3 ^ 40 * 7248991 * 2
def baseEnd_7248991 : Nat := 1240738881038784341025001

theorem tailTrace_7248991 : CollatzResearch.WordTrace tailWord_7248991 prefixEnd_7248991 1240738881038784341025001 := by
  unfold tailWord_7248991
  simp only [CollatzResearch.WordTrace]
  refine ⟨264392422481151110943378827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176261614987434073962252551 264392422481151110943378827)
  ·
    refine ⟨396588633721726666415068241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264392422481151110943378827 396588633721726666415068241)
    ·
      refine ⟨297441475291294999811301181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396588633721726666415068241 297441475291294999811301181)
      ·
        refine ⟨111540553234235624929237943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297441475291294999811301181 111540553234235624929237943)
        ·
          refine ⟨167310829851353437393856915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111540553234235624929237943 167310829851353437393856915)
          ·
            refine ⟨250966244777030156090785373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167310829851353437393856915 250966244777030156090785373)
            ·
              refine ⟨94112341791386308534044515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250966244777030156090785373 94112341791386308534044515)
              ·
                refine ⟨141168512687079462801066773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94112341791386308534044515 141168512687079462801066773)
                ·
                  refine ⟨6617274032206849818800005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141168512687079462801066773 6617274032206849818800005)
                  ·
                    refine ⟨1240738881038784341025001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617274032206849818800005 1240738881038784341025001)
                    ·
                      rfl

theorem cell23_7248991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 4].length) (baseStart_7248991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7248991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7248991 prefixEnd_7248991 := by exact prefixLift 7248991
  have htrace : WordTrace (prefixWord ++ tailWord_7248991) baseStart_7248991 baseEnd_7248991 := by
    simpa [prefixWord, tailWord_7248991, baseEnd_7248991] using wordTrace_append hprefix tailTrace_7248991
  have hstable : (prefixWord ++ tailWord_7248991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7248991).length < 2 ^ (prefixWord ++ tailWord_7248991).sum := by decide
  have hdescent : baseEnd_7248991 < baseStart_7248991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7248991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249001 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 5]
def baseStart_7249001 : Nat := 118140960795 + 7249001 * 2 ^ 59
def prefixEnd_7249001 : Nat := 4983230072969 + 3 ^ 40 * 7249001 * 2
def baseEnd_7249001 : Nat := 3722221777922897983949957

theorem tailTrace_7249001 : CollatzResearch.WordTrace tailWord_7249001 prefixEnd_7249001 3722221777922897983949957 := by
  unfold tailWord_7249001
  simp only [CollatzResearch.WordTrace]
  refine ⟨264392787211114882651242857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176261858140743255100828571 264392787211114882651242857)
  ·
    refine ⟨198294590408336161988432143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264392787211114882651242857 198294590408336161988432143)
    ·
      refine ⟨297441885612504242982648215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198294590408336161988432143 297441885612504242982648215)
      ·
        refine ⟨446162828418756364473972323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297441885612504242982648215 446162828418756364473972323)
        ·
          refine ⟨669244242628134546710958485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446162828418756364473972323 669244242628134546710958485)
          ·
            refine ⟨31370823873193806877076179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 669244242628134546710958485 31370823873193806877076179)
            ·
              refine ⟨47056235809790710315614269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31370823873193806877076179 47056235809790710315614269)
              ·
                refine ⟨17646088428671516368355351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47056235809790710315614269 17646088428671516368355351)
                ·
                  refine ⟨26469132643007274552533027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17646088428671516368355351 26469132643007274552533027)
                  ·
                    refine ⟨39703698964510911828799541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26469132643007274552533027 39703698964510911828799541)
                    ·
                      refine ⟨3722221777922897983949957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39703698964510911828799541 3722221777922897983949957)
                      ·
                        rfl

theorem cell23_7249001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_7249001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249001 prefixEnd_7249001 := by exact prefixLift 7249001
  have htrace : WordTrace (prefixWord ++ tailWord_7249001) baseStart_7249001 baseEnd_7249001 := by
    simpa [prefixWord, tailWord_7249001, baseEnd_7249001] using wordTrace_append hprefix tailTrace_7249001
  have hstable : (prefixWord ++ tailWord_7249001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249001).length < 2 ^ (prefixWord ++ tailWord_7249001).sum := by decide
  have hdescent : baseEnd_7249001 < baseStart_7249001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249008 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 2, 4]
def baseStart_7249008 : Nat := 118140960795 + 7249008 * 2 ^ 59
def prefixEnd_7249008 : Nat := 4983230072969 + 3 ^ 40 * 7249008 * 2
def baseEnd_7249008 : Nat := 1240741790762493152187475

theorem tailTrace_7249008 : CollatzResearch.WordTrace tailWord_7249008 prefixEnd_7249008 1240741790762493152187475 := by
  unfold tailWord_7249008
  simp only [CollatzResearch.WordTrace]
  refine ⟨132196521261044761423373839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176262028348059681897831785 132196521261044761423373839)
  ·
    refine ⟨198294781891567142135060759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132196521261044761423373839 198294781891567142135060759)
    ·
      refine ⟨297442172837350713202591139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198294781891567142135060759 297442172837350713202591139)
      ·
        refine ⟨446163259256026069803886709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297442172837350713202591139 446163259256026069803886709)
        ·
          refine ⟨41827805555252444044114379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 446163259256026069803886709 41827805555252444044114379)
          ·
            refine ⟨62741708332878666066171569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41827805555252444044114379 62741708332878666066171569)
            ·
              refine ⟨47056281249658999549628677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62741708332878666066171569 47056281249658999549628677)
              ·
                refine ⟨8823052734311062415555377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47056281249658999549628677 8823052734311062415555377)
                ·
                  refine ⟨6617289550733296811666533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8823052734311062415555377 6617289550733296811666533)
                  ·
                    refine ⟨1240741790762493152187475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617289550733296811666533 1240741790762493152187475)
                    ·
                      rfl

theorem cell23_7249008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2, 4].length) (baseStart_7249008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249008 prefixEnd_7249008 := by exact prefixLift 7249008
  have htrace : WordTrace (prefixWord ++ tailWord_7249008) baseStart_7249008 baseEnd_7249008 := by
    simpa [prefixWord, tailWord_7249008, baseEnd_7249008] using wordTrace_append hprefix tailTrace_7249008
  have hstable : (prefixWord ++ tailWord_7249008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249008).length < 2 ^ (prefixWord ++ tailWord_7249008).sum := by decide
  have hdescent : baseEnd_7249008 < baseStart_7249008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249021 : List Nat := [1, 4, 1, 1, 3, 1, 4, 8]
def baseStart_7249021 : Nat := 118140960795 + 7249021 * 2 ^ 59
def prefixEnd_7249021 : Nat := 4983230072969 + 3 ^ 40 * 7249021 * 2
def baseEnd_7249021 : Nat := 137860446205036589099995

theorem tailTrace_7249021 : CollatzResearch.WordTrace tailWord_7249021 prefixEnd_7249021 137860446205036589099995 := by
  unfold tailWord_7249021
  simp only [CollatzResearch.WordTrace]
  refine ⟨264393516671042426066970917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176262344447361617377980611 264393516671042426066970917)
  ·
    refine ⟨49573784375820454887557047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264393516671042426066970917 49573784375820454887557047)
    ·
      refine ⟨74360676563730682331335571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49573784375820454887557047 74360676563730682331335571)
      ·
        refine ⟨111541014845596023497003357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74360676563730682331335571 111541014845596023497003357)
        ·
          refine ⟨41827880567098508811376259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111541014845596023497003357 41827880567098508811376259)
          ·
            refine ⟨62741820850647763217064389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41827880567098508811376259 62741820850647763217064389)
            ·
              refine ⟨11764091409496455603199573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62741820850647763217064389 11764091409496455603199573)
              ·
                refine ⟨137860446205036589099995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11764091409496455603199573 137860446205036589099995)
                ·
                  rfl

theorem cell23_7249021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 8].length) (baseStart_7249021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249021 prefixEnd_7249021 := by exact prefixLift 7249021
  have htrace : WordTrace (prefixWord ++ tailWord_7249021) baseStart_7249021 baseEnd_7249021 := by
    simpa [prefixWord, tailWord_7249021, baseEnd_7249021] using wordTrace_append hprefix tailTrace_7249021
  have hstable : (prefixWord ++ tailWord_7249021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249021).length < 2 ^ (prefixWord ++ tailWord_7249021).sum := by decide
  have hdescent : baseEnd_7249021 < baseStart_7249021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249025 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 2, 4]
def baseStart_7249025 : Nat := 118140960795 + 7249025 * 2 ^ 59
def prefixEnd_7249025 : Nat := 4983230072969 + 3 ^ 40 * 7249025 * 2
def baseEnd_7249025 : Nat := 1240744700486201963349949

theorem tailTrace_7249025 : CollatzResearch.WordTrace tailWord_7249025 prefixEnd_7249025 1240744700486201963349949 := by
  unfold tailWord_7249025
  simp only [CollatzResearch.WordTrace]
  refine ⟨264393662563027934750116529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176262441708685289833411019 264393662563027934750116529)
  ·
    refine ⟨198295246922270951062587397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264393662563027934750116529 198295246922270951062587397)
    ·
      refine ⟨37180358797925803324235137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198295246922270951062587397 37180358797925803324235137)
      ·
        refine ⟨27885269098444352493176353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37180358797925803324235137 27885269098444352493176353)
        ·
          refine ⟨20913951823833264369882265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27885269098444352493176353 20913951823833264369882265)
          ·
            refine ⟨15685463867874948277411699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20913951823833264369882265 15685463867874948277411699)
            ·
              refine ⟨23528195801812422416117549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15685463867874948277411699 23528195801812422416117549)
              ·
                refine ⟨8823073425679658406044081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23528195801812422416117549 8823073425679658406044081)
                ·
                  refine ⟨6617305069259743804533061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8823073425679658406044081 6617305069259743804533061)
                  ·
                    refine ⟨1240744700486201963349949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617305069259743804533061 1240744700486201963349949)
                    ·
                      rfl

theorem cell23_7249025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_7249025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249025 prefixEnd_7249025 := by exact prefixLift 7249025
  have htrace : WordTrace (prefixWord ++ tailWord_7249025) baseStart_7249025 baseEnd_7249025 := by
    simpa [prefixWord, tailWord_7249025, baseEnd_7249025] using wordTrace_append hprefix tailTrace_7249025
  have hstable : (prefixWord ++ tailWord_7249025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249025).length < 2 ^ (prefixWord ++ tailWord_7249025).sum := by decide
  have hdescent : baseEnd_7249025 < baseStart_7249025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249032 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_7249032 : Nat := 118140960795 + 7249032 * 2 ^ 59
def prefixEnd_7249032 : Nat := 4983230072969 + 3 ^ 40 * 7249032 * 2
def baseEnd_7249032 : Nat := 3722237695823187362662315

theorem tailTrace_7249032 : CollatzResearch.WordTrace tailWord_7249032 prefixEnd_7249032 3722237695823187362662315 := by
  unfold tailWord_7249032
  simp only [CollatzResearch.WordTrace]
  refine ⟨132196958937001287472810675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176262611916001716630414233 132196958937001287472810675)
  ·
    refine ⟨198295438405501931209216013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132196958937001287472810675 198295438405501931209216013)
    ·
      refine ⟨74360789402063224203456005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198295438405501931209216013 74360789402063224203456005)
      ·
        refine ⟨13942648012886854538148001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74360789402063224203456005 13942648012886854538148001)
        ·
          refine ⟨10456986009665140903611001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13942648012886854538148001 10456986009665140903611001)
          ·
            refine ⟨7842739507248855677708251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10456986009665140903611001 7842739507248855677708251)
            ·
              refine ⟨11764109260873283516562377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7842739507248855677708251 11764109260873283516562377)
              ·
                refine ⟨8823081945654962637421783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11764109260873283516562377 8823081945654962637421783)
                ·
                  refine ⟨13234622918482443956132675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8823081945654962637421783 13234622918482443956132675)
                  ·
                    refine ⟨19851934377723665934199013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13234622918482443956132675 19851934377723665934199013)
                    ·
                      refine ⟨3722237695823187362662315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19851934377723665934199013 3722237695823187362662315)
                      ·
                        rfl

theorem cell23_7249032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_7249032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249032 prefixEnd_7249032 := by exact prefixLift 7249032
  have htrace : WordTrace (prefixWord ++ tailWord_7249032) baseStart_7249032 baseEnd_7249032 := by
    simpa [prefixWord, tailWord_7249032, baseEnd_7249032] using wordTrace_append hprefix tailTrace_7249032
  have hstable : (prefixWord ++ tailWord_7249032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249032).length < 2 ^ (prefixWord ++ tailWord_7249032).sum := by decide
  have hdescent : baseEnd_7249032 < baseStart_7249032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249048 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 3, 3, 3]
def baseStart_7249048 : Nat := 118140960795 + 7249048 * 2 ^ 59
def prefixEnd_7249048 : Nat := 4983230072969 + 3 ^ 40 * 7249048 * 2
def baseEnd_7249048 : Nat := 3722245911513659300062241

theorem tailTrace_7249048 : CollatzResearch.WordTrace tailWord_7249048 prefixEnd_7249048 3722245911513659300062241 := by
  unfold tailWord_7249048
  simp only [CollatzResearch.WordTrace]
  refine ⟨132197250720972304839101899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176263000961296406452135865 132197250720972304839101899)
  ·
    refine ⟨198295876081458457258652849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132197250720972304839101899 198295876081458457258652849)
    ·
      refine ⟨148721907061093842943989637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198295876081458457258652849 148721907061093842943989637)
      ·
        refine ⟨27885357573955095551998057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148721907061093842943989637 27885357573955095551998057)
        ·
          refine ⟨20914018180466321663998543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27885357573955095551998057 20914018180466321663998543)
          ·
            refine ⟨31371027270699482495997815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20914018180466321663998543 31371027270699482495997815)
            ·
              refine ⟨47056540906049223743996723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31371027270699482495997815 47056540906049223743996723)
              ·
                refine ⟨70584811359073835615995085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47056540906049223743996723 70584811359073835615995085)
                ·
                  refine ⟨26469304259652688355998157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70584811359073835615995085 26469304259652688355998157)
                  ·
                    refine ⟨9925989097369758133499309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26469304259652688355998157 9925989097369758133499309)
                    ·
                      refine ⟨3722245911513659300062241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9925989097369758133499309 3722245911513659300062241)
                      ·
                        rfl

theorem cell23_7249048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_7249048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249048 prefixEnd_7249048 := by exact prefixLift 7249048
  have htrace : WordTrace (prefixWord ++ tailWord_7249048) baseStart_7249048 baseEnd_7249048 := by
    simpa [prefixWord, tailWord_7249048, baseEnd_7249048] using wordTrace_append hprefix tailTrace_7249048
  have hstable : (prefixWord ++ tailWord_7249048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249048).length < 2 ^ (prefixWord ++ tailWord_7249048).sum := by decide
  have hdescent : baseEnd_7249048 < baseStart_7249048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249052 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_7249052 : Nat := 118140960795 + 7249052 * 2 ^ 59
def prefixEnd_7249052 : Nat := 4983230072969 + 3 ^ 40 * 7249052 * 2
def baseEnd_7249052 : Nat := 3722247965436277284412223

theorem tailTrace_7249052 : CollatzResearch.WordTrace tailWord_7249052 prefixEnd_7249052 3722247965436277284412223 := by
  unfold tailWord_7249052
  simp only [CollatzResearch.WordTrace]
  refine ⟨132197323666965059180674705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176263098222620078907566273 132197323666965059180674705)
  ·
    refine ⟨99147992750223794385506029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132197323666965059180674705 99147992750223794385506029)
    ·
      refine ⟨37180497281333922894564761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99147992750223794385506029 37180497281333922894564761)
      ·
        refine ⟨27885372961000442170923571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37180497281333922894564761 27885372961000442170923571)
        ·
          refine ⟨41828059441500663256385357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27885372961000442170923571 41828059441500663256385357)
          ·
            refine ⟨15685522290562748721144509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41828059441500663256385357 15685522290562748721144509)
            ·
              refine ⟨5882070858961030770429191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15685522290562748721144509 5882070858961030770429191)
              ·
                refine ⟨8823106288441546155643787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5882070858961030770429191 8823106288441546155643787)
                ·
                  refine ⟨13234659432662319233465681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8823106288441546155643787 13234659432662319233465681)
                  ·
                    refine ⟨9925994574496739425099261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13234659432662319233465681 9925994574496739425099261)
                    ·
                      refine ⟨3722247965436277284412223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9925994574496739425099261 3722247965436277284412223)
                      ·
                        rfl

theorem cell23_7249052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_7249052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249052 prefixEnd_7249052 := by exact prefixLift 7249052
  have htrace : WordTrace (prefixWord ++ tailWord_7249052) baseStart_7249052 baseEnd_7249052 := by
    simpa [prefixWord, tailWord_7249052, baseEnd_7249052] using wordTrace_append hprefix tailTrace_7249052
  have hstable : (prefixWord ++ tailWord_7249052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249052).length < 2 ^ (prefixWord ++ tailWord_7249052).sum := by decide
  have hdescent : baseEnd_7249052 < baseStart_7249052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249066 : List Nat := [3, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_7249066 : Nat := 118140960795 + 7249066 * 2 ^ 59
def prefixEnd_7249066 : Nat := 4983230072969 + 3 ^ 40 * 7249066 * 2
def baseEnd_7249066 : Nat := 3722255154165440229637159

theorem tailTrace_7249066 : CollatzResearch.WordTrace tailWord_7249066 prefixEnd_7249066 3722255154165440229637159 := by
  unfold tailWord_7249066
  simp only [CollatzResearch.WordTrace]
  refine ⟨66098789488969849688089763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176263438637252932501572701 66098789488969849688089763)
  ·
    refine ⟨99148184233454774532134645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66098789488969849688089763 99148184233454774532134645)
    ·
      refine ⟨9295142271886385112387623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99148184233454774532134645 9295142271886385112387623)
      ·
        refine ⟨13942713407829577668581435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9295142271886385112387623 13942713407829577668581435)
        ·
          refine ⟨20914070111744366502872153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13942713407829577668581435 20914070111744366502872153)
          ·
            refine ⟨15685552583808274877154115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20914070111744366502872153 15685552583808274877154115)
            ·
              refine ⟨23528328875712412315731173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15685552583808274877154115 23528328875712412315731173)
              ·
                refine ⟨4411561664196077309199595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23528328875712412315731173 4411561664196077309199595)
                ·
                  refine ⟨6617342496294115963799393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411561664196077309199595 6617342496294115963799393)
                  ·
                    refine ⟨4963006872220586972849545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6617342496294115963799393 4963006872220586972849545)
                    ·
                      refine ⟨3722255154165440229637159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963006872220586972849545 3722255154165440229637159)
                      ·
                        rfl

theorem cell23_7249066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_7249066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249066 prefixEnd_7249066 := by exact prefixLift 7249066
  have htrace : WordTrace (prefixWord ++ tailWord_7249066) baseStart_7249066 baseEnd_7249066 := by
    simpa [prefixWord, tailWord_7249066, baseEnd_7249066] using wordTrace_append hprefix tailTrace_7249066
  have hstable : (prefixWord ++ tailWord_7249066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249066).length < 2 ^ (prefixWord ++ tailWord_7249066).sum := by decide
  have hdescent : baseEnd_7249066 < baseStart_7249066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249071 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 4]
def baseStart_7249071 : Nat := 118140960795 + 7249071 * 2 ^ 59
def prefixEnd_7249071 : Nat := 4983230072969 + 3 ^ 40 * 7249071 * 2
def baseEnd_7249071 : Nat := 3722257721568712710074635

theorem tailTrace_7249071 : CollatzResearch.WordTrace tailWord_7249071 prefixEnd_7249071 3722257721568712710074635 := by
  unfold tailWord_7249071
  simp only [CollatzResearch.WordTrace]
  refine ⟨264395340320861284606291067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176263560213907523070860711 264395340320861284606291067)
  ·
    refine ⟨396593010481291926909436601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264395340320861284606291067 396593010481291926909436601)
    ·
      refine ⟨297444757860968945182077451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396593010481291926909436601 297444757860968945182077451)
      ·
        refine ⟨446167136791453417773116177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297444757860968945182077451 446167136791453417773116177)
        ·
          refine ⟨334625352593590063329837133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446167136791453417773116177 334625352593590063329837133)
          ·
            refine ⟨125484507222596273748688925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334625352593590063329837133 125484507222596273748688925)
            ·
              refine ⟨47056690208473602655758347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125484507222596273748688925 47056690208473602655758347)
              ·
                refine ⟨70585035312710403983637521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47056690208473602655758347 70585035312710403983637521)
                ·
                  refine ⟨52938776484532802987728141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70585035312710403983637521 52938776484532802987728141)
                  ·
                    refine ⟨19852041181699801120398053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52938776484532802987728141 19852041181699801120398053)
                    ·
                      refine ⟨3722257721568712710074635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19852041181699801120398053 3722257721568712710074635)
                      ·
                        rfl

theorem cell23_7249071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_7249071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249071 prefixEnd_7249071 := by exact prefixLift 7249071
  have htrace : WordTrace (prefixWord ++ tailWord_7249071) baseStart_7249071 baseEnd_7249071 := by
    simpa [prefixWord, tailWord_7249071, baseEnd_7249071] using wordTrace_append hprefix tailTrace_7249071
  have hstable : (prefixWord ++ tailWord_7249071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249071).length < 2 ^ (prefixWord ++ tailWord_7249071).sum := by decide
  have hdescent : baseEnd_7249071 < baseStart_7249071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249081 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 1, 8]
def baseStart_7249081 : Nat := 118140960795 + 7249081 * 2 ^ 59
def prefixEnd_7249081 : Nat := 4983230072969 + 3 ^ 40 * 7249081 * 2
def baseEnd_7249081 : Nat := 1240754285458419223649863

theorem tailTrace_7249081 : CollatzResearch.WordTrace tailWord_7249081 prefixEnd_7249081 1240754285458419223649863 := by
  unfold tailWord_7249081
  simp only [CollatzResearch.WordTrace]
  refine ⟨264395705050825056314155097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176263803367216704209436731 264395705050825056314155097)
  ·
    refine ⟨198296778788118792235616323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264395705050825056314155097 198296778788118792235616323)
    ·
      refine ⟨297445168182178188353424485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198296778788118792235616323 297445168182178188353424485)
      ·
        refine ⟨55770969034158410316267091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297445168182178188353424485 55770969034158410316267091)
        ·
          refine ⟨83656453551237615474400637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55770969034158410316267091 83656453551237615474400637)
          ·
            refine ⟨31371170081714105802900239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83656453551237615474400637 31371170081714105802900239)
            ·
              refine ⟨47056755122571158704350359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31371170081714105802900239 47056755122571158704350359)
              ·
                refine ⟨70585132683856738056525539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47056755122571158704350359 70585132683856738056525539)
                ·
                  refine ⟨105877699025785107084788309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70585132683856738056525539 105877699025785107084788309)
                  ·
                    refine ⟨1240754285458419223649863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105877699025785107084788309 1240754285458419223649863)
                    ·
                      rfl

theorem cell23_7249081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_7249081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249081 prefixEnd_7249081 := by exact prefixLift 7249081
  have htrace : WordTrace (prefixWord ++ tailWord_7249081) baseStart_7249081 baseEnd_7249081 := by
    simpa [prefixWord, tailWord_7249081, baseEnd_7249081] using wordTrace_append hprefix tailTrace_7249081
  have hstable : (prefixWord ++ tailWord_7249081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249081).length < 2 ^ (prefixWord ++ tailWord_7249081).sum := by decide
  have hdescent : baseEnd_7249081 < baseStart_7249081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249091 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 5]
def baseStart_7249091 : Nat := 118140960795 + 7249091 * 2 ^ 59
def prefixEnd_7249091 : Nat := 4983230072969 + 3 ^ 40 * 7249091 * 2
def baseEnd_7249091 : Nat := 3722267991181802631824543

theorem tailTrace_7249091 : CollatzResearch.WordTrace tailWord_7249091 prefixEnd_7249091 3722267991181802631824543 := by
  unfold tailWord_7249091
  simp only [CollatzResearch.WordTrace]
  refine ⟨264396069780788828022019127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176264046520525885348012751 264396069780788828022019127)
  ·
    refine ⟨396594104671183242033028691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264396069780788828022019127 396594104671183242033028691)
    ·
      refine ⟨594891157006774863049543037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396594104671183242033028691 594891157006774863049543037)
      ·
        refine ⟨223084183877540573643578639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594891157006774863049543037 223084183877540573643578639)
        ·
          refine ⟨334626275816310860465367959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223084183877540573643578639 334626275816310860465367959)
          ·
            refine ⟨501939413724466290698051939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334626275816310860465367959 501939413724466290698051939)
            ·
              refine ⟨752909120586699436047077909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501939413724466290698051939 752909120586699436047077909)
              ·
                refine ⟨35292615027501536064706777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 752909120586699436047077909 35292615027501536064706777)
                ·
                  refine ⟨26469461270626152048530083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35292615027501536064706777 26469461270626152048530083)
                  ·
                    refine ⟨39704191905939228072795125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26469461270626152048530083 39704191905939228072795125)
                    ·
                      refine ⟨3722267991181802631824543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39704191905939228072795125 3722267991181802631824543)
                      ·
                        rfl

theorem cell23_7249091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_7249091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249091 prefixEnd_7249091 := by exact prefixLift 7249091
  have htrace : WordTrace (prefixWord ++ tailWord_7249091) baseStart_7249091 baseEnd_7249091 := by
    simpa [prefixWord, tailWord_7249091, baseEnd_7249091] using wordTrace_append hprefix tailTrace_7249091
  have hstable : (prefixWord ++ tailWord_7249091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249091).length < 2 ^ (prefixWord ++ tailWord_7249091).sum := by decide
  have hdescent : baseEnd_7249091 < baseStart_7249091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249105 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 4, 2, 2]
def baseStart_7249105 : Nat := 118140960795 + 7249105 * 2 ^ 59
def prefixEnd_7249105 : Nat := 4983230072969 + 3 ^ 40 * 7249105 * 2
def baseEnd_7249105 : Nat := 3722275179910965577049479

theorem tailTrace_7249105 : CollatzResearch.WordTrace tailWord_7249105 prefixEnd_7249105 3722275179910965577049479 := by
  unfold tailWord_7249105
  simp only [CollatzResearch.WordTrace]
  refine ⟨264396580402738108413028769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176264386935158738942019179 264396580402738108413028769)
  ·
    refine ⟨198297435302053581309771577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264396580402738108413028769 198297435302053581309771577)
    ·
      refine ⟨148723076476540185982328683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198297435302053581309771577 148723076476540185982328683)
      ·
        refine ⟨223084614714810278973493025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148723076476540185982328683 223084614714810278973493025)
        ·
          refine ⟨167313461036107709230119769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223084614714810278973493025 167313461036107709230119769)
          ·
            refine ⟨125485095777080781922589827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167313461036107709230119769 125485095777080781922589827)
            ·
              refine ⟨188227643665621172883884741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125485095777080781922589827 188227643665621172883884741)
              ·
                refine ⟨35292683187303969915728389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188227643665621172883884741 35292683187303969915728389)
                ·
                  refine ⟨6617378097619494359199073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35292683187303969915728389 6617378097619494359199073)
                  ·
                    refine ⟨4963033573214620769399305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6617378097619494359199073 4963033573214620769399305)
                    ·
                      refine ⟨3722275179910965577049479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963033573214620769399305 3722275179910965577049479)
                      ·
                        rfl

theorem cell23_7249105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 2, 2].length) (baseStart_7249105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249105 prefixEnd_7249105 := by exact prefixLift 7249105
  have htrace : WordTrace (prefixWord ++ tailWord_7249105) baseStart_7249105 baseEnd_7249105 := by
    simpa [prefixWord, tailWord_7249105, baseEnd_7249105] using wordTrace_append hprefix tailTrace_7249105
  have hstable : (prefixWord ++ tailWord_7249105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249105).length < 2 ^ (prefixWord ++ tailWord_7249105).sum := by decide
  have hdescent : baseEnd_7249105 < baseStart_7249105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249109 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 1, 3, 2]
def baseStart_7249109 : Nat := 118140960795 + 7249109 * 2 ^ 59
def prefixEnd_7249109 : Nat := 4983230072969 + 3 ^ 40 * 7249109 * 2
def baseEnd_7249109 : Nat := 3722277233833583561399461

theorem tailTrace_7249109 : CollatzResearch.WordTrace tailWord_7249109 prefixEnd_7249109 3722277233833583561399461 := by
  unfold tailWord_7249109
  simp only [CollatzResearch.WordTrace]
  refine ⟨264396726294723617096174381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176264484196482411397449587 264396726294723617096174381)
  ·
    refine ⟨99148772360521356411065393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264396726294723617096174381 99148772360521356411065393)
    ·
      refine ⟨74361579270391017308299045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99148772360521356411065393 74361579270391017308299045)
      ·
        refine ⟨13942796113198315745306071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74361579270391017308299045 13942796113198315745306071)
        ·
          refine ⟨20914194169797473617959107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13942796113198315745306071 20914194169797473617959107)
          ·
            refine ⟨31371291254696210426938661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20914194169797473617959107 31371291254696210426938661)
            ·
              refine ⟨5882117110255539455050999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31371291254696210426938661 5882117110255539455050999)
              ·
                refine ⟨8823175665383309182576499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5882117110255539455050999 8823175665383309182576499)
                ·
                  refine ⟨13234763498074963773864749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8823175665383309182576499 13234763498074963773864749)
                  ·
                    refine ⟨4963036311778111415199281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13234763498074963773864749 4963036311778111415199281)
                    ·
                      refine ⟨3722277233833583561399461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963036311778111415199281 3722277233833583561399461)
                      ·
                        rfl

theorem cell23_7249109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_7249109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249109 prefixEnd_7249109 := by exact prefixLift 7249109
  have htrace : WordTrace (prefixWord ++ tailWord_7249109) baseStart_7249109 baseEnd_7249109 := by
    simpa [prefixWord, tailWord_7249109, baseEnd_7249109] using wordTrace_append hprefix tailTrace_7249109
  have hstable : (prefixWord ++ tailWord_7249109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249109).length < 2 ^ (prefixWord ++ tailWord_7249109).sum := by decide
  have hdescent : baseEnd_7249109 < baseStart_7249109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249128 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 7]
def baseStart_7249128 : Nat := 118140960795 + 7249128 * 2 ^ 59
def prefixEnd_7249128 : Nat := 4983230072969 + 3 ^ 40 * 7249128 * 2
def baseEnd_7249128 : Nat := 413587443329557665229097

theorem tailTrace_7249128 : CollatzResearch.WordTrace tailWord_7249128 prefixEnd_7249128 413587443329557665229097 := by
  unfold tailWord_7249128
  simp only [CollatzResearch.WordTrace]
  refine ⟨132198709640827391670558019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176264946187769855560744025 132198709640827391670558019)
  ·
    refine ⟨198298064461241087505837029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132198709640827391670558019 198298064461241087505837029)
    ·
      refine ⟨37180887086482703907344443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198298064461241087505837029 37180887086482703907344443)
      ·
        refine ⟨55771330629724055861016665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37180887086482703907344443 55771330629724055861016665)
        ·
          refine ⟨41828497972293041895762499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55771330629724055861016665 41828497972293041895762499)
          ·
            refine ⟨62742746958439562843643749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41828497972293041895762499 62742746958439562843643749)
            ·
              refine ⟨11764265054707418033183203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62742746958439562843643749 11764265054707418033183203)
              ·
                refine ⟨17646397582061127049774805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11764265054707418033183203 17646397582061127049774805)
                ·
                  refine ⟨413587443329557665229097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17646397582061127049774805 413587443329557665229097)
                  ·
                    rfl

theorem cell23_7249128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 7].length) (baseStart_7249128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249128 prefixEnd_7249128 := by exact prefixLift 7249128
  have htrace : WordTrace (prefixWord ++ tailWord_7249128) baseStart_7249128 baseEnd_7249128 := by
    simpa [prefixWord, tailWord_7249128, baseEnd_7249128] using wordTrace_append hprefix tailTrace_7249128
  have hstable : (prefixWord ++ tailWord_7249128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249128).length < 2 ^ (prefixWord ++ tailWord_7249128).sum := by decide
  have hdescent : baseEnd_7249128 < baseStart_7249128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249139 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 2, 2, 2]
def baseStart_7249139 : Nat := 118140960795 + 7249139 * 2 ^ 59
def prefixEnd_7249139 : Nat := 4983230072969 + 3 ^ 40 * 7249139 * 2
def baseEnd_7249139 : Nat := 3722292638253218444024323

theorem tailTrace_7249139 : CollatzResearch.WordTrace tailWord_7249139 prefixEnd_7249139 3722292638253218444024323 := by
  unfold tailWord_7249139
  simp only [CollatzResearch.WordTrace]
  refine ⟨264397820484614932219766471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176265213656409954813177647 264397820484614932219766471)
  ·
    refine ⟨396596730726922398329649707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264397820484614932219766471 396596730726922398329649707)
    ·
      refine ⟨594895096090383597494474561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396596730726922398329649707 594895096090383597494474561)
      ·
        refine ⟨446171322067787698120855921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594895096090383597494474561 446171322067787698120855921)
        ·
          refine ⟨334628491550840773590641941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446171322067787698120855921 334628491550840773590641941)
          ·
            refine ⟨15685710541445661262061341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 334628491550840773590641941 15685710541445661262061341)
            ·
              refine ⟨5882141453042122973273003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15685710541445661262061341 5882141453042122973273003)
              ·
                refine ⟨8823212179563184459909505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5882141453042122973273003 8823212179563184459909505)
                ·
                  refine ⟨6617409134672388344932129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8823212179563184459909505 6617409134672388344932129)
                  ·
                    refine ⟨4963056851004291258699097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6617409134672388344932129 4963056851004291258699097)
                    ·
                      refine ⟨3722292638253218444024323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963056851004291258699097 3722292638253218444024323)
                      ·
                        rfl

theorem cell23_7249139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 2, 2, 2].length) (baseStart_7249139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249139 prefixEnd_7249139 := by exact prefixLift 7249139
  have htrace : WordTrace (prefixWord ++ tailWord_7249139) baseStart_7249139 baseEnd_7249139 := by
    simpa [prefixWord, tailWord_7249139, baseEnd_7249139] using wordTrace_append hprefix tailTrace_7249139
  have hstable : (prefixWord ++ tailWord_7249139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249139).length < 2 ^ (prefixWord ++ tailWord_7249139).sum := by decide
  have hdescent : baseEnd_7249139 < baseStart_7249139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249215 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 3]
def baseStart_7249215 : Nat := 118140960795 + 7249215 * 2 ^ 59
def prefixEnd_7249215 : Nat := 4983230072969 + 3 ^ 40 * 7249215 * 2
def baseEnd_7249215 : Nat := 3722331662782960146673973

theorem tailTrace_7249215 : CollatzResearch.WordTrace tailWord_7249215 prefixEnd_7249215 3722331662782960146673973 := by
  unfold tailWord_7249215
  simp only [CollatzResearch.WordTrace]
  refine ⟨264400592432339597199533099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176267061621559731466355399 264400592432339597199533099)
  ·
    refine ⟨396600888648509395799299649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264400592432339597199533099 396600888648509395799299649)
    ·
      refine ⟨297450666486382046849474737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396600888648509395799299649 297450666486382046849474737)
      ·
        refine ⟨223087999864786535137106053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297450666486382046849474737 223087999864786535137106053)
        ·
          refine ⟨41828999974647475338207385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223087999864786535137106053 41828999974647475338207385)
          ·
            refine ⟨31371749980985606503655539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41828999974647475338207385 31371749980985606503655539)
            ·
              refine ⟨47057624971478409755483309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31371749980985606503655539 47057624971478409755483309)
              ·
                refine ⟨17646609364304403658306241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47057624971478409755483309 17646609364304403658306241)
                ·
                  refine ⟨13234957023228302743729681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17646609364304403658306241 13234957023228302743729681)
                  ·
                    refine ⟨9926217767421227057797261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13234957023228302743729681 9926217767421227057797261)
                    ·
                      refine ⟨3722331662782960146673973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9926217767421227057797261 3722331662782960146673973)
                      ·
                        rfl

theorem cell23_7249215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_7249215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249215 prefixEnd_7249215 := by exact prefixLift 7249215
  have htrace : WordTrace (prefixWord ++ tailWord_7249215) baseStart_7249215 baseEnd_7249215 := by
    simpa [prefixWord, tailWord_7249215, baseEnd_7249215] using wordTrace_append hprefix tailTrace_7249215
  have hstable : (prefixWord ++ tailWord_7249215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249215).length < 2 ^ (prefixWord ++ tailWord_7249215).sum := by decide
  have hdescent : baseEnd_7249215 < baseStart_7249215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249239 : List Nat := [1, 1, 3, 2, 3, 2, 4, 2, 1, 4]
def baseStart_7249239 : Nat := 118140960795 + 7249239 * 2 ^ 59
def prefixEnd_7249239 : Nat := 4983230072969 + 3 ^ 40 * 7249239 * 2
def baseEnd_7249239 : Nat := 1240781328772889350924621

theorem tailTrace_7249239 : CollatzResearch.WordTrace tailWord_7249239 prefixEnd_7249239 1240781328772889350924621 := by
  unfold tailWord_7249239
  simp only [CollatzResearch.WordTrace]
  refine ⟨264401467784252649298406771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176267645189501766198937847 264401467784252649298406771)
  ·
    refine ⟨396602201676378973947610157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264401467784252649298406771 396602201676378973947610157)
    ·
      refine ⟨148725825628642115230353809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396602201676378973947610157 148725825628642115230353809)
      ·
        refine ⟨111544369221481586422765357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148725825628642115230353809 111544369221481586422765357)
        ·
          refine ⟨41829138458055594908537009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111544369221481586422765357 41829138458055594908537009)
          ·
            refine ⟨31371853843541696181402757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41829138458055594908537009 31371853843541696181402757)
            ·
              refine ⟨5882222595664068034013017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31371853843541696181402757 5882222595664068034013017)
              ·
                refine ⟨4411666946748051025509763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5882222595664068034013017 4411666946748051025509763)
                ·
                  refine ⟨6617500420122076538264645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411666946748051025509763 6617500420122076538264645)
                  ·
                    refine ⟨1240781328772889350924621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617500420122076538264645 1240781328772889350924621)
                    ·
                      rfl

theorem cell23_7249239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_7249239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249239 prefixEnd_7249239 := by exact prefixLift 7249239
  have htrace : WordTrace (prefixWord ++ tailWord_7249239) baseStart_7249239 baseEnd_7249239 := by
    simpa [prefixWord, tailWord_7249239, baseEnd_7249239] using wordTrace_append hprefix tailTrace_7249239
  have hstable : (prefixWord ++ tailWord_7249239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249239).length < 2 ^ (prefixWord ++ tailWord_7249239).sum := by decide
  have hdescent : baseEnd_7249239 < baseStart_7249239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249305 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 5]
def baseStart_7249305 : Nat := 118140960795 + 7249305 * 2 ^ 59
def prefixEnd_7249305 : Nat := 4983230072969 + 3 ^ 40 * 7249305 * 2
def baseEnd_7249305 : Nat := 3722377876041864794548559

theorem tailTrace_7249305 : CollatzResearch.WordTrace tailWord_7249305 prefixEnd_7249305 3722377876041864794548559 := by
  unfold tailWord_7249305
  simp only [CollatzResearch.WordTrace]
  refine ⟨264403875002013542570309369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176269250001342361713539579 264403875002013542570309369)
  ·
    refine ⟨198302906251510156927732027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264403875002013542570309369 198302906251510156927732027)
    ·
      refine ⟨297454359377265235391598041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198302906251510156927732027 297454359377265235391598041)
      ·
        refine ⟨223090769532948926543698531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297454359377265235391598041 223090769532948926543698531)
        ·
          refine ⟨334636154299423389815547797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223090769532948926543698531 334636154299423389815547797)
          ·
            refine ⟨15686069732785471397603803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 334636154299423389815547797 15686069732785471397603803)
            ·
              refine ⟨23529104599178207096405705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15686069732785471397603803 23529104599178207096405705)
              ·
                refine ⟨17646828449383655322304279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23529104599178207096405705 17646828449383655322304279)
                ·
                  refine ⟨26470242674075482983456419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17646828449383655322304279 26470242674075482983456419)
                  ·
                    refine ⟨39705364011113224475184629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26470242674075482983456419 39705364011113224475184629)
                    ·
                      refine ⟨3722377876041864794548559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39705364011113224475184629 3722377876041864794548559)
                      ·
                        rfl

theorem cell23_7249305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_7249305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249305 prefixEnd_7249305 := by exact prefixLift 7249305
  have htrace : WordTrace (prefixWord ++ tailWord_7249305) baseStart_7249305 baseEnd_7249305 := by
    simpa [prefixWord, tailWord_7249305, baseEnd_7249305] using wordTrace_append hprefix tailTrace_7249305
  have hstable : (prefixWord ++ tailWord_7249305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249305).length < 2 ^ (prefixWord ++ tailWord_7249305).sum := by decide
  have hdescent : baseEnd_7249305 < baseStart_7249305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249319 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_7249319 : Nat := 118140960795 + 7249319 * 2 ^ 59
def prefixEnd_7249319 : Nat := 4983230072969 + 3 ^ 40 * 7249319 * 2
def baseEnd_7249319 : Nat := 3722385064771027739773495

theorem tailTrace_7249319 : CollatzResearch.WordTrace tailWord_7249319 prefixEnd_7249319 3722385064771027739773495 := by
  unfold tailWord_7249319
  simp only [CollatzResearch.WordTrace]
  refine ⟨264404385623962822961319011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176269590415975215307546007 264404385623962822961319011)
  ·
    refine ⟨396606578435944234441978517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264404385623962822961319011 396606578435944234441978517)
    ·
      refine ⟨18590933364184885989467743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 396606578435944234441978517 18590933364184885989467743)
      ·
        refine ⟨27886400046277328984201615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18590933364184885989467743 27886400046277328984201615)
        ·
          refine ⟨41829600069415993476302423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27886400046277328984201615 41829600069415993476302423)
          ·
            refine ⟨62744400104123990214453635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41829600069415993476302423 62744400104123990214453635)
            ·
              refine ⟨94116600156185985321680453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62744400104123990214453635 94116600156185985321680453)
              ·
                refine ⟨17646862529284872247815085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94116600156185985321680453 17646862529284872247815085)
                ·
                  refine ⟨6617573448481827092930657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17646862529284872247815085 6617573448481827092930657)
                  ·
                    refine ⟨4963180086361370319697993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6617573448481827092930657 4963180086361370319697993)
                    ·
                      refine ⟨3722385064771027739773495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963180086361370319697993 3722385064771027739773495)
                      ·
                        rfl

theorem cell23_7249319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_7249319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249319 prefixEnd_7249319 := by exact prefixLift 7249319
  have htrace : WordTrace (prefixWord ++ tailWord_7249319) baseStart_7249319 baseEnd_7249319 := by
    simpa [prefixWord, tailWord_7249319, baseEnd_7249319] using wordTrace_append hprefix tailTrace_7249319
  have hstable : (prefixWord ++ tailWord_7249319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249319).length < 2 ^ (prefixWord ++ tailWord_7249319).sum := by decide
  have hdescent : baseEnd_7249319 < baseStart_7249319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249335 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 3]
def baseStart_7249335 : Nat := 118140960795 + 7249335 * 2 ^ 59
def prefixEnd_7249335 : Nat := 4983230072969 + 3 ^ 40 * 7249335 * 2
def baseEnd_7249335 : Nat := 3722393280461499677173421

theorem tailTrace_7249335 : CollatzResearch.WordTrace tailWord_7249335 prefixEnd_7249335 3722393280461499677173421 := by
  unfold tailWord_7249335
  simp only [CollatzResearch.WordTrace]
  refine ⟨264404969191904857693901459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176269979461269905129267639 264404969191904857693901459)
  ·
    refine ⟨396607453787857286540852189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264404969191904857693901459 396607453787857286540852189)
    ·
      refine ⟨148727795170446482452819571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396607453787857286540852189 148727795170446482452819571)
      ·
        refine ⟨223091692755669723679229357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148727795170446482452819571 223091692755669723679229357)
        ·
          refine ⟨83659384783376146379711009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223091692755669723679229357 83659384783376146379711009)
          ·
            refine ⟨62744538587532109784783257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83659384783376146379711009 62744538587532109784783257)
            ·
              refine ⟨47058403940649082338587443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62744538587532109784783257 47058403940649082338587443)
              ·
                refine ⟨70587605910973623507881165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47058403940649082338587443 70587605910973623507881165)
                ·
                  refine ⟨26470352216615108815455437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70587605910973623507881165 26470352216615108815455437)
                  ·
                    refine ⟨9926382081230665805795789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26470352216615108815455437 9926382081230665805795789)
                    ·
                      refine ⟨3722393280461499677173421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9926382081230665805795789 3722393280461499677173421)
                      ·
                        rfl

theorem cell23_7249335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_7249335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249335 prefixEnd_7249335 := by exact prefixLift 7249335
  have htrace : WordTrace (prefixWord ++ tailWord_7249335) baseStart_7249335 baseEnd_7249335 := by
    simpa [prefixWord, tailWord_7249335, baseEnd_7249335] using wordTrace_append hprefix tailTrace_7249335
  have hstable : (prefixWord ++ tailWord_7249335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249335).length < 2 ^ (prefixWord ++ tailWord_7249335).sum := by decide
  have hdescent : baseEnd_7249335 < baseStart_7249335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249336 : List Nat := [2, 1, 2, 1, 2, 2, 5, 3, 1, 2, 2]
def baseStart_7249336 : Nat := 118140960795 + 7249336 * 2 ^ 59
def prefixEnd_7249336 : Nat := 4983230072969 + 3 ^ 40 * 7249336 * 2
def baseEnd_7249336 : Nat := 3722393793942154173260917

theorem tailTrace_7249336 : CollatzResearch.WordTrace tailWord_7249336 prefixEnd_7249336 3722393793942154173260917 := by
  unfold tailWord_7249336
  simp only [CollatzResearch.WordTrace]
  refine ⟨132202502832450617432343931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176270003776600823243125241 132202502832450617432343931)
  ·
    refine ⟨198303754248675926148515897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132202502832450617432343931 198303754248675926148515897)
    ·
      refine ⟨148727815686506944611386923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198303754248675926148515897 148727815686506944611386923)
      ·
        refine ⟨223091723529760416917080385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148727815686506944611386923 223091723529760416917080385)
        ·
          refine ⟨167318792647320312687810289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223091723529760416917080385 167318792647320312687810289)
          ·
            refine ⟨125489094485490234515857717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167318792647320312687810289 125489094485490234515857717)
            ·
              refine ⟨11764602608014709485861661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125489094485490234515857717 11764602608014709485861661)
              ·
                refine ⟨4411725978005516057198123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11764602608014709485861661 4411725978005516057198123)
                ·
                  refine ⟨6617588967008274085797185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411725978005516057198123 6617588967008274085797185)
                  ·
                    refine ⟨4963191725256205564347889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6617588967008274085797185 4963191725256205564347889)
                    ·
                      refine ⟨3722393793942154173260917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963191725256205564347889 3722393793942154173260917)
                      ·
                        rfl

theorem cell23_7249336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 1, 2, 2].length) (baseStart_7249336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249336 prefixEnd_7249336 := by exact prefixLift 7249336
  have htrace : WordTrace (prefixWord ++ tailWord_7249336) baseStart_7249336 baseEnd_7249336 := by
    simpa [prefixWord, tailWord_7249336, baseEnd_7249336] using wordTrace_append hprefix tailTrace_7249336
  have hstable : (prefixWord ++ tailWord_7249336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249336).length < 2 ^ (prefixWord ++ tailWord_7249336).sum := by decide
  have hdescent : baseEnd_7249336 < baseStart_7249336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249338 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_7249338 : Nat := 118140960795 + 7249338 * 2 ^ 59
def prefixEnd_7249338 : Nat := 4983230072969 + 3 ^ 40 * 7249338 * 2
def baseEnd_7249338 : Nat := 1240798273634487721811969

theorem tailTrace_7249338 : CollatzResearch.WordTrace tailWord_7249338 prefixEnd_7249338 1240798273634487721811969 := by
  unfold tailWord_7249338
  simp only [CollatzResearch.WordTrace]
  refine ⟨66101269652723497301565167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176270052407262659470840445 66101269652723497301565167)
  ·
    refine ⟨99151904479085245952347751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66101269652723497301565167 99151904479085245952347751)
    ·
      refine ⟨148727856718627868928521627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99151904479085245952347751 148727856718627868928521627)
      ·
        refine ⟨223091785077941803392782441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148727856718627868928521627 223091785077941803392782441)
        ·
          refine ⟨167318838808456352544586831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223091785077941803392782441 167318838808456352544586831)
          ·
            refine ⟨250978258212684528816880247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167318838808456352544586831 250978258212684528816880247)
            ·
              refine ⟨376467387319026793225320371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250978258212684528816880247 376467387319026793225320371)
              ·
                refine ⟨564701080978540189837980557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376467387319026793225320371 564701080978540189837980557)
                ·
                  refine ⟨211762905366952571189242709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564701080978540189837980557 211762905366952571189242709)
                  ·
                    refine ⟨1240798273634487721811969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 211762905366952571189242709 1240798273634487721811969)
                    ·
                      rfl

theorem cell23_7249338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_7249338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249338 prefixEnd_7249338 := by exact prefixLift 7249338
  have htrace : WordTrace (prefixWord ++ tailWord_7249338) baseStart_7249338 baseEnd_7249338 := by
    simpa [prefixWord, tailWord_7249338, baseEnd_7249338] using wordTrace_append hprefix tailTrace_7249338
  have hstable : (prefixWord ++ tailWord_7249338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249338).length < 2 ^ (prefixWord ++ tailWord_7249338).sum := by decide
  have hdescent : baseEnd_7249338 < baseStart_7249338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249352 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_7249352 : Nat := 118140960795 + 7249352 * 2 ^ 59
def prefixEnd_7249352 : Nat := 4983230072969 + 3 ^ 40 * 7249352 * 2
def baseEnd_7249352 : Nat := 3722402009632626110660843

theorem tailTrace_7249352 : CollatzResearch.WordTrace tailWord_7249352 prefixEnd_7249352 3722402009632626110660843 := by
  unfold tailWord_7249352
  simp only [CollatzResearch.WordTrace]
  refine ⟨132202794616421634798635155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176270392821895513064846873 132202794616421634798635155)
  ·
    refine ⟨198304191924632452197952733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132202794616421634798635155 198304191924632452197952733)
    ·
      refine ⟨74364071971737169574232275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198304191924632452197952733 74364071971737169574232275)
      ·
        refine ⟨111546107957605754361348413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74364071971737169574232275 111546107957605754361348413)
        ·
          refine ⟨41829790484102157885505655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111546107957605754361348413 41829790484102157885505655)
          ·
            refine ⟨62744685726153236828258483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41829790484102157885505655 62744685726153236828258483)
            ·
              refine ⟨94117028589229855242387725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62744685726153236828258483 94117028589229855242387725)
              ·
                refine ⟨35293885720961195715895397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94117028589229855242387725 35293885720961195715895397)
                ·
                  refine ⟨6617603572680224196730387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35293885720961195715895397 6617603572680224196730387)
                  ·
                    refine ⟨9926405359020336295095581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6617603572680224196730387 9926405359020336295095581)
                    ·
                      refine ⟨3722402009632626110660843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9926405359020336295095581 3722402009632626110660843)
                      ·
                        rfl

theorem cell23_7249352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_7249352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249352 prefixEnd_7249352 := by exact prefixLift 7249352
  have htrace : WordTrace (prefixWord ++ tailWord_7249352) baseStart_7249352 baseEnd_7249352 := by
    simpa [prefixWord, tailWord_7249352, baseEnd_7249352] using wordTrace_append hprefix tailTrace_7249352
  have hstable : (prefixWord ++ tailWord_7249352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249352).length < 2 ^ (prefixWord ++ tailWord_7249352).sum := by decide
  have hdescent : baseEnd_7249352 < baseStart_7249352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249369 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 2, 1, 3]
def baseStart_7249369 : Nat := 118140960795 + 7249369 * 2 ^ 59
def prefixEnd_7249369 : Nat := 4983230072969 + 3 ^ 40 * 7249369 * 2
def baseEnd_7249369 : Nat := 3722410738803752544148265

theorem tailTrace_7249369 : CollatzResearch.WordTrace tailWord_7249369 prefixEnd_7249369 3722410738803752544148265 := by
  unfold tailWord_7249369
  simp only [CollatzResearch.WordTrace]
  refine ⟨264406209273781681500639161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176270806182521121000426107 264406209273781681500639161)
  ·
    refine ⟨198304656955336261125479371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264406209273781681500639161 198304656955336261125479371)
    ·
      refine ⟨297456985433004391688219057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198304656955336261125479371 297456985433004391688219057)
      ·
        refine ⟨223092739074753293766164293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297456985433004391688219057 223092739074753293766164293)
        ·
          refine ⟨41829888576516242581155805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223092739074753293766164293 41829888576516242581155805)
          ·
            refine ⟨15686208216193590967933427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41829888576516242581155805 15686208216193590967933427)
            ·
              refine ⟨23529312324290386451900141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15686208216193590967933427 23529312324290386451900141)
              ·
                refine ⟨8823492121608894919462553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23529312324290386451900141 8823492121608894919462553)
                ·
                  refine ⟨6617619091206671189596915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8823492121608894919462553 6617619091206671189596915)
                  ·
                    refine ⟨9926428636810006784395373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6617619091206671189596915 9926428636810006784395373)
                    ·
                      refine ⟨3722410738803752544148265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9926428636810006784395373 3722410738803752544148265)
                      ·
                        rfl

theorem cell23_7249369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_7249369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249369 prefixEnd_7249369 := by exact prefixLift 7249369
  have htrace : WordTrace (prefixWord ++ tailWord_7249369) baseStart_7249369 baseEnd_7249369 := by
    simpa [prefixWord, tailWord_7249369, baseEnd_7249369] using wordTrace_append hprefix tailTrace_7249369
  have hstable : (prefixWord ++ tailWord_7249369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249369).length < 2 ^ (prefixWord ++ tailWord_7249369).sum := by decide
  have hdescent : baseEnd_7249369 < baseStart_7249369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249379 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 3, 3, 2]
def baseStart_7249379 : Nat := 118140960795 + 7249379 * 2 ^ 59
def prefixEnd_7249379 : Nat := 4983230072969 + 3 ^ 40 * 7249379 * 2
def baseEnd_7249379 : Nat := 3722415873610297505023219

theorem tailTrace_7249379 : CollatzResearch.WordTrace tailWord_7249379 prefixEnd_7249379 3722415873610297505023219 := by
  unfold tailWord_7249379
  simp only [CollatzResearch.WordTrace]
  refine ⟨264406574003745453208503191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176271049335830302139002127 264406574003745453208503191)
  ·
    refine ⟨396609861005618179812754787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264406574003745453208503191 396609861005618179812754787)
    ·
      refine ⟨594914791508427269719132181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396609861005618179812754787 594914791508427269719132181)
      ·
        refine ⟨27886630851957528268084321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 594914791508427269719132181 27886630851957528268084321)
        ·
          refine ⟨20914973138968146201063241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27886630851957528268084321 20914973138968146201063241)
          ·
            refine ⟨15686229854226109650797431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20914973138968146201063241 15686229854226109650797431)
            ·
              refine ⟨23529344781339164476196147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15686229854226109650797431 23529344781339164476196147)
              ·
                refine ⟨35294017172008746714294221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23529344781339164476196147 35294017172008746714294221)
                ·
                  refine ⟨13235256439503280017860333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35294017172008746714294221 13235256439503280017860333)
                  ·
                    refine ⟨4963221164813730006697625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13235256439503280017860333 4963221164813730006697625)
                    ·
                      refine ⟨3722415873610297505023219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963221164813730006697625 3722415873610297505023219)
                      ·
                        rfl

theorem cell23_7249379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_7249379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249379 prefixEnd_7249379 := by exact prefixLift 7249379
  have htrace : WordTrace (prefixWord ++ tailWord_7249379) baseStart_7249379 baseEnd_7249379 := by
    simpa [prefixWord, tailWord_7249379, baseEnd_7249379] using wordTrace_append hprefix tailTrace_7249379
  have hstable : (prefixWord ++ tailWord_7249379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249379).length < 2 ^ (prefixWord ++ tailWord_7249379).sum := by decide
  have hdescent : baseEnd_7249379 < baseStart_7249379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249392 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 3, 4, 2]
def baseStart_7249392 : Nat := 118140960795 + 7249392 * 2 ^ 59
def prefixEnd_7249392 : Nat := 4983230072969 + 3 ^ 40 * 7249392 * 2
def baseEnd_7249392 : Nat := 3722422548858805954160659

theorem tailTrace_7249392 : CollatzResearch.WordTrace tailWord_7249392 prefixEnd_7249392 3722422548858805954160659 := by
  unfold tailWord_7249392
  simp only [CollatzResearch.WordTrace]
  refine ⟨132203524076349178214363215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176271365435132237619150953 132203524076349178214363215)
  ·
    refine ⟨198305286114523767321544823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132203524076349178214363215 198305286114523767321544823)
    ·
      refine ⟨297457929171785650982317235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198305286114523767321544823 297457929171785650982317235)
      ·
        refine ⟨446186893757678476473475853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297457929171785650982317235 446186893757678476473475853)
        ·
          refine ⟨167320085159129428677553445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446186893757678476473475853 167320085159129428677553445)
          ·
            refine ⟨31372515967336767877041271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167320085159129428677553445 31372515967336767877041271)
            ·
              refine ⟨47058773951005151815561907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31372515967336767877041271 47058773951005151815561907)
              ·
                refine ⟨70588160926507727723342861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47058773951005151815561907 70588160926507727723342861)
                ·
                  refine ⟨26470560347440397896253573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70588160926507727723342861 26470560347440397896253573)
                  ·
                    refine ⟨4963230065145074605547545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26470560347440397896253573 4963230065145074605547545)
                    ·
                      refine ⟨3722422548858805954160659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963230065145074605547545 3722422548858805954160659)
                      ·
                        rfl

theorem cell23_7249392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 4, 2].length) (baseStart_7249392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249392 prefixEnd_7249392 := by exact prefixLift 7249392
  have htrace : WordTrace (prefixWord ++ tailWord_7249392) baseStart_7249392 baseEnd_7249392 := by
    simpa [prefixWord, tailWord_7249392, baseEnd_7249392] using wordTrace_append hprefix tailTrace_7249392
  have hstable : (prefixWord ++ tailWord_7249392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249392).length < 2 ^ (prefixWord ++ tailWord_7249392).sum := by decide
  have hdescent : baseEnd_7249392 < baseStart_7249392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249432 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 7]
def baseStart_7249432 : Nat := 118140960795 + 7249432 * 2 ^ 59
def prefixEnd_7249432 : Nat := 4983230072969 + 3 ^ 40 * 7249432 * 2
def baseEnd_7249432 : Nat := 413604787564998421962275

theorem tailTrace_7249432 : CollatzResearch.WordTrace tailWord_7249432 prefixEnd_7249432 413604787564998421962275 := by
  unfold tailWord_7249432
  simp only [CollatzResearch.WordTrace]
  refine ⟨132204253536276721630091275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176272338048368962173455033 132204253536276721630091275)
  ·
    refine ⟨198306380304415082445136913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132204253536276721630091275 198306380304415082445136913)
    ·
      refine ⟨148729785228311311833852685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198306380304415082445136913 148729785228311311833852685)
      ·
        refine ⟨55773669460616741937694757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148729785228311311833852685 55773669460616741937694757)
        ·
          refine ⟨10457563023865639113317767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55773669460616741937694757 10457563023865639113317767)
          ·
            refine ⟨15686344535798458669976651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10457563023865639113317767 15686344535798458669976651)
            ·
              refine ⟨23529516803697688004964977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15686344535798458669976651 23529516803697688004964977)
              ·
                refine ⟨17647137602773266003723733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23529516803697688004964977 17647137602773266003723733)
                ·
                  refine ⟨413604787564998421962275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17647137602773266003723733 413604787564998421962275)
                  ·
                    rfl

theorem cell23_7249432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 7].length) (baseStart_7249432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249432 prefixEnd_7249432 := by exact prefixLift 7249432
  have htrace : WordTrace (prefixWord ++ tailWord_7249432) baseStart_7249432 baseEnd_7249432 := by
    simpa [prefixWord, tailWord_7249432, baseEnd_7249432] using wordTrace_append hprefix tailTrace_7249432
  have hstable : (prefixWord ++ tailWord_7249432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249432).length < 2 ^ (prefixWord ++ tailWord_7249432).sum := by decide
  have hdescent : baseEnd_7249432 < baseStart_7249432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249505 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 10]
def baseStart_7249505 : Nat := 118140960795 + 7249505 * 2 ^ 59
def prefixEnd_7249505 : Nat := 4983230072969 + 3 ^ 40 * 7249505 * 2
def baseEnd_7249505 : Nat := 413608952463640445783071

theorem tailTrace_7249505 : CollatzResearch.WordTrace tailWord_7249505 prefixEnd_7249505 413608952463640445783071 := by
  unfold tailWord_7249505
  simp only [CollatzResearch.WordTrace]
  refine ⟨264411169601288976727589969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176274113067525984485059979 264411169601288976727589969)
  ·
    refine ⟨198308377200966732545692477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264411169601288976727589969 198308377200966732545692477)
    ·
      refine ⟨74365641450362524704634679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198308377200966732545692477 74365641450362524704634679)
      ·
        refine ⟨111548462175543787056952019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74365641450362524704634679 111548462175543787056952019)
        ·
          refine ⟨167322693263315680585428029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111548462175543787056952019 167322693263315680585428029)
          ·
            refine ⟨62746009973743380219535511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167322693263315680585428029 62746009973743380219535511)
            ·
              refine ⟨94119014960615070329303267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62746009973743380219535511 94119014960615070329303267)
              ·
                refine ⟨141178522440922605493954901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94119014960615070329303267 141178522440922605493954901)
                ·
                  refine ⟨413608952463640445783071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 141178522440922605493954901 413608952463640445783071)
                  ·
                    rfl

theorem cell23_7249505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 10].length) (baseStart_7249505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249505 prefixEnd_7249505 := by exact prefixLift 7249505
  have htrace : WordTrace (prefixWord ++ tailWord_7249505) baseStart_7249505 baseEnd_7249505 := by
    simpa [prefixWord, tailWord_7249505, baseEnd_7249505] using wordTrace_append hprefix tailTrace_7249505
  have hstable : (prefixWord ++ tailWord_7249505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249505).length < 2 ^ (prefixWord ++ tailWord_7249505).sum := by decide
  have hdescent : baseEnd_7249505 < baseStart_7249505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249522 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 8]
def baseStart_7249522 : Nat := 118140960795 + 7249522 * 2 ^ 59
def prefixEnd_7249522 : Nat := 4983230072969 + 3 ^ 40 * 7249522 * 2
def baseEnd_7249522 : Nat := 413609922371543382837229

theorem tailTrace_7249522 : CollatzResearch.WordTrace tailWord_7249522 prefixEnd_7249522 413609922371543382837229 := by
  unfold tailWord_7249522
  simp only [CollatzResearch.WordTrace]
  refine ⟨66102947410556847157739705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176274526428151592420639213 66102947410556847157739705)
  ·
    refine ⟨49577210557917635368304779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66102947410556847157739705 49577210557917635368304779)
    ·
      refine ⟨74365815836876453052457169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49577210557917635368304779 74365815836876453052457169)
      ·
        refine ⟨55774361877657339789342877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74365815836876453052457169 55774361877657339789342877)
        ·
          refine ⟨20915385704121502421003579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55774361877657339789342877 20915385704121502421003579)
          ·
            refine ⟨31373078556182253631505369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20915385704121502421003579 31373078556182253631505369)
            ·
              refine ⟨23529808917136690223629027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31373078556182253631505369 23529808917136690223629027)
              ·
                refine ⟨35294713375705035335443541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23529808917136690223629027 35294713375705035335443541)
                ·
                  refine ⟨413609922371543382837229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35294713375705035335443541 413609922371543382837229)
                  ·
                    rfl

theorem cell23_7249522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_7249522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249522 prefixEnd_7249522 := by exact prefixLift 7249522
  have htrace : WordTrace (prefixWord ++ tailWord_7249522) baseStart_7249522 baseEnd_7249522 := by
    simpa [prefixWord, tailWord_7249522, baseEnd_7249522] using wordTrace_append hprefix tailTrace_7249522
  have hstable : (prefixWord ++ tailWord_7249522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249522).length < 2 ^ (prefixWord ++ tailWord_7249522).sum := by decide
  have hdescent : baseEnd_7249522 < baseStart_7249522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249526 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_7249526 : Nat := 118140960795 + 7249526 * 2 ^ 59
def prefixEnd_7249526 : Nat := 4983230072969 + 3 ^ 40 * 7249526 * 2
def baseEnd_7249526 : Nat := 1240830451755502809961681

theorem tailTrace_7249526 : CollatzResearch.WordTrace tailWord_7249526 prefixEnd_7249526 1240830451755502809961681 := by
  unfold tailWord_7249526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16525745970888306082131527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176274623689475264876069621 16525745970888306082131527)
  ·
    refine ⟨24788618956332459123197291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16525745970888306082131527 24788618956332459123197291)
    ·
      refine ⟨37182928434498688684795937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24788618956332459123197291 37182928434498688684795937)
      ·
        refine ⟨27887196325874016513596953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37182928434498688684795937 27887196325874016513596953)
        ·
          refine ⟨20915397244405512385197715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27887196325874016513596953 20915397244405512385197715)
          ·
            refine ⟨31373095866608268577796573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20915397244405512385197715 31373095866608268577796573)
            ·
              refine ⟨11764910949978100716673715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31373095866608268577796573 11764910949978100716673715)
              ·
                refine ⟨17647366424967151075010573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11764910949978100716673715 17647366424967151075010573)
                ·
                  refine ⟨6617762409362681653128965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17647366424967151075010573 6617762409362681653128965)
                  ·
                    refine ⟨1240830451755502809961681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617762409362681653128965 1240830451755502809961681)
                    ·
                      rfl

theorem cell23_7249526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_7249526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249526 prefixEnd_7249526 := by exact prefixLift 7249526
  have htrace : WordTrace (prefixWord ++ tailWord_7249526) baseStart_7249526 baseEnd_7249526 := by
    simpa [prefixWord, tailWord_7249526, baseEnd_7249526] using wordTrace_append hprefix tailTrace_7249526
  have hstable : (prefixWord ++ tailWord_7249526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249526).length < 2 ^ (prefixWord ++ tailWord_7249526).sum := by decide
  have hdescent : baseEnd_7249526 < baseStart_7249526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249592 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_7249592 : Nat := 118140960795 + 7249592 * 2 ^ 59
def prefixEnd_7249592 : Nat := 4983230072969 + 3 ^ 40 * 7249592 * 2
def baseEnd_7249592 : Nat := 3722525244989705171659739

theorem tailTrace_7249592 : CollatzResearch.WordTrace tailWord_7249592 prefixEnd_7249592 3722525244989705171659739 := by
  unfold tailWord_7249592
  simp only [CollatzResearch.WordTrace]
  refine ⟨132207171375986895293003515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176276228501315860390671353 132207171375986895293003515)
  ·
    refine ⟨198310757063980342939505273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132207171375986895293003515 198310757063980342939505273)
    ·
      refine ⟨148733067797985257204628955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198310757063980342939505273 148733067797985257204628955)
      ·
        refine ⟨223099601696977885806943433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148733067797985257204628955 223099601696977885806943433)
        ·
          refine ⟨167324701272733414355207575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223099601696977885806943433 167324701272733414355207575)
          ·
            refine ⟨250987051909100121532811363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167324701272733414355207575 250987051909100121532811363)
            ·
              refine ⟨376480577863650182299217045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250987051909100121532811363 376480577863650182299217045)
              ·
                refine ⟨17647527087358602295275799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 376480577863650182299217045 17647527087358602295275799)
                ·
                  refine ⟨26471290631037903442913699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17647527087358602295275799 26471290631037903442913699)
                  ·
                    refine ⟨39706935946556855164370549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26471290631037903442913699 39706935946556855164370549)
                    ·
                      refine ⟨3722525244989705171659739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39706935946556855164370549 3722525244989705171659739)
                      ·
                        rfl

theorem cell23_7249592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_7249592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249592 prefixEnd_7249592 := by exact prefixLift 7249592
  have htrace : WordTrace (prefixWord ++ tailWord_7249592) baseStart_7249592 baseEnd_7249592 := by
    simpa [prefixWord, tailWord_7249592, baseEnd_7249592] using wordTrace_append hprefix tailTrace_7249592
  have hstable : (prefixWord ++ tailWord_7249592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249592).length < 2 ^ (prefixWord ++ tailWord_7249592).sum := by decide
  have hdescent : baseEnd_7249592 < baseStart_7249592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249599 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 2, 4]
def baseStart_7249599 : Nat := 118140960795 + 7249599 * 2 ^ 59
def prefixEnd_7249599 : Nat := 4983230072969 + 3 ^ 40 * 7249599 * 2
def baseEnd_7249599 : Nat := 1240842946451428881424069

theorem tailTrace_7249599 : CollatzResearch.WordTrace tailWord_7249599 prefixEnd_7249599 1240842946451428881424069 := by
  unfold tailWord_7249599
  simp only [CollatzResearch.WordTrace]
  refine ⟨264414598062948430781511851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176276398708632287187674567 264414598062948430781511851)
  ·
    refine ⟨396621897094422646172267777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264414598062948430781511851 396621897094422646172267777)
    ·
      refine ⟨297466422820816984629200833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396621897094422646172267777 297466422820816984629200833)
      ·
        refine ⟨223099817115612738471900625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297466422820816984629200833 223099817115612738471900625)
        ·
          refine ⟨167324862836709553853925469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223099817115612738471900625 167324862836709553853925469)
          ·
            refine ⟨62746823563766082695222051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167324862836709553853925469 62746823563766082695222051)
            ·
              refine ⟨94120235345649124042833077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62746823563766082695222051 94120235345649124042833077)
              ·
                refine ⟨8823772063654605379015601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94120235345649124042833077 8823772063654605379015601)
                ·
                  refine ⟨6617829047740954034261701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8823772063654605379015601 6617829047740954034261701)
                  ·
                    refine ⟨1240842946451428881424069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617829047740954034261701 1240842946451428881424069)
                    ·
                      rfl

theorem cell23_7249599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 4].length) (baseStart_7249599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249599 prefixEnd_7249599 := by exact prefixLift 7249599
  have htrace : WordTrace (prefixWord ++ tailWord_7249599) baseStart_7249599 baseEnd_7249599 := by
    simpa [prefixWord, tailWord_7249599, baseEnd_7249599] using wordTrace_append hprefix tailTrace_7249599
  have hstable : (prefixWord ++ tailWord_7249599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249599).length < 2 ^ (prefixWord ++ tailWord_7249599).sum := by decide
  have hdescent : baseEnd_7249599 < baseStart_7249599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249610 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2]
def baseStart_7249610 : Nat := 118140960795 + 7249610 * 2 ^ 59
def prefixEnd_7249610 : Nat := 4983230072969 + 3 ^ 40 * 7249610 * 2
def baseEnd_7249610 : Nat := 3722534487641486101234657

theorem tailTrace_7249610 : CollatzResearch.WordTrace tailWord_7249610 prefixEnd_7249610 3722534487641486101234657 := by
  unfold tailWord_7249610
  simp only [CollatzResearch.WordTrace]
  refine ⟨66103749816477144915040571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176276666177272386440108189 66103749816477144915040571)
  ·
    refine ⟨99155624724715717372560857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66103749816477144915040571 99155624724715717372560857)
    ·
      refine ⟨74366718543536788029420643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99155624724715717372560857 74366718543536788029420643)
      ·
        refine ⟨111550077815305182044130965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74366718543536788029420643 111550077815305182044130965)
        ·
          refine ⟨5228909897592430408318639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111550077815305182044130965 5228909897592430408318639)
          ·
            refine ⟨7843364846388645612477959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5228909897592430408318639 7843364846388645612477959)
            ·
              refine ⟨11765047269582968418716939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7843364846388645612477959 11765047269582968418716939)
              ·
                refine ⟨17647570904374452628075409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11765047269582968418716939 17647570904374452628075409)
                ·
                  refine ⟨13235678178280839471056557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17647570904374452628075409 13235678178280839471056557)
                  ·
                    refine ⟨4963379316855314801646209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13235678178280839471056557 4963379316855314801646209)
                    ·
                      refine ⟨3722534487641486101234657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963379316855314801646209 3722534487641486101234657)
                      ·
                        rfl

theorem cell23_7249610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_7249610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249610 prefixEnd_7249610 := by exact prefixLift 7249610
  have htrace : WordTrace (prefixWord ++ tailWord_7249610) baseStart_7249610 baseEnd_7249610 := by
    simpa [prefixWord, tailWord_7249610, baseEnd_7249610] using wordTrace_append hprefix tailTrace_7249610
  have hstable : (prefixWord ++ tailWord_7249610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249610).length < 2 ^ (prefixWord ++ tailWord_7249610).sum := by decide
  have hdescent : baseEnd_7249610 < baseStart_7249610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249626 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3]
def baseStart_7249626 : Nat := 118140960795 + 7249626 * 2 ^ 59
def prefixEnd_7249626 : Nat := 4983230072969 + 3 ^ 40 * 7249626 * 2
def baseEnd_7249626 : Nat := 3722542703331958038634583

theorem tailTrace_7249626 : CollatzResearch.WordTrace tailWord_7249626 prefixEnd_7249626 3722542703331958038634583 := by
  unfold tailWord_7249626
  simp only [CollatzResearch.WordTrace]
  refine ⟨66103895708462653598186183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176277055222567076261829821 66103895708462653598186183)
  ·
    refine ⟨99155843562693980397279275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66103895708462653598186183 99155843562693980397279275)
    ·
      refine ⟨148733765344040970595918913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99155843562693980397279275 148733765344040970595918913)
      ·
        refine ⟨111550324008030727946939185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148733765344040970595918913 111550324008030727946939185)
        ·
          refine ⟨83662743006023045960204389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111550324008030727946939185 83662743006023045960204389)
          ·
            refine ⟨15686764313629321117538323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83662743006023045960204389 15686764313629321117538323)
            ·
              refine ⟨23530146470443981676307485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15686764313629321117538323 23530146470443981676307485)
              ·
                refine ⟨8823804926416493128615307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23530146470443981676307485 8823804926416493128615307)
                ·
                  refine ⟨13235707389624739692922961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8823804926416493128615307 13235707389624739692922961)
                  ·
                    refine ⟨9926780542218554769692221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13235707389624739692922961 9926780542218554769692221)
                    ·
                      refine ⟨3722542703331958038634583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9926780542218554769692221 3722542703331958038634583)
                      ·
                        rfl

theorem cell23_7249626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_7249626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249626 prefixEnd_7249626 := by exact prefixLift 7249626
  have htrace : WordTrace (prefixWord ++ tailWord_7249626) baseStart_7249626 baseEnd_7249626 := by
    simpa [prefixWord, tailWord_7249626, baseEnd_7249626] using wordTrace_append hprefix tailTrace_7249626
  have hstable : (prefixWord ++ tailWord_7249626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249626).length < 2 ^ (prefixWord ++ tailWord_7249626).sum := by decide
  have hdescent : baseEnd_7249626 < baseStart_7249626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249633 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 2, 4]
def baseStart_7249633 : Nat := 118140960795 + 7249633 * 2 ^ 59
def prefixEnd_7249633 : Nat := 4983230072969 + 3 ^ 40 * 7249633 * 2
def baseEnd_7249633 : Nat := 1240848765898846503749017

theorem tailTrace_7249633 : CollatzResearch.WordTrace tailWord_7249633 prefixEnd_7249633 1240848765898846503749017 := by
  unfold tailWord_7249633
  simp only [CollatzResearch.WordTrace]
  refine ⟨264415838144825254588249553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176277225429883503058833035 264415838144825254588249553)
  ·
    refine ⟨198311878608618940941187165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264415838144825254588249553 198311878608618940941187165)
    ·
      refine ⟨74366954478232102852945187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198311878608618940941187165 74366954478232102852945187)
      ·
        refine ⟨111550431717348154279417781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74366954478232102852945187 111550431717348154279417781)
        ·
          refine ⟨10457852973501389463695417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111550431717348154279417781 10457852973501389463695417)
          ·
            refine ⟨7843389730126042097771563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10457852973501389463695417 7843389730126042097771563)
            ·
              refine ⟨11765084595189063146657345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7843389730126042097771563 11765084595189063146657345)
              ·
                refine ⟨8823813446391797359993009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11765084595189063146657345 8823813446391797359993009)
                ·
                  refine ⟨6617860084793848019994757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8823813446391797359993009 6617860084793848019994757)
                  ·
                    refine ⟨1240848765898846503749017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6617860084793848019994757 1240848765898846503749017)
                    ·
                      rfl

theorem cell23_7249633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_7249633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249633 prefixEnd_7249633 := by exact prefixLift 7249633
  have htrace : WordTrace (prefixWord ++ tailWord_7249633) baseStart_7249633 baseEnd_7249633 := by
    simpa [prefixWord, tailWord_7249633, baseEnd_7249633] using wordTrace_append hprefix tailTrace_7249633
  have hstable : (prefixWord ++ tailWord_7249633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249633).length < 2 ^ (prefixWord ++ tailWord_7249633).sum := by decide
  have hdescent : baseEnd_7249633 < baseStart_7249633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249640 : List Nat := [2, 1, 4, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_7249640 : Nat := 118140960795 + 7249640 * 2 ^ 59
def prefixEnd_7249640 : Nat := 4983230072969 + 3 ^ 40 * 7249640 * 2
def baseEnd_7249640 : Nat := 3722549892061120983859519

theorem tailTrace_7249640 : CollatzResearch.WordTrace tailWord_7249640 prefixEnd_7249640 3722549892061120983859519 := by
  unfold tailWord_7249640
  simp only [CollatzResearch.WordTrace]
  refine ⟨132208046727899947391877187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176277395637199929855836249 132208046727899947391877187)
  ·
    refine ⟨198312070091849921087815781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132208046727899947391877187 198312070091849921087815781)
    ·
      refine ⟨37183513142221860203965459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198312070091849921087815781 37183513142221860203965459)
      ·
        refine ⟨55775269713332790305948189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37183513142221860203965459 55775269713332790305948189)
        ·
          refine ⟨20915726142499796364730571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55775269713332790305948189 20915726142499796364730571)
          ·
            refine ⟨31373589213749694547095857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20915726142499796364730571 31373589213749694547095857)
            ·
              refine ⟨23530191910312270910321893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31373589213749694547095857 23530191910312270910321893)
              ·
                refine ⟨4411910983183550795685355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23530191910312270910321893 4411910983183550795685355)
                ·
                  refine ⟨6617866474775326193528033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4411910983183550795685355 6617866474775326193528033)
                  ·
                    refine ⟨4963399856081494645146025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6617866474775326193528033 4963399856081494645146025)
                    ·
                      refine ⟨3722549892061120983859519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963399856081494645146025 3722549892061120983859519)
                      ·
                        rfl

theorem cell23_7249640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_7249640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249640 prefixEnd_7249640 := by exact prefixLift 7249640
  have htrace : WordTrace (prefixWord ++ tailWord_7249640) baseStart_7249640 baseEnd_7249640 := by
    simpa [prefixWord, tailWord_7249640, baseEnd_7249640] using wordTrace_append hprefix tailTrace_7249640
  have hstable : (prefixWord ++ tailWord_7249640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249640).length < 2 ^ (prefixWord ++ tailWord_7249640).sum := by decide
  have hdescent : baseEnd_7249640 < baseStart_7249640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249642 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_7249642 : Nat := 118140960795 + 7249642 * 2 ^ 59
def prefixEnd_7249642 : Nat := 4983230072969 + 3 ^ 40 * 7249642 * 2
def baseEnd_7249642 : Nat := 1240850306340809992011503

theorem tailTrace_7249642 : CollatzResearch.WordTrace tailWord_7249642 prefixEnd_7249642 1240850306340809992011503 := by
  unfold tailWord_7249642
  simp only [CollatzResearch.WordTrace]
  refine ⟨66104041600448162281331795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176277444267861766083551453 66104041600448162281331795)
  ·
    refine ⟨99156062400672243421997693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66104041600448162281331795 99156062400672243421997693)
    ·
      refine ⟨37183523400252091283249135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99156062400672243421997693 37183523400252091283249135)
      ·
        refine ⟨55775285100378136924873703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37183523400252091283249135 55775285100378136924873703)
        ·
          refine ⟨83662927650567205387310555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55775285100378136924873703 83662927650567205387310555)
          ·
            refine ⟨125494391475850808080965833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83662927650567205387310555 125494391475850808080965833)
            ·
              refine ⟨94120793606888106060724375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125494391475850808080965833 94120793606888106060724375)
              ·
                refine ⟨141181190410332159091086563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94120793606888106060724375 141181190410332159091086563)
                ·
                  refine ⟨211771785615498238636629845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141181190410332159091086563 211771785615498238636629845)
                  ·
                    refine ⟨1240850306340809992011503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 211771785615498238636629845 1240850306340809992011503)
                    ·
                      rfl

theorem cell23_7249642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_7249642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249642 prefixEnd_7249642 := by exact prefixLift 7249642
  have htrace : WordTrace (prefixWord ++ tailWord_7249642) baseStart_7249642 baseEnd_7249642 := by
    simpa [prefixWord, tailWord_7249642, baseEnd_7249642] using wordTrace_append hprefix tailTrace_7249642
  have hstable : (prefixWord ++ tailWord_7249642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249642).length < 2 ^ (prefixWord ++ tailWord_7249642).sum := by decide
  have hdescent : baseEnd_7249642 < baseStart_7249642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249677 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7249677 : Nat := 118140960795 + 7249677 * 2 ^ 59
def prefixEnd_7249677 : Nat := 4983230072969 + 3 ^ 40 * 7249677 * 2
def baseEnd_7249677 : Nat := 3722568890845337339096849

theorem tailTrace_7249677 : CollatzResearch.WordTrace tailWord_7249677 prefixEnd_7249677 3722568890845337339096849 := by
  unfold tailWord_7249677
  simp only [CollatzResearch.WordTrace]
  refine ⟨264417442956665850102851285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176278295304443900068567523 264417442956665850102851285)
  ·
    refine ⟨6197283819296855861785577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 264417442956665850102851285 6197283819296855861785577)
    ·
      refine ⟨4647962864472641896339183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6197283819296855861785577 4647962864472641896339183)
      ·
        refine ⟨6971944296708962844508775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4647962864472641896339183 6971944296708962844508775)
        ·
          refine ⟨10457916445063444266763163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6971944296708962844508775 10457916445063444266763163)
          ·
            refine ⟨15686874667595166400144745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10457916445063444266763163 15686874667595166400144745)
            ·
              refine ⟨11765156000696374800108559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15686874667595166400144745 11765156000696374800108559)
              ·
                refine ⟨17647734001044562200162839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11765156000696374800108559 17647734001044562200162839)
                ·
                  refine ⟨26471601001566843300244259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17647734001044562200162839 26471601001566843300244259)
                  ·
                    refine ⟨39707401502350264950366389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26471601001566843300244259 39707401502350264950366389)
                    ·
                      refine ⟨3722568890845337339096849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39707401502350264950366389 3722568890845337339096849)
                      ·
                        rfl

theorem cell23_7249677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7249677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249677 prefixEnd_7249677 := by exact prefixLift 7249677
  have htrace : WordTrace (prefixWord ++ tailWord_7249677) baseStart_7249677 baseEnd_7249677 := by
    simpa [prefixWord, tailWord_7249677, baseEnd_7249677] using wordTrace_append hprefix tailTrace_7249677
  have hstable : (prefixWord ++ tailWord_7249677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249677).length < 2 ^ (prefixWord ++ tailWord_7249677).sum := by decide
  have hdescent : baseEnd_7249677 < baseStart_7249677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249716 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_7249716 : Nat := 118140960795 + 7249716 * 2 ^ 59
def prefixEnd_7249716 : Nat := 4983230072969 + 3 ^ 40 * 7249716 * 2
def baseEnd_7249716 : Nat := 3722588916590862686509169

theorem tailTrace_7249716 : CollatzResearch.WordTrace tailWord_7249716 prefixEnd_7249716 3722588916590862686509169 := by
  unfold tailWord_7249716
  simp only [CollatzResearch.WordTrace]
  refine ⟨132209432701762279881760501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176279243602349706509014001 132209432701762279881760501)
  ·
    refine ⟨12394634315790213738915047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132209432701762279881760501 12394634315790213738915047)
    ·
      refine ⟨18591951473685320608372571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12394634315790213738915047 18591951473685320608372571)
      ·
        refine ⟨27887927210527980912558857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18591951473685320608372571 27887927210527980912558857)
        ·
          refine ⟨20915945407895985684419143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27887927210527980912558857 20915945407895985684419143)
          ·
            refine ⟨31373918111843978526628715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20915945407895985684419143 31373918111843978526628715)
            ·
              refine ⟨47060877167765967789943073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31373918111843978526628715 47060877167765967789943073)
              ·
                refine ⟨35295657875824475842457305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47060877167765967789943073 35295657875824475842457305)
                ·
                  refine ⟨26471743406868356881842979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35295657875824475842457305 26471743406868356881842979)
                  ·
                    refine ⟨39707615110302535322764469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26471743406868356881842979 39707615110302535322764469)
                    ·
                      refine ⟨3722588916590862686509169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39707615110302535322764469 3722588916590862686509169)
                      ·
                        rfl

theorem cell23_7249716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_7249716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249716 prefixEnd_7249716 := by exact prefixLift 7249716
  have htrace : WordTrace (prefixWord ++ tailWord_7249716) baseStart_7249716 baseEnd_7249716 := by
    simpa [prefixWord, tailWord_7249716, baseEnd_7249716] using wordTrace_append hprefix tailTrace_7249716
  have hstable : (prefixWord ++ tailWord_7249716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249716).length < 2 ^ (prefixWord ++ tailWord_7249716).sum := by decide
  have hdescent : baseEnd_7249716 < baseStart_7249716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249717 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_7249717 : Nat := 118140960795 + 7249717 * 2 ^ 59
def prefixEnd_7249717 : Nat := 4983230072969 + 3 ^ 40 * 7249717 * 2
def baseEnd_7249717 : Nat := 3722589430071517182596665

theorem tailTrace_7249717 : CollatzResearch.WordTrace tailWord_7249717 prefixEnd_7249717 3722589430071517182596665 := by
  unfold tailWord_7249717
  simp only [CollatzResearch.WordTrace]
  refine ⟨264418901876520936934307405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176279267917680624622871603 264418901876520936934307405)
  ·
    refine ⟨99157088203695351350365277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264418901876520936934307405 99157088203695351350365277)
    ·
      refine ⟨37183908076385756756386979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99157088203695351350365277 37183908076385756756386979)
      ·
        refine ⟨55775862114578635134580469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37183908076385756756386979 55775862114578635134580469)
        ·
          refine ⟨5228987073241747043866919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55775862114578635134580469 5228987073241747043866919)
          ·
            refine ⟨7843480609862620565800379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5228987073241747043866919 7843480609862620565800379)
            ·
              refine ⟨11765220914793930848700569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7843480609862620565800379 11765220914793930848700569)
              ·
                refine ⟨8823915686095448136525427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11765220914793930848700569 8823915686095448136525427)
                ·
                  refine ⟨13235873529143172204788141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8823915686095448136525427 13235873529143172204788141)
                  ·
                    refine ⟨4963452573428689576795553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13235873529143172204788141 4963452573428689576795553)
                    ·
                      refine ⟨3722589430071517182596665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963452573428689576795553 3722589430071517182596665)
                      ·
                        rfl

theorem cell23_7249717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_7249717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249717 prefixEnd_7249717 := by exact prefixLift 7249717
  have htrace : WordTrace (prefixWord ++ tailWord_7249717) baseStart_7249717 baseEnd_7249717 := by
    simpa [prefixWord, tailWord_7249717, baseEnd_7249717] using wordTrace_append hprefix tailTrace_7249717
  have hstable : (prefixWord ++ tailWord_7249717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249717).length < 2 ^ (prefixWord ++ tailWord_7249717).sum := by decide
  have hdescent : baseEnd_7249717 < baseStart_7249717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249734 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7249734 : Nat := 118140960795 + 7249734 * 2 ^ 59
def prefixEnd_7249734 : Nat := 4983230072969 + 3 ^ 40 * 7249734 * 2
def baseEnd_7249734 : Nat := 3722598159242643616084087

theorem tailTrace_7249734 : CollatzResearch.WordTrace tailWord_7249734 prefixEnd_7249734 3722598159242643616084087 := by
  unfold tailWord_7249734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8263110059920604651177383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176279681278306232558450837 8263110059920604651177383)
  ·
    refine ⟨12394665089880906976766075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8263110059920604651177383 12394665089880906976766075)
    ·
      refine ⟨18591997634821360465149113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12394665089880906976766075 18591997634821360465149113)
      ·
        refine ⟨13943998226116020348861835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18591997634821360465149113 13943998226116020348861835)
        ·
          refine ⟨20915997339174030523292753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13943998226116020348861835 20915997339174030523292753)
          ·
            refine ⟨15686998004380522892469565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20915997339174030523292753 15686998004380522892469565)
            ·
              refine ⟨5882624251642696084676087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15686998004380522892469565 5882624251642696084676087)
              ·
                refine ⟨8823936377464044127014131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5882624251642696084676087 8823936377464044127014131)
                ·
                  refine ⟨13235904566196066190521197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8823936377464044127014131 13235904566196066190521197)
                  ·
                    refine ⟨4963464212323524821445449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13235904566196066190521197 4963464212323524821445449)
                    ·
                      refine ⟨3722598159242643616084087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963464212323524821445449 3722598159242643616084087)
                      ·
                        rfl

theorem cell23_7249734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7249734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249734 prefixEnd_7249734 := by exact prefixLift 7249734
  have htrace : WordTrace (prefixWord ++ tailWord_7249734) baseStart_7249734 baseEnd_7249734 := by
    simpa [prefixWord, tailWord_7249734, baseEnd_7249734] using wordTrace_append hprefix tailTrace_7249734
  have hstable : (prefixWord ++ tailWord_7249734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249734).length < 2 ^ (prefixWord ++ tailWord_7249734).sum := by decide
  have hdescent : baseEnd_7249734 < baseStart_7249734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249759 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 5]
def baseStart_7249759 : Nat := 118140960795 + 7249759 * 2 ^ 59
def prefixEnd_7249759 : Nat := 4983230072969 + 3 ^ 40 * 7249759 * 2
def baseEnd_7249759 : Nat := 3722610996259006018271471

theorem tailTrace_7249759 : CollatzResearch.WordTrace tailWord_7249759 prefixEnd_7249759 3722610996259006018271471 := by
  unfold tailWord_7249759
  simp only [CollatzResearch.WordTrace]
  refine ⟨264420433742368778107336331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176280289161579185404890887 264420433742368778107336331)
  ·
    refine ⟨396630650613553167161004497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264420433742368778107336331 396630650613553167161004497)
    ·
      refine ⟨297472987960164875370753373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396630650613553167161004497 297472987960164875370753373)
      ·
        refine ⟨111552370485061828264032515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297472987960164875370753373 111552370485061828264032515)
        ·
          refine ⟨167328555727592742396048773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111552370485061828264032515 167328555727592742396048773)
          ·
            refine ⟨31374104198923639199259145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167328555727592742396048773 31374104198923639199259145)
            ·
              refine ⟨23530578149192729399444359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31374104198923639199259145 23530578149192729399444359)
              ·
                refine ⟨35295867223789094099166539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23530578149192729399444359 35295867223789094099166539)
                ·
                  refine ⟨52943800835683641148749809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35295867223789094099166539 52943800835683641148749809)
                  ·
                    refine ⟨39707850626762730861562357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52943800835683641148749809 39707850626762730861562357)
                    ·
                      refine ⟨3722610996259006018271471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39707850626762730861562357 3722610996259006018271471)
                      ·
                        rfl

theorem cell23_7249759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_7249759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249759 prefixEnd_7249759 := by exact prefixLift 7249759
  have htrace : WordTrace (prefixWord ++ tailWord_7249759) baseStart_7249759 baseEnd_7249759 := by
    simpa [prefixWord, tailWord_7249759, baseEnd_7249759] using wordTrace_append hprefix tailTrace_7249759
  have hstable : (prefixWord ++ tailWord_7249759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249759).length < 2 ^ (prefixWord ++ tailWord_7249759).sum := by decide
  have hdescent : baseEnd_7249759 < baseStart_7249759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249769 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 4]
def baseStart_7249769 : Nat := 118140960795 + 7249769 * 2 ^ 59
def prefixEnd_7249769 : Nat := 4983230072969 + 3 ^ 40 * 7249769 * 2
def baseEnd_7249769 : Nat := 3722616131065550979146425

theorem tailTrace_7249769 : CollatzResearch.WordTrace tailWord_7249769 prefixEnd_7249769 3722616131065550979146425 := by
  unfold tailWord_7249769
  simp only [CollatzResearch.WordTrace]
  refine ⟨264420798472332549815200361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176280532314888366543466907 264420798472332549815200361)
  ·
    refine ⟨198315598854249412361400271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264420798472332549815200361 198315598854249412361400271)
    ·
      refine ⟨297473398281374118542100407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198315598854249412361400271 297473398281374118542100407)
      ·
        refine ⟨446210097422061177813150611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297473398281374118542100407 446210097422061177813150611)
        ·
          refine ⟨669315146133091766719725917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446210097422061177813150611 669315146133091766719725917)
          ·
            refine ⟨250993179799909412519897219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 669315146133091766719725917 250993179799909412519897219)
            ·
              refine ⟨376489769699864118779845829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250993179799909412519897219 376489769699864118779845829)
              ·
                refine ⟨70591831818724522271221093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376489769699864118779845829 70591831818724522271221093)
                ·
                  refine ⟨13235968466010847925853955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70591831818724522271221093 13235968466010847925853955)
                  ·
                    refine ⟨19853952699016271888780933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13235968466010847925853955 19853952699016271888780933)
                    ·
                      refine ⟨3722616131065550979146425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19853952699016271888780933 3722616131065550979146425)
                      ·
                        rfl

theorem cell23_7249769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_7249769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249769 prefixEnd_7249769 := by exact prefixLift 7249769
  have htrace : WordTrace (prefixWord ++ tailWord_7249769) baseStart_7249769 baseEnd_7249769 := by
    simpa [prefixWord, tailWord_7249769, baseEnd_7249769] using wordTrace_append hprefix tailTrace_7249769
  have hstable : (prefixWord ++ tailWord_7249769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249769).length < 2 ^ (prefixWord ++ tailWord_7249769).sum := by decide
  have hdescent : baseEnd_7249769 < baseStart_7249769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249786 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4]
def baseStart_7249786 : Nat := 118140960795 + 7249786 * 2 ^ 59
def prefixEnd_7249786 : Nat := 4983230072969 + 3 ^ 40 * 7249786 * 2
def baseEnd_7249786 : Nat := 3722624860236677412633847

theorem tailTrace_7249786 : CollatzResearch.WordTrace tailWord_7249786 prefixEnd_7249786 3722624860236677412633847 := by
  unfold tailWord_7249786
  simp only [CollatzResearch.WordTrace]
  refine ⟨66105354628317740429642303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176280945675513974479046141 66105354628317740429642303)
  ·
    refine ⟨99158031942476610644463455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66105354628317740429642303 99158031942476610644463455)
    ·
      refine ⟨148737047913714915966695183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99158031942476610644463455 148737047913714915966695183)
      ·
        refine ⟨223105571870572373950042775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148737047913714915966695183 223105571870572373950042775)
        ·
          refine ⟨334658357805858560925064163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223105571870572373950042775 334658357805858560925064163)
          ·
            refine ⟨501987536708787841387596245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334658357805858560925064163 501987536708787841387596245)
            ·
              refine ⟨11765332891612215032521787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 501987536708787841387596245 11765332891612215032521787)
              ·
                refine ⟨17647999337418322548782681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11765332891612215032521787 17647999337418322548782681)
                ·
                  refine ⟨13235999503063741911587011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17647999337418322548782681 13235999503063741911587011)
                  ·
                    refine ⟨19853999254595612867380517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13235999503063741911587011 19853999254595612867380517)
                    ·
                      refine ⟨3722624860236677412633847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19853999254595612867380517 3722624860236677412633847)
                      ·
                        rfl

theorem cell23_7249786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_7249786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249786 prefixEnd_7249786 := by exact prefixLift 7249786
  have htrace : WordTrace (prefixWord ++ tailWord_7249786) baseStart_7249786 baseEnd_7249786 := by
    simpa [prefixWord, tailWord_7249786, baseEnd_7249786] using wordTrace_append hprefix tailTrace_7249786
  have hstable : (prefixWord ++ tailWord_7249786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249786).length < 2 ^ (prefixWord ++ tailWord_7249786).sum := by decide
  have hdescent : baseEnd_7249786 < baseStart_7249786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249813 : List Nat := [1, 3, 2, 1, 1, 3, 1, 6, 1, 4]
def baseStart_7249813 : Nat := 118140960795 + 7249813 * 2 ^ 59
def prefixEnd_7249813 : Nat := 4983230072969 + 3 ^ 40 * 7249813 * 2
def baseEnd_7249813 : Nat := 1240879574738116268998741

theorem tailTrace_7249813 : CollatzResearch.WordTrace tailWord_7249813 prefixEnd_7249813 1240879574738116268998741 := by
  unfold tailWord_7249813
  simp only [CollatzResearch.WordTrace]
  refine ⟨264422403284173145329802093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176281602189448763553201395 264422403284173145329802093)
  ·
    refine ⟨99158401231564929498675785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264422403284173145329802093 99158401231564929498675785)
    ·
      refine ⟨74368800923673697124006839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99158401231564929498675785 74368800923673697124006839)
      ·
        refine ⟨111553201385510545686010259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74368800923673697124006839 111553201385510545686010259)
        ·
          refine ⟨167329802078265818529015389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111553201385510545686010259 167329802078265818529015389)
          ·
            refine ⟨62748675779349681948380771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167329802078265818529015389 62748675779349681948380771)
            ·
              refine ⟨94123013669024522922571157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62748675779349681948380771 94123013669024522922571157)
              ·
                refine ⟨4412016265735524511995523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94123013669024522922571157 4412016265735524511995523)
                ·
                  refine ⟨6618024398603286767993285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4412016265735524511995523 6618024398603286767993285)
                  ·
                    refine ⟨1240879574738116268998741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6618024398603286767993285 1240879574738116268998741)
                    ·
                      rfl

theorem cell23_7249813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_7249813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249813 prefixEnd_7249813 := by exact prefixLift 7249813
  have htrace : WordTrace (prefixWord ++ tailWord_7249813) baseStart_7249813 baseEnd_7249813 := by
    simpa [prefixWord, tailWord_7249813, baseEnd_7249813] using wordTrace_append hprefix tailTrace_7249813
  have hstable : (prefixWord ++ tailWord_7249813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249813).length < 2 ^ (prefixWord ++ tailWord_7249813).sum := by decide
  have hdescent : baseEnd_7249813 < baseStart_7249813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249856 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 1, 5]
def baseStart_7249856 : Nat := 118140960795 + 7249856 * 2 ^ 59
def prefixEnd_7249856 : Nat := 4983230072969 + 3 ^ 40 * 7249856 * 2
def baseEnd_7249856 : Nat := 1240886934627497379586175

theorem tailTrace_7249856 : CollatzResearch.WordTrace tailWord_7249856 prefixEnd_7249856 1240886934627497379586175 := by
  unfold tailWord_7249856
  simp only [CollatzResearch.WordTrace]
  refine ⟨132211985811508681836808711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176282647748678242449078281 132211985811508681836808711)
  ·
    refine ⟨198317978717263022755213067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132211985811508681836808711 198317978717263022755213067)
    ·
      refine ⟨297476968075894534132819601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198317978717263022755213067 297476968075894534132819601)
      ·
        refine ⟨223107726056920900599614701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297476968075894534132819601 223107726056920900599614701)
        ·
          refine ⟨83665397271345337724855513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223107726056920900599614701 83665397271345337724855513)
          ·
            refine ⟨62749047953509003293641635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83665397271345337724855513 62749047953509003293641635)
            ·
              refine ⟨94123571930263504940462453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62749047953509003293641635 94123571930263504940462453)
              ·
                refine ⟨8824084868462203588168355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94123571930263504940462453 8824084868462203588168355)
                ·
                  refine ⟨13236127302693305382252533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8824084868462203588168355 13236127302693305382252533)
                  ·
                    refine ⟨1240886934627497379586175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13236127302693305382252533 1240886934627497379586175)
                    ·
                      rfl

theorem cell23_7249856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 5].length) (baseStart_7249856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249856 prefixEnd_7249856 := by exact prefixLift 7249856
  have htrace : WordTrace (prefixWord ++ tailWord_7249856) baseStart_7249856 baseEnd_7249856 := by
    simpa [prefixWord, tailWord_7249856, baseEnd_7249856] using wordTrace_append hprefix tailTrace_7249856
  have hstable : (prefixWord ++ tailWord_7249856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249856).length < 2 ^ (prefixWord ++ tailWord_7249856).sum := by decide
  have hdescent : baseEnd_7249856 < baseStart_7249856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249890 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7249890 : Nat := 118140960795 + 7249890 * 2 ^ 59
def prefixEnd_7249890 : Nat := 4983230072969 + 3 ^ 40 * 7249890 * 2
def baseEnd_7249890 : Nat := 1240892754074915001911123

theorem tailTrace_7249890 : CollatzResearch.WordTrace tailWord_7249890 prefixEnd_7249890 1240892754074915001911123 := by
  unfold tailWord_7249890
  simp only [CollatzResearch.WordTrace]
  refine ⟨66106302926223546870088781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176283474469929458320236749 66106302926223546870088781)
  ·
    refine ⟨24789863597333830076283293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66106302926223546870088781 24789863597333830076283293)
    ·
      refine ⟨9296198849000186278606235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24789863597333830076283293 9296198849000186278606235)
      ·
        refine ⟨13944298273500279417909353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9296198849000186278606235 13944298273500279417909353)
        ·
          refine ⟨10458223705125209563432015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13944298273500279417909353 10458223705125209563432015)
          ·
            refine ⟨15687335557687814345148023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10458223705125209563432015 15687335557687814345148023)
            ·
              refine ⟨23531003336531721517722035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15687335557687814345148023 23531003336531721517722035)
              ·
                refine ⟨35296505004797582276583053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23531003336531721517722035 35296505004797582276583053)
                ·
                  refine ⟨13236189376799093353718645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35296505004797582276583053 13236189376799093353718645)
                  ·
                    refine ⟨1240892754074915001911123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13236189376799093353718645 1240892754074915001911123)
                    ·
                      rfl

theorem cell23_7249890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7249890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249890 prefixEnd_7249890 := by exact prefixLift 7249890
  have htrace : WordTrace (prefixWord ++ tailWord_7249890) baseStart_7249890 baseEnd_7249890 := by
    simpa [prefixWord, tailWord_7249890, baseEnd_7249890] using wordTrace_append hprefix tailTrace_7249890
  have hstable : (prefixWord ++ tailWord_7249890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249890).length < 2 ^ (prefixWord ++ tailWord_7249890).sum := by decide
  have hdescent : baseEnd_7249890 < baseStart_7249890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249913 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 5]
def baseStart_7249913 : Nat := 118140960795 + 7249913 * 2 ^ 59
def prefixEnd_7249913 : Nat := 4983230072969 + 3 ^ 40 * 7249913 * 2
def baseEnd_7249913 : Nat := 3722690072279798415745763

theorem tailTrace_7249913 : CollatzResearch.WordTrace tailWord_7249913 prefixEnd_7249913 3722690072279798415745763 := by
  unfold tailWord_7249913
  simp only [CollatzResearch.WordTrace]
  refine ⟨264426050583810862408442393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176284033722540574938961595 264426050583810862408442393)
  ·
    refine ⟨198319537937858146806331795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264426050583810862408442393 198319537937858146806331795)
    ·
      refine ⟨297479306906787220209497693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198319537937858146806331795 297479306906787220209497693)
      ·
        refine ⟨111554740090045207578561635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297479306906787220209497693 111554740090045207578561635)
        ·
          refine ⟨167332110135067811367842453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111554740090045207578561635 167332110135067811367842453)
          ·
            refine ⟨7843692662581303657867615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167332110135067811367842453 7843692662581303657867615)
            ·
              refine ⟨11765538993871955486801423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7843692662581303657867615 11765538993871955486801423)
              ·
                refine ⟨17648308490807933230202135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11765538993871955486801423 17648308490807933230202135)
                ·
                  refine ⟨26472462736211899845303203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17648308490807933230202135 26472462736211899845303203)
                  ·
                    refine ⟨39708694104317849767954805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26472462736211899845303203 39708694104317849767954805)
                    ·
                      refine ⟨3722690072279798415745763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39708694104317849767954805 3722690072279798415745763)
                      ·
                        rfl

theorem cell23_7249913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_7249913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249913 prefixEnd_7249913 := by exact prefixLift 7249913
  have htrace : WordTrace (prefixWord ++ tailWord_7249913) baseStart_7249913 baseEnd_7249913 := by
    simpa [prefixWord, tailWord_7249913, baseEnd_7249913] using wordTrace_append hprefix tailTrace_7249913
  have hstable : (prefixWord ++ tailWord_7249913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249913).length < 2 ^ (prefixWord ++ tailWord_7249913).sum := by decide
  have hdescent : baseEnd_7249913 < baseStart_7249913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249983 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 3, 4, 2]
def baseStart_7249983 : Nat := 118140960795 + 7249983 * 2 ^ 59
def prefixEnd_7249983 : Nat := 4983230072969 + 3 ^ 40 * 7249983 * 2
def baseEnd_7249983 : Nat := 3722726015925613141870441

theorem tailTrace_7249983 : CollatzResearch.WordTrace tailWord_7249983 prefixEnd_7249983 3722726015925613141870441 := by
  unfold tailWord_7249983
  simp only [CollatzResearch.WordTrace]
  refine ⟨264428603693557264363490603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176285735795704842908993735 264428603693557264363490603)
  ·
    refine ⟨396642905540335896545235905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264428603693557264363490603 396642905540335896545235905)
    ·
      refine ⟨297482179155251922408926929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396642905540335896545235905 297482179155251922408926929)
      ·
        refine ⟨223111634366438941806695197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297482179155251922408926929 223111634366438941806695197)
        ·
          refine ⟨83666862887414603177510699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223111634366438941806695197 83666862887414603177510699)
          ·
            refine ⟨125500294331121904766266049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83666862887414603177510699 125500294331121904766266049)
            ·
              refine ⟨94125220748341428574699537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125500294331121904766266049 94125220748341428574699537)
              ·
                refine ⟨70593915561256071431024653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94125220748341428574699537 70593915561256071431024653)
                ·
                  refine ⟨26472718335471026786634245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70593915561256071431024653 26472718335471026786634245)
                  ·
                    refine ⟨4963634687900817522493921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26472718335471026786634245 4963634687900817522493921)
                    ·
                      refine ⟨3722726015925613141870441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963634687900817522493921 3722726015925613141870441)
                      ·
                        rfl

theorem cell23_7249983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 4, 2].length) (baseStart_7249983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7249983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7249983 prefixEnd_7249983 := by exact prefixLift 7249983
  have htrace : WordTrace (prefixWord ++ tailWord_7249983) baseStart_7249983 baseEnd_7249983 := by
    simpa [prefixWord, tailWord_7249983, baseEnd_7249983] using wordTrace_append hprefix tailTrace_7249983
  have hstable : (prefixWord ++ tailWord_7249983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249983).length < 2 ^ (prefixWord ++ tailWord_7249983).sum := by decide
  have hdescent : baseEnd_7249983 < baseStart_7249983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250124 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7250124 : Nat := 118140960795 + 7250124 * 2 ^ 59
def prefixEnd_7250124 : Nat := 4983230072969 + 3 ^ 40 * 7250124 * 2
def baseEnd_7250124 : Nat := 3722798416697897090207293

theorem tailTrace_7250124 : CollatzResearch.WordTrace tailWord_7250124 prefixEnd_7250124 3722798416697897090207293 := by
  unfold tailWord_7250124
  simp only [CollatzResearch.WordTrace]
  refine ⟨132216873193023222722186713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176289164257364296962915617 132216873193023222722186713)
  ·
    refine ⟨99162654894767417041640035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132216873193023222722186713 99162654894767417041640035)
    ·
      refine ⟨148743982342151125562460053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99162654894767417041640035 148743982342151125562460053)
      ·
        refine ⟨6972374172288334010740315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148743982342151125562460053 6972374172288334010740315)
        ·
          refine ⟨10458561258432501016110473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972374172288334010740315 10458561258432501016110473)
          ·
            refine ⟨7843920943824375762082855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10458561258432501016110473 7843920943824375762082855)
            ·
              refine ⟨11765881415736563643124283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7843920943824375762082855 11765881415736563643124283)
              ·
                refine ⟨17648822123604845464686425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11765881415736563643124283 17648822123604845464686425)
                ·
                  refine ⟨13236616592703634098514819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17648822123604845464686425 13236616592703634098514819)
                  ·
                    refine ⟨19854924889055451147772229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13236616592703634098514819 19854924889055451147772229)
                    ·
                      refine ⟨3722798416697897090207293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19854924889055451147772229 3722798416697897090207293)
                      ·
                        rfl

theorem cell23_7250124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7250124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250124 prefixEnd_7250124 := by exact prefixLift 7250124
  have htrace : WordTrace (prefixWord ++ tailWord_7250124) baseStart_7250124 baseEnd_7250124 := by
    simpa [prefixWord, tailWord_7250124, baseEnd_7250124] using wordTrace_append hprefix tailTrace_7250124
  have hstable : (prefixWord ++ tailWord_7250124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250124).length < 2 ^ (prefixWord ++ tailWord_7250124).sum := by decide
  have hdescent : baseEnd_7250124 < baseStart_7250124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250190 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_7250190 : Nat := 118140960795 + 7250190 * 2 ^ 59
def prefixEnd_7250190 : Nat := 4983230072969 + 3 ^ 40 * 7250190 * 2
def baseEnd_7250190 : Nat := 1240944102140364610660663

theorem tailTrace_7250190 : CollatzResearch.WordTrace tailWord_7250190 prefixEnd_7250190 1240944102140364610660663 := by
  unfold tailWord_7250190
  simp only [CollatzResearch.WordTrace]
  refine ⟨33054519200475917339534503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176290769069204892477517349 33054519200475917339534503)
  ·
    refine ⟨49581778800713876009301755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33054519200475917339534503 49581778800713876009301755)
    ·
      refine ⟨74372668201070814013952633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49581778800713876009301755 74372668201070814013952633)
      ·
        refine ⟨55779501150803110510464475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74372668201070814013952633 55779501150803110510464475)
        ·
          refine ⟨83669251726204665765696713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55779501150803110510464475 83669251726204665765696713)
          ·
            refine ⟨62751938794653499324272535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83669251726204665765696713 62751938794653499324272535)
            ·
              refine ⟨94127908191980248986408803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62751938794653499324272535 94127908191980248986408803)
              ·
                refine ⟨141191862287970373479613205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94127908191980248986408803 141191862287970373479613205)
                ·
                  refine ⟨6618368544748611256856869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141191862287970373479613205 6618368544748611256856869)
                  ·
                    refine ⟨1240944102140364610660663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6618368544748611256856869 1240944102140364610660663)
                    ·
                      rfl

theorem cell23_7250190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_7250190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250190 prefixEnd_7250190 := by exact prefixLift 7250190
  have htrace : WordTrace (prefixWord ++ tailWord_7250190) baseStart_7250190 baseEnd_7250190 := by
    simpa [prefixWord, tailWord_7250190, baseEnd_7250190] using wordTrace_append hprefix tailTrace_7250190
  have hstable : (prefixWord ++ tailWord_7250190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250190).length < 2 ^ (prefixWord ++ tailWord_7250190).sum := by decide
  have hdescent : baseEnd_7250190 < baseStart_7250190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250197 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 5, 2, 2]
def baseStart_7250197 : Nat := 118140960795 + 7250197 * 2 ^ 59
def prefixEnd_7250197 : Nat := 4983230072969 + 3 ^ 40 * 7250197 * 2
def baseEnd_7250197 : Nat := 3722835900785675304594457

theorem tailTrace_7250197 : CollatzResearch.WordTrace tailWord_7250197 prefixEnd_7250197 3722835900785675304594457 := by
  unfold tailWord_7250197
  simp only [CollatzResearch.WordTrace]
  refine ⟨264436408914781978911780845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176290939276521319274520563 264436408914781978911780845)
  ·
    refine ⟨99163653343043242091917817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264436408914781978911780845 99163653343043242091917817)
    ·
      refine ⟨74372740007282431568938363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99163653343043242091917817 74372740007282431568938363)
      ·
        refine ⟨111559110010923647353407545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74372740007282431568938363 111559110010923647353407545)
        ·
          refine ⟨83669332508192735515055659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111559110010923647353407545 83669332508192735515055659)
          ·
            refine ⟨125503998762289103272583489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83669332508192735515055659 125503998762289103272583489)
            ·
              refine ⟨94127999071716827454437617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125503998762289103272583489 94127999071716827454437617)
              ·
                refine ⟨70595999303787620590828213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94127999071716827454437617 70595999303787620590828213)
                ·
                  refine ⟨6618374934730089430390145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70595999303787620590828213 6618374934730089430390145)
                  ·
                    refine ⟨4963781201047567072792609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6618374934730089430390145 4963781201047567072792609)
                    ·
                      refine ⟨3722835900785675304594457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963781201047567072792609 3722835900785675304594457)
                      ·
                        rfl

theorem cell23_7250197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_7250197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250197 prefixEnd_7250197 := by exact prefixLift 7250197
  have htrace : WordTrace (prefixWord ++ tailWord_7250197) baseStart_7250197 baseEnd_7250197 := by
    simpa [prefixWord, tailWord_7250197, baseEnd_7250197] using wordTrace_append hprefix tailTrace_7250197
  have hstable : (prefixWord ++ tailWord_7250197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250197).length < 2 ^ (prefixWord ++ tailWord_7250197).sum := by decide
  have hdescent : baseEnd_7250197 < baseStart_7250197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250200 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 1, 1, 5]
def baseStart_7250200 : Nat := 118140960795 + 7250200 * 2 ^ 59
def prefixEnd_7250200 : Nat := 4983230072969 + 3 ^ 40 * 7250200 * 2
def baseEnd_7250200 : Nat := 3722837441227638792856943

theorem tailTrace_7250200 : CollatzResearch.WordTrace tailWord_7250200 prefixEnd_7250200 3722837441227638792856943 := by
  unfold tailWord_7250200
  simp only [CollatzResearch.WordTrace]
  refine ⟨132218259166885555212070027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176291012222514073616093369 132218259166885555212070027)
  ·
    refine ⟨198327388750328332818105041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132218259166885555212070027 198327388750328332818105041)
    ·
      refine ⟨148745541562746249613578781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198327388750328332818105041 148745541562746249613578781)
      ·
        refine ⟨55779578086029843605092043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148745541562746249613578781 55779578086029843605092043)
        ·
          refine ⟨83669367129044765407638065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55779578086029843605092043 83669367129044765407638065)
          ·
            refine ⟨62752025346783574055728549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83669367129044765407638065 62752025346783574055728549)
            ·
              refine ⟨11766004752521920135449103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62752025346783574055728549 11766004752521920135449103)
              ·
                refine ⟨17649007128782880203173655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11766004752521920135449103 17649007128782880203173655)
                ·
                  refine ⟨26473510693174320304760483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17649007128782880203173655 26473510693174320304760483)
                  ·
                    refine ⟨39710266039761480457140725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26473510693174320304760483 39710266039761480457140725)
                    ·
                      refine ⟨3722837441227638792856943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39710266039761480457140725 3722837441227638792856943)
                      ·
                        rfl

theorem cell23_7250200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_7250200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250200 prefixEnd_7250200 := by exact prefixLift 7250200
  have htrace : WordTrace (prefixWord ++ tailWord_7250200) baseStart_7250200 baseEnd_7250200 := by
    simpa [prefixWord, tailWord_7250200, baseEnd_7250200] using wordTrace_append hprefix tailTrace_7250200
  have hstable : (prefixWord ++ tailWord_7250200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250200).length < 2 ^ (prefixWord ++ tailWord_7250200).sum := by decide
  have hdescent : baseEnd_7250200 < baseStart_7250200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250210 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_7250210 : Nat := 118140960795 + 7250210 * 2 ^ 59
def prefixEnd_7250210 : Nat := 4983230072969 + 3 ^ 40 * 7250210 * 2
def baseEnd_7250210 : Nat := 3722842576034183753731897

theorem tailTrace_7250210 : CollatzResearch.WordTrace tailWord_7250210 prefixEnd_7250210 3722842576034183753731897 := by
  unfold tailWord_7250210
  simp only [CollatzResearch.WordTrace]
  refine ⟨66109220765933720533001021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176291255375823254754669389 66109220765933720533001021)
  ·
    refine ⟨24790957787225145199875383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66109220765933720533001021 24790957787225145199875383)
    ·
      refine ⟨37186436680837717799813075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24790957787225145199875383 37186436680837717799813075)
      ·
        refine ⟨55779655021256576699719613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37186436680837717799813075 55779655021256576699719613)
        ·
          refine ⟨20917370632971216262394855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55779655021256576699719613 20917370632971216262394855)
          ·
            refine ⟨31376055949456824393592283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20917370632971216262394855 31376055949456824393592283)
            ·
              refine ⟨47064083924185236590388425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31376055949456824393592283 47064083924185236590388425)
              ·
                refine ⟨35298062943138927442791319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47064083924185236590388425 35298062943138927442791319)
                ·
                  refine ⟨52947094414708391164186979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35298062943138927442791319 52947094414708391164186979)
                  ·
                    refine ⟨79420641622062586746280469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52947094414708391164186979 79420641622062586746280469)
                    ·
                      refine ⟨3722842576034183753731897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79420641622062586746280469 3722842576034183753731897)
                      ·
                        rfl

theorem cell23_7250210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_7250210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250210 prefixEnd_7250210 := by exact prefixLift 7250210
  have htrace : WordTrace (prefixWord ++ tailWord_7250210) baseStart_7250210 baseEnd_7250210 := by
    simpa [prefixWord, tailWord_7250210, baseEnd_7250210] using wordTrace_append hprefix tailTrace_7250210
  have hstable : (prefixWord ++ tailWord_7250210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250210).length < 2 ^ (prefixWord ++ tailWord_7250210).sum := by decide
  have hdescent : baseEnd_7250210 < baseStart_7250210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250234 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3]
def baseStart_7250234 : Nat := 118140960795 + 7250234 * 2 ^ 59
def prefixEnd_7250234 : Nat := 4983230072969 + 3 ^ 40 * 7250234 * 2
def baseEnd_7250234 : Nat := 3722854899569891659831787

theorem tailTrace_7250234 : CollatzResearch.WordTrace tailWord_7250234 prefixEnd_7250234 3722854899569891659831787 := by
  unfold tailWord_7250234
  simp only [CollatzResearch.WordTrace]
  refine ⟨66109439603911983557719439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176291838943765289487251837 66109439603911983557719439)
  ·
    refine ⟨99164159405867975336579159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66109439603911983557719439 99164159405867975336579159)
    ·
      refine ⟨148746239108801963004868739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99164159405867975336579159 148746239108801963004868739)
      ·
        refine ⟨223119358663202944507303109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148746239108801963004868739 223119358663202944507303109)
        ·
          refine ⟨41834879749350552095119333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223119358663202944507303109 41834879749350552095119333)
          ·
            refine ⟨7844039953003228517834875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41834879749350552095119333 7844039953003228517834875)
            ·
              refine ⟨11766059929504842776752313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7844039953003228517834875 11766059929504842776752313)
              ·
                refine ⟨8824544947128632082564235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11766059929504842776752313 8824544947128632082564235)
                ·
                  refine ⟨13236817420692948123846353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8824544947128632082564235 13236817420692948123846353)
                  ·
                    refine ⟨9927613065519711092884765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13236817420692948123846353 9927613065519711092884765)
                    ·
                      refine ⟨3722854899569891659831787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9927613065519711092884765 3722854899569891659831787)
                      ·
                        rfl

theorem cell23_7250234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_7250234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250234 prefixEnd_7250234 := by exact prefixLift 7250234
  have htrace : WordTrace (prefixWord ++ tailWord_7250234) baseStart_7250234 baseEnd_7250234 := by
    simpa [prefixWord, tailWord_7250234, baseEnd_7250234] using wordTrace_append hprefix tailTrace_7250234
  have hstable : (prefixWord ++ tailWord_7250234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250234).length < 2 ^ (prefixWord ++ tailWord_7250234).sum := by decide
  have hdescent : baseEnd_7250234 < baseStart_7250234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250243 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 5]
def baseStart_7250243 : Nat := 118140960795 + 7250243 * 2 ^ 59
def prefixEnd_7250243 : Nat := 4983230072969 + 3 ^ 40 * 7250243 * 2
def baseEnd_7250243 : Nat := 3722859520895782124619245

theorem tailTrace_7250243 : CollatzResearch.WordTrace tailWord_7250243 prefixEnd_7250243 3722859520895782124619245 := by
  unfold tailWord_7250243
  simp only [CollatzResearch.WordTrace]
  refine ⟨264438086672615328767955383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176292057781743552511970255 264438086672615328767955383)
  ·
    refine ⟨396657130008922993151933075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264438086672615328767955383 396657130008922993151933075)
    ·
      refine ⟨594985695013384489727899613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396657130008922993151933075 594985695013384489727899613)
      ·
        refine ⟨223119635630019183647962355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594985695013384489727899613 223119635630019183647962355)
        ·
          refine ⟨334679453445028775471943533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223119635630019183647962355 334679453445028775471943533)
          ·
            refine ⟨125504795041885790801978825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334679453445028775471943533 125504795041885790801978825)
            ·
              refine ⟨94128596281414343101484119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125504795041885790801978825 94128596281414343101484119)
              ·
                refine ⟨141192894422121514652226179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94128596281414343101484119 141192894422121514652226179)
                ·
                  refine ⟨211789341633182271978339269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141192894422121514652226179 211789341633182271978339269)
                  ·
                    refine ⟨39710501556221675995938613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 211789341633182271978339269 39710501556221675995938613)
                    ·
                      refine ⟨3722859520895782124619245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39710501556221675995938613 3722859520895782124619245)
                      ·
                        rfl

theorem cell23_7250243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_7250243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250243 prefixEnd_7250243 := by exact prefixLift 7250243
  have htrace : WordTrace (prefixWord ++ tailWord_7250243) baseStart_7250243 baseEnd_7250243 := by
    simpa [prefixWord, tailWord_7250243, baseEnd_7250243] using wordTrace_append hprefix tailTrace_7250243
  have hstable : (prefixWord ++ tailWord_7250243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250243).length < 2 ^ (prefixWord ++ tailWord_7250243).sum := by decide
  have hdescent : baseEnd_7250243 < baseStart_7250243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250244 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_7250244 : Nat := 118140960795 + 7250244 * 2 ^ 59
def prefixEnd_7250244 : Nat := 4983230072969 + 3 ^ 40 * 7250244 * 2
def baseEnd_7250244 : Nat := 3722860034376436620706741

theorem tailTrace_7250244 : CollatzResearch.WordTrace tailWord_7250244 prefixEnd_7250244 3722860034376436620706741 := by
  unfold tailWord_7250244
  simp only [CollatzResearch.WordTrace]
  refine ⟨132219061572805852969370893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176292082097074470625827857 132219061572805852969370893)
  ·
    refine ⟨49582148089802194863514085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132219061572805852969370893 49582148089802194863514085)
    ·
      refine ⟨9296652766837911536908891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49582148089802194863514085 9296652766837911536908891)
      ·
        refine ⟨13944979150256867305363337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9296652766837911536908891 13944979150256867305363337)
        ·
          refine ⟨10458734362692650479022503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13944979150256867305363337 10458734362692650479022503)
          ·
            refine ⟨15688101544038975718533755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10458734362692650479022503 15688101544038975718533755)
            ·
              refine ⟨23532152316058463577800633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15688101544038975718533755 23532152316058463577800633)
              ·
                refine ⟨17649114237043847683350475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23532152316058463577800633 17649114237043847683350475)
                ·
                  refine ⟨26473671355565771525025713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17649114237043847683350475 26473671355565771525025713)
                  ·
                    refine ⟨19855253516674328643769285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26473671355565771525025713 19855253516674328643769285)
                    ·
                      refine ⟨3722860034376436620706741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19855253516674328643769285 3722860034376436620706741)
                      ·
                        rfl

theorem cell23_7250244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_7250244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250244 prefixEnd_7250244 := by exact prefixLift 7250244
  have htrace : WordTrace (prefixWord ++ tailWord_7250244) baseStart_7250244 baseEnd_7250244 := by
    simpa [prefixWord, tailWord_7250244, baseEnd_7250244] using wordTrace_append hprefix tailTrace_7250244
  have hstable : (prefixWord ++ tailWord_7250244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250244).length < 2 ^ (prefixWord ++ tailWord_7250244).sum := by decide
  have hdescent : baseEnd_7250244 < baseStart_7250244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250274 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_7250274 : Nat := 118140960795 + 7250274 * 2 ^ 59
def prefixEnd_7250274 : Nat := 4983230072969 + 3 ^ 40 * 7250274 * 2
def baseEnd_7250274 : Nat := 3722875438796071503331603

theorem tailTrace_7250274 : CollatzResearch.WordTrace tailWord_7250274 prefixEnd_7250274 3722875438796071503331603 := by
  unfold tailWord_7250274
  simp only [CollatzResearch.WordTrace]
  refine ⟨66109804333875755265583469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176292811557002014041555917 66109804333875755265583469)
  ·
    refine ⟨24791176625203408224593801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66109804333875755265583469 24791176625203408224593801)
    ·
      refine ⟨18593382468902556168445351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24791176625203408224593801 18593382468902556168445351)
      ·
        refine ⟨27890073703353834252668027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18593382468902556168445351 27890073703353834252668027)
        ·
          refine ⟨41835110555030751379002041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27890073703353834252668027 41835110555030751379002041)
          ·
            refine ⟨31376332916273063534251531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41835110555030751379002041 31376332916273063534251531)
            ·
              refine ⟨47064499374409595301377297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31376332916273063534251531 47064499374409595301377297)
              ·
                refine ⟨35298374530807196476032973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47064499374409595301377297 35298374530807196476032973)
                ·
                  refine ⟨13236890449052698678512365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35298374530807196476032973 13236890449052698678512365)
                  ·
                    refine ⟨4963833918394762004442137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13236890449052698678512365 4963833918394762004442137)
                    ·
                      refine ⟨3722875438796071503331603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963833918394762004442137 3722875438796071503331603)
                      ·
                        rfl

theorem cell23_7250274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_7250274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250274 prefixEnd_7250274 := by exact prefixLift 7250274
  have htrace : WordTrace (prefixWord ++ tailWord_7250274) baseStart_7250274 baseEnd_7250274 := by
    simpa [prefixWord, tailWord_7250274, baseEnd_7250274] using wordTrace_append hprefix tailTrace_7250274
  have hstable : (prefixWord ++ tailWord_7250274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250274).length < 2 ^ (prefixWord ++ tailWord_7250274).sum := by decide
  have hdescent : baseEnd_7250274 < baseStart_7250274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250280 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 1, 8]
def baseStart_7250280 : Nat := 118140960795 + 7250280 * 2 ^ 59
def prefixEnd_7250280 : Nat := 4983230072969 + 3 ^ 40 * 7250280 * 2
def baseEnd_7250280 : Nat := 1240959506559999493285525

theorem tailTrace_7250280 : CollatzResearch.WordTrace tailWord_7250280 prefixEnd_7250280 1240959506559999493285525 := by
  unfold tailWord_7250280
  simp only [CollatzResearch.WordTrace]
  refine ⟨132219718086740642043526147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176292957448987522724701529 132219718086740642043526147)
  ·
    refine ⟨198329577130110963065289221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132219718086740642043526147 198329577130110963065289221)
    ·
      refine ⟨37186795711895805574741729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198329577130110963065289221 37186795711895805574741729)
      ·
        refine ⟨27890096783921854181056297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37186795711895805574741729 27890096783921854181056297)
        ·
          refine ⟨20917572587941390635792223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27890096783921854181056297 20917572587941390635792223)
          ·
            refine ⟨31376358881912085953688335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20917572587941390635792223 31376358881912085953688335)
            ·
              refine ⟨47064538322868128930532503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31376358881912085953688335 47064538322868128930532503)
              ·
                refine ⟨70596807484302193395798755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47064538322868128930532503 70596807484302193395798755)
                ·
                  refine ⟨105895211226453290093698133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70596807484302193395798755 105895211226453290093698133)
                  ·
                    refine ⟨1240959506559999493285525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105895211226453290093698133 1240959506559999493285525)
                    ·
                      rfl

theorem cell23_7250280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_7250280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250280 prefixEnd_7250280 := by exact prefixLift 7250280
  have htrace : WordTrace (prefixWord ++ tailWord_7250280) baseStart_7250280 baseEnd_7250280 := by
    simpa [prefixWord, tailWord_7250280, baseEnd_7250280] using wordTrace_append hprefix tailTrace_7250280
  have hstable : (prefixWord ++ tailWord_7250280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250280).length < 2 ^ (prefixWord ++ tailWord_7250280).sum := by decide
  have hdescent : baseEnd_7250280 < baseStart_7250280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250283 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 6]
def baseStart_7250283 : Nat := 118140960795 + 7250283 * 2 ^ 59
def prefixEnd_7250283 : Nat := 4983230072969 + 3 ^ 40 * 7250283 * 2
def baseEnd_7250283 : Nat := 3722880060121961968119061

theorem tailTrace_7250283 : CollatzResearch.WordTrace tailWord_7250283 prefixEnd_7250283 3722880060121961968119061 := by
  unfold tailWord_7250283
  simp only [CollatzResearch.WordTrace]
  refine ⟨264439545592470415599411503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176293030394980277066274335 264439545592470415599411503)
  ·
    refine ⟨396659318388705623399117255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264439545592470415599411503 396659318388705623399117255)
    ·
      refine ⟨594988977583058435098675883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396659318388705623399117255 594988977583058435098675883)
      ·
        refine ⟨892483466374587652648013825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594988977583058435098675883 892483466374587652648013825)
        ·
          refine ⟨669362599780940739486010369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 892483466374587652648013825 669362599780940739486010369)
          ·
            refine ⟨502021949835705554614507777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669362599780940739486010369 502021949835705554614507777)
            ·
              refine ⟨376516462376779165960880833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502021949835705554614507777 376516462376779165960880833)
              ·
                refine ⟨282387346782584374470660625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376516462376779165960880833 282387346782584374470660625)
                ·
                  refine ⟨211790510086938280852995469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282387346782584374470660625 211790510086938280852995469)
                  ·
                    refine ⟨79421441282601855319873301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211790510086938280852995469 79421441282601855319873301)
                    ·
                      refine ⟨3722880060121961968119061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79421441282601855319873301 3722880060121961968119061)
                      ·
                        rfl

theorem cell23_7250283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_7250283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250283 prefixEnd_7250283 := by exact prefixLift 7250283
  have htrace : WordTrace (prefixWord ++ tailWord_7250283) baseStart_7250283 baseEnd_7250283 := by
    simpa [prefixWord, tailWord_7250283, baseEnd_7250283] using wordTrace_append hprefix tailTrace_7250283
  have hstable : (prefixWord ++ tailWord_7250283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250283).length < 2 ^ (prefixWord ++ tailWord_7250283).sum := by decide
  have hdescent : baseEnd_7250283 < baseStart_7250283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250327 : List Nat := [1, 1, 3, 3, 1, 1, 4, 4, 5]
def baseStart_7250327 : Nat := 118140960795 + 7250327 * 2 ^ 59
def prefixEnd_7250327 : Nat := 4983230072969 + 3 ^ 40 * 7250327 * 2
def baseEnd_7250327 : Nat := 413655850363417755107651

theorem tailTrace_7250327 : CollatzResearch.WordTrace tailWord_7250327 prefixEnd_7250327 413655850363417755107651 := by
  unfold tailWord_7250327
  simp only [CollatzResearch.WordTrace]
  refine ⟨264441150404311011114013235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176294100269540674076008823 264441150404311011114013235)
  ·
    refine ⟨396661725606466516671019853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264441150404311011114013235 396661725606466516671019853)
    ·
      refine ⟨148748147102424943751632445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396661725606466516671019853 148748147102424943751632445)
      ·
        refine ⟨55780555163409353906862167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148748147102424943751632445 55780555163409353906862167)
        ·
          refine ⟨83670832745114030860293251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55780555163409353906862167 83670832745114030860293251)
          ·
            refine ⟨125506249117671046290439877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83670832745114030860293251 125506249117671046290439877)
            ·
              refine ⟨23532421709563321179457477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125506249117671046290439877 23532421709563321179457477)
              ·
                refine ⟨4412329070543122721148277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23532421709563321179457477 4412329070543122721148277)
                ·
                  refine ⟨413655850363417755107651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4412329070543122721148277 413655850363417755107651)
                  ·
                    rfl

theorem cell23_7250327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 5].length) (baseStart_7250327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250327 prefixEnd_7250327 := by exact prefixLift 7250327
  have htrace : WordTrace (prefixWord ++ tailWord_7250327) baseStart_7250327 baseEnd_7250327 := by
    simpa [prefixWord, tailWord_7250327, baseEnd_7250327] using wordTrace_append hprefix tailTrace_7250327
  have hstable : (prefixWord ++ tailWord_7250327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250327).length < 2 ^ (prefixWord ++ tailWord_7250327).sum := by decide
  have hdescent : baseEnd_7250327 < baseStart_7250327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250334 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_7250334 : Nat := 118140960795 + 7250334 * 2 ^ 59
def prefixEnd_7250334 : Nat := 4983230072969 + 3 ^ 40 * 7250334 * 2
def baseEnd_7250334 : Nat := 3722906247635341268581327

theorem tailTrace_7250334 : CollatzResearch.WordTrace tailWord_7250334 prefixEnd_7250334 3722906247635341268581327 := by
  unfold tailWord_7250334
  simp only [CollatzResearch.WordTrace]
  refine ⟨33055175714410706413689757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176294270476857100873012037 33055175714410706413689757)
  ·
    refine ⟨12395690892904014905133659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33055175714410706413689757 12395690892904014905133659)
    ·
      refine ⟨18593536339356022357700489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12395690892904014905133659 18593536339356022357700489)
      ·
        refine ⟨13945152254517016768275367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18593536339356022357700489 13945152254517016768275367)
        ·
          refine ⟨20917728381775525152413051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13945152254517016768275367 20917728381775525152413051)
          ·
            refine ⟨31376592572663287728619577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20917728381775525152413051 31376592572663287728619577)
            ·
              refine ⟨23532444429497465796464683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31376592572663287728619577 23532444429497465796464683)
              ·
                refine ⟨35298666644246198694697025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23532444429497465796464683 35298666644246198694697025)
                ·
                  refine ⟨26473999983184649021022769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35298666644246198694697025 26473999983184649021022769)
                  ·
                    refine ⟨19855499987388486765767077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26473999983184649021022769 19855499987388486765767077)
                    ·
                      refine ⟨3722906247635341268581327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19855499987388486765767077 3722906247635341268581327)
                      ·
                        rfl

theorem cell23_7250334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_7250334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250334 prefixEnd_7250334 := by exact prefixLift 7250334
  have htrace : WordTrace (prefixWord ++ tailWord_7250334) baseStart_7250334 baseEnd_7250334 := by
    simpa [prefixWord, tailWord_7250334, baseEnd_7250334] using wordTrace_append hprefix tailTrace_7250334
  have hstable : (prefixWord ++ tailWord_7250334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250334).length < 2 ^ (prefixWord ++ tailWord_7250334).sum := by decide
  have hdescent : baseEnd_7250334 < baseStart_7250334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250338 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_7250338 : Nat := 118140960795 + 7250338 * 2 ^ 59
def prefixEnd_7250338 : Nat := 4983230072969 + 3 ^ 40 * 7250338 * 2
def baseEnd_7250338 : Nat := 3722908301557959252931309

theorem tailTrace_7250338 : CollatzResearch.WordTrace tailWord_7250338 prefixEnd_7250338 3722908301557959252931309 := by
  unfold tailWord_7250338
  simp only [CollatzResearch.WordTrace]
  refine ⟨66110387901817789998165917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176294367738180773328442445 66110387901817789998165917)
  ·
    refine ⟨24791395463181671249312219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66110387901817789998165917 24791395463181671249312219)
    ·
      refine ⟨37187093194772506873968329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24791395463181671249312219 37187093194772506873968329)
      ·
        refine ⟨27890319896079380155476247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37187093194772506873968329 27890319896079380155476247)
        ·
          refine ⟨41835479844119070233214371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27890319896079380155476247 41835479844119070233214371)
          ·
            refine ⟨62753219766178605349821557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41835479844119070233214371 62753219766178605349821557)
            ·
              refine ⟨5883114353079244251545771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62753219766178605349821557 5883114353079244251545771)
              ·
                refine ⟨8824671529618866377318657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883114353079244251545771 8824671529618866377318657)
                ·
                  refine ⟨6618503647214149782988993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8824671529618866377318657 6618503647214149782988993)
                  ·
                    refine ⟨4963877735410612337241745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6618503647214149782988993 4963877735410612337241745)
                    ·
                      refine ⟨3722908301557959252931309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963877735410612337241745 3722908301557959252931309)
                      ·
                        rfl

theorem cell23_7250338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_7250338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250338 prefixEnd_7250338 := by exact prefixLift 7250338
  have htrace : WordTrace (prefixWord ++ tailWord_7250338) baseStart_7250338 baseEnd_7250338 := by
    simpa [prefixWord, tailWord_7250338, baseEnd_7250338] using wordTrace_append hprefix tailTrace_7250338
  have hstable : (prefixWord ++ tailWord_7250338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250338).length < 2 ^ (prefixWord ++ tailWord_7250338).sum := by decide
  have hdescent : baseEnd_7250338 < baseStart_7250338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250340 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_7250340 : Nat := 118140960795 + 7250340 * 2 ^ 59
def prefixEnd_7250340 : Nat := 4983230072969 + 3 ^ 40 * 7250340 * 2
def baseEnd_7250340 : Nat := 1240969776173089415035433

theorem tailTrace_7250340 : CollatzResearch.WordTrace tailWord_7250340 prefixEnd_7250340 1240969776173089415035433 := by
  unfold tailWord_7250340
  simp only [CollatzResearch.WordTrace]
  refine ⟨132220812276631957167118237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176294416368842609556157649 132220812276631957167118237)
  ·
    refine ⟨49582804603736983937669339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132220812276631957167118237 49582804603736983937669339)
    ·
      refine ⟨74374206905605475906504009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49582804603736983937669339 74374206905605475906504009)
      ·
        refine ⟨55780655179204106929878007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74374206905605475906504009 55780655179204106929878007)
        ·
          refine ⟨83670982768806160394817011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55780655179204106929878007 83670982768806160394817011)
          ·
            refine ⟨125506474153209240592225517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83670982768806160394817011 125506474153209240592225517)
            ·
              refine ⟨47064927807453465222084569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125506474153209240592225517 47064927807453465222084569)
              ·
                refine ⟨35298695855590098916563427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47064927807453465222084569 35298695855590098916563427)
                ·
                  refine ⟨52948043783385148374845141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35298695855590098916563427 52948043783385148374845141)
                  ·
                    refine ⟨1240969776173089415035433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52948043783385148374845141 1240969776173089415035433)
                    ·
                      rfl

theorem cell23_7250340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_7250340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250340 prefixEnd_7250340 := by exact prefixLift 7250340
  have htrace : WordTrace (prefixWord ++ tailWord_7250340) baseStart_7250340 baseEnd_7250340 := by
    simpa [prefixWord, tailWord_7250340, baseEnd_7250340] using wordTrace_append hprefix tailTrace_7250340
  have hstable : (prefixWord ++ tailWord_7250340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250340).length < 2 ^ (prefixWord ++ tailWord_7250340).sum := by decide
  have hdescent : baseEnd_7250340 < baseStart_7250340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250377 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 4, 4, 2]
def baseStart_7250377 : Nat := 118140960795 + 7250377 * 2 ^ 59
def prefixEnd_7250377 : Nat := 4983230072969 + 3 ^ 40 * 7250377 * 2
def baseEnd_7250377 : Nat := 3722928327303484600343629

theorem tailTrace_7250377 : CollatzResearch.WordTrace tailWord_7250377 prefixEnd_7250377 3722928327303484600343629 := by
  unfold tailWord_7250377
  simp only [CollatzResearch.WordTrace]
  refine ⟨264442974054129869653333385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176295316036086579768888923 264442974054129869653333385)
  ·
    refine ⟨198332230540597402240000039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264442974054129869653333385 198332230540597402240000039)
    ·
      refine ⟨297498345810896103360000059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198332230540597402240000039 297498345810896103360000059)
      ·
        refine ⟨446247518716344155040000089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297498345810896103360000059 446247518716344155040000089)
        ·
          refine ⟨334685639037258116280000067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446247518716344155040000089 334685639037258116280000067)
          ·
            refine ⟨502028458555887174420000101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334685639037258116280000067 502028458555887174420000101)
            ·
              refine ⟨94130335979228845203750019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502028458555887174420000101 94130335979228845203750019)
              ·
                refine ⟨141195503968843267805625029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94130335979228845203750019 141195503968843267805625029)
                ·
                  refine ⟨26474156994158112713554693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141195503968843267805625029 26474156994158112713554693)
                  ·
                    refine ⟨4963904436404646133791505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26474156994158112713554693 4963904436404646133791505)
                    ·
                      refine ⟨3722928327303484600343629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963904436404646133791505 3722928327303484600343629)
                      ·
                        rfl

theorem cell23_7250377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 4, 2].length) (baseStart_7250377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250377 prefixEnd_7250377 := by exact prefixLift 7250377
  have htrace : WordTrace (prefixWord ++ tailWord_7250377) baseStart_7250377 baseEnd_7250377 := by
    simpa [prefixWord, tailWord_7250377, baseEnd_7250377] using wordTrace_append hprefix tailTrace_7250377
  have hstable : (prefixWord ++ tailWord_7250377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250377).length < 2 ^ (prefixWord ++ tailWord_7250377).sum := by decide
  have hdescent : baseEnd_7250377 < baseStart_7250377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250414 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_7250414 : Nat := 118140960795 + 7250414 * 2 ^ 59
def prefixEnd_7250414 : Nat := 4983230072969 + 3 ^ 40 * 7250414 * 2
def baseEnd_7250414 : Nat := 3722947326087700955580959

theorem tailTrace_7250414 : CollatzResearch.WordTrace tailWord_7250414 prefixEnd_7250414 3722947326087700955580959 := by
  unfold tailWord_7250414
  simp only [CollatzResearch.WordTrace]
  refine ⟨33055540444374478121553787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176296215703330549981620197 33055540444374478121553787)
  ·
    refine ⟨49583310666561717182330681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33055540444374478121553787 49583310666561717182330681)
    ·
      refine ⟨37187482999921287886748011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49583310666561717182330681 37187482999921287886748011)
      ·
        refine ⟨55781224499881931830122017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37187482999921287886748011 55781224499881931830122017)
        ·
          refine ⟨41835918374911448872591513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55781224499881931830122017 41835918374911448872591513)
          ·
            refine ⟨31376938781183586654443635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41835918374911448872591513 31376938781183586654443635)
            ·
              refine ⟨47065408171775379981665453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31376938781183586654443635 47065408171775379981665453)
              ·
                refine ⟨17649528064415767493124545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47065408171775379981665453 17649528064415767493124545)
                ·
                  refine ⟨13237146048311825619843409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17649528064415767493124545 13237146048311825619843409)
                  ·
                    refine ⟨9927859536233869214882557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13237146048311825619843409 9927859536233869214882557)
                    ·
                      refine ⟨3722947326087700955580959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9927859536233869214882557 3722947326087700955580959)
                      ·
                        rfl

theorem cell23_7250414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_7250414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250414 prefixEnd_7250414 := by exact prefixLift 7250414
  have htrace : WordTrace (prefixWord ++ tailWord_7250414) baseStart_7250414 baseEnd_7250414 := by
    simpa [prefixWord, tailWord_7250414, baseEnd_7250414] using wordTrace_append hprefix tailTrace_7250414
  have hstable : (prefixWord ++ tailWord_7250414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250414).length < 2 ^ (prefixWord ++ tailWord_7250414).sum := by decide
  have hdescent : baseEnd_7250414 < baseStart_7250414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250461 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_7250461 : Nat := 118140960795 + 7250461 * 2 ^ 59
def prefixEnd_7250461 : Nat := 4983230072969 + 3 ^ 40 * 7250461 * 2
def baseEnd_7250461 : Nat := 3722971459678462271693243

theorem tailTrace_7250461 : CollatzResearch.WordTrace tailWord_7250461 prefixEnd_7250461 3722971459678462271693243 := by
  unfold tailWord_7250461
  simp only [CollatzResearch.WordTrace]
  refine ⟨264446037785825551999391237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176297358523883701332927491 264446037785825551999391237)
  ·
    refine ⟨49583632084842290999885857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264446037785825551999391237 49583632084842290999885857)
    ·
      refine ⟨37187724063631718249914393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49583632084842290999885857 37187724063631718249914393)
      ·
        refine ⟨27890793047723788687435795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37187724063631718249914393 27890793047723788687435795)
        ·
          refine ⟨41836189571585683031153693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27890793047723788687435795 41836189571585683031153693)
          ·
            refine ⟨15688571089344631136682635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41836189571585683031153693 15688571089344631136682635)
            ·
              refine ⟨23532856634016946705023953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15688571089344631136682635 23532856634016946705023953)
              ·
                refine ⟨17649642475512710028767965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23532856634016946705023953 17649642475512710028767965)
                ·
                  refine ⟨6618615928317266260787987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17649642475512710028767965 6618615928317266260787987)
                  ·
                    refine ⟨9927923892475899391181981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6618615928317266260787987 9927923892475899391181981)
                    ·
                      refine ⟨3722971459678462271693243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9927923892475899391181981 3722971459678462271693243)
                      ·
                        rfl

theorem cell23_7250461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_7250461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250461 prefixEnd_7250461 := by exact prefixLift 7250461
  have htrace : WordTrace (prefixWord ++ tailWord_7250461) baseStart_7250461 baseEnd_7250461 := by
    simpa [prefixWord, tailWord_7250461, baseEnd_7250461] using wordTrace_append hprefix tailTrace_7250461
  have hstable : (prefixWord ++ tailWord_7250461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250461).length < 2 ^ (prefixWord ++ tailWord_7250461).sum := by decide
  have hdescent : baseEnd_7250461 < baseStart_7250461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250487 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_7250487 : Nat := 118140960795 + 7250487 * 2 ^ 59
def prefixEnd_7250487 : Nat := 4983230072969 + 3 ^ 40 * 7250487 * 2
def baseEnd_7250487 : Nat := 3722984810175479169968123

theorem tailTrace_7250487 : CollatzResearch.WordTrace tailWord_7250487 prefixEnd_7250487 3722984810175479169968123 := by
  unfold tailWord_7250487
  simp only [CollatzResearch.WordTrace]
  refine ⟨264446986083731358439837715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176297990722487572293225143 264446986083731358439837715)
  ·
    refine ⟨396670479125597037659756573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264446986083731358439837715 396670479125597037659756573)
    ·
      refine ⟨148751429672098889122408715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396670479125597037659756573 148751429672098889122408715)
      ·
        refine ⟨223127144508148333683613073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148751429672098889122408715 223127144508148333683613073)
        ·
          refine ⟨167345358381111250262709805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223127144508148333683613073 167345358381111250262709805)
          ·
            refine ⟨62754509392916718848516177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167345358381111250262709805 62754509392916718848516177)
            ·
              refine ⟨47065882044687539136387133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62754509392916718848516177 47065882044687539136387133)
              ·
                refine ⟨17649705766757827176145175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47065882044687539136387133 17649705766757827176145175)
                ·
                  refine ⟨26474558650136740764217763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17649705766757827176145175 26474558650136740764217763)
                  ·
                    refine ⟨39711837975205111146326645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26474558650136740764217763 39711837975205111146326645)
                    ·
                      refine ⟨3722984810175479169968123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39711837975205111146326645 3722984810175479169968123)
                      ·
                        rfl

theorem cell23_7250487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_7250487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250487 prefixEnd_7250487 := by exact prefixLift 7250487
  have htrace : WordTrace (prefixWord ++ tailWord_7250487) baseStart_7250487 baseEnd_7250487 := by
    simpa [prefixWord, tailWord_7250487, baseEnd_7250487] using wordTrace_append hprefix tailTrace_7250487
  have hstable : (prefixWord ++ tailWord_7250487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250487).length < 2 ^ (prefixWord ++ tailWord_7250487).sum := by decide
  have hdescent : baseEnd_7250487 < baseStart_7250487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250501 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 3, 2, 2]
def baseStart_7250501 : Nat := 118140960795 + 7250501 * 2 ^ 59
def prefixEnd_7250501 : Nat := 4983230072969 + 3 ^ 40 * 7250501 * 2
def baseEnd_7250501 : Nat := 3722991998904642115193059

theorem tailTrace_7250501 : CollatzResearch.WordTrace tailWord_7250501 prefixEnd_7250501 3722991998904642115193059 := by
  unfold tailWord_7250501
  simp only [CollatzResearch.WordTrace]
  refine ⟨264447496705680638830847357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176298331137120425887231571 264447496705680638830847357)
  ·
    refine ⟨99167811264630239561567759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264447496705680638830847357 99167811264630239561567759)
    ·
      refine ⟨148751716896945359342351639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99167811264630239561567759 148751716896945359342351639)
      ·
        refine ⟨223127575345418039013527459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148751716896945359342351639 223127575345418039013527459)
        ·
          refine ⟨334691363018127058520291189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223127575345418039013527459 334691363018127058520291189)
          ·
            refine ⟨31377315282949411736277299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 334691363018127058520291189 31377315282949411736277299)
            ·
              refine ⟨47065972924424117604415949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31377315282949411736277299 47065972924424117604415949)
              ·
                refine ⟨17649739846659044101655981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47065972924424117604415949 17649739846659044101655981)
                ·
                  refine ⟨6618652442497141538120993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17649739846659044101655981 6618652442497141538120993)
                  ·
                    refine ⟨4963989331872856153590745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6618652442497141538120993 4963989331872856153590745)
                    ·
                      refine ⟨3722991998904642115193059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4963989331872856153590745 3722991998904642115193059)
                      ·
                        rfl

theorem cell23_7250501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 2, 2].length) (baseStart_7250501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250501 prefixEnd_7250501 := by exact prefixLift 7250501
  have htrace : WordTrace (prefixWord ++ tailWord_7250501) baseStart_7250501 baseEnd_7250501 := by
    simpa [prefixWord, tailWord_7250501, baseEnd_7250501] using wordTrace_append hprefix tailTrace_7250501
  have hstable : (prefixWord ++ tailWord_7250501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250501).length < 2 ^ (prefixWord ++ tailWord_7250501).sum := by decide
  have hdescent : baseEnd_7250501 < baseStart_7250501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250524 : List Nat := [2, 2, 4, 1, 3, 1, 1, 9]
def baseStart_7250524 : Nat := 118140960795 + 7250524 * 2 ^ 59
def prefixEnd_7250524 : Nat := 4983230072969 + 3 ^ 40 * 7250524 * 2
def baseEnd_7250524 : Nat := 137889029961470204637239

theorem tailTrace_7250524 : CollatzResearch.WordTrace tailWord_7250524 prefixEnd_7250524 137889029961470204637239 := by
  unfold tailWord_7250524
  simp only [CollatzResearch.WordTrace]
  refine ⟨132224167792298656879467313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176298890389731542505956417 132224167792298656879467313)
  ·
    refine ⟨99168125844223992659600485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132224167792298656879467313 99168125844223992659600485)
    ·
      refine ⟨18594023595791998623675091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99168125844223992659600485 18594023595791998623675091)
      ·
        refine ⟨27891035393687997935512637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18594023595791998623675091 27891035393687997935512637)
        ·
          refine ⟨10459138272632999225817239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27891035393687997935512637 10459138272632999225817239)
          ·
            refine ⟨15688707408949498838725859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10459138272632999225817239 15688707408949498838725859)
            ·
              refine ⟨23533061113424248258088789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15688707408949498838725859 23533061113424248258088789)
              ·
                refine ⟨137889029961470204637239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23533061113424248258088789 137889029961470204637239)
                ·
                  rfl

theorem cell23_7250524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 9].length) (baseStart_7250524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250524 prefixEnd_7250524 := by exact prefixLift 7250524
  have htrace : WordTrace (prefixWord ++ tailWord_7250524) baseStart_7250524 baseEnd_7250524 := by
    simpa [prefixWord, tailWord_7250524, baseEnd_7250524] using wordTrace_append hprefix tailTrace_7250524
  have hstable : (prefixWord ++ tailWord_7250524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250524).length < 2 ^ (prefixWord ++ tailWord_7250524).sum := by decide
  have hdescent : baseEnd_7250524 < baseStart_7250524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250561 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_7250561 : Nat := 118140960795 + 7250561 * 2 ^ 59
def prefixEnd_7250561 : Nat := 4983230072969 + 3 ^ 40 * 7250561 * 2
def baseEnd_7250561 : Nat := 3723022807743911880442783

theorem tailTrace_7250561 : CollatzResearch.WordTrace tailWord_7250561 prefixEnd_7250561 3723022807743911880442783 := by
  unfold tailWord_7250561
  simp only [CollatzResearch.WordTrace]
  refine ⟨264449685085463269078031537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176299790056975512718687691 264449685085463269078031537)
  ·
    refine ⟨198337263814097451808523653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264449685085463269078031537 198337263814097451808523653)
    ·
      refine ⟨37188236965143272214098185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198337263814097451808523653 37188236965143272214098185)
      ·
        refine ⟨27891177723857454160573639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37188236965143272214098185 27891177723857454160573639)
        ·
          refine ⟨41836766585786181240860459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27891177723857454160573639 41836766585786181240860459)
          ·
            refine ⟨62755149878679271861290689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41836766585786181240860459 62755149878679271861290689)
            ·
              refine ⟨47066362409009453895968017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62755149878679271861290689 47066362409009453895968017)
              ·
                refine ⟨35299771806757090421976013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47066362409009453895968017 35299771806757090421976013)
                ·
                  refine ⟨13237414427533908908241005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35299771806757090421976013 13237414427533908908241005)
                  ·
                    refine ⟨4964030410325215840590377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13237414427533908908241005 4964030410325215840590377)
                    ·
                      refine ⟨3723022807743911880442783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964030410325215840590377 3723022807743911880442783)
                      ·
                        rfl

theorem cell23_7250561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_7250561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250561 prefixEnd_7250561 := by exact prefixLift 7250561
  have htrace : WordTrace (prefixWord ++ tailWord_7250561) baseStart_7250561 baseEnd_7250561 := by
    simpa [prefixWord, tailWord_7250561, baseEnd_7250561] using wordTrace_append hprefix tailTrace_7250561
  have hstable : (prefixWord ++ tailWord_7250561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250561).length < 2 ^ (prefixWord ++ tailWord_7250561).sum := by decide
  have hdescent : baseEnd_7250561 < baseStart_7250561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250562 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7250562 : Nat := 118140960795 + 7250562 * 2 ^ 59
def prefixEnd_7250562 : Nat := 4983230072969 + 3 ^ 40 * 7250562 * 2
def baseEnd_7250562 : Nat := 1241007773741522125510093

theorem tailTrace_7250562 : CollatzResearch.WordTrace tailWord_7250562 prefixEnd_7250562 1241007773741522125510093 := by
  unfold tailWord_7250562
  simp only [CollatzResearch.WordTrace]
  refine ⟨66112430389614911562204485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176299814372306430832545293 66112430389614911562204485)
  ·
    refine ⟨12396080698052795917913341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66112430389614911562204485 12396080698052795917913341)
    ·
      refine ⟨4648530261769798469217503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12396080698052795917913341 4648530261769798469217503)
      ·
        refine ⟨6972795392654697703826255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4648530261769798469217503 6972795392654697703826255)
        ·
          refine ⟨10459193088982046555739383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972795392654697703826255 10459193088982046555739383)
          ·
            refine ⟨15688789633473069833609075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10459193088982046555739383 15688789633473069833609075)
            ·
              refine ⟨23533184450209604750413613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15688789633473069833609075 23533184450209604750413613)
              ·
                refine ⟨8824944168828601781405105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23533184450209604750413613 8824944168828601781405105)
                ·
                  refine ⟨6618708126621451336053829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8824944168828601781405105 6618708126621451336053829)
                  ·
                    refine ⟨1241007773741522125510093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6618708126621451336053829 1241007773741522125510093)
                    ·
                      rfl

theorem cell23_7250562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7250562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250562 prefixEnd_7250562 := by exact prefixLift 7250562
  have htrace : WordTrace (prefixWord ++ tailWord_7250562) baseStart_7250562 baseEnd_7250562 := by
    simpa [prefixWord, tailWord_7250562, baseEnd_7250562] using wordTrace_append hprefix tailTrace_7250562
  have hstable : (prefixWord ++ tailWord_7250562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250562).length < 2 ^ (prefixWord ++ tailWord_7250562).sum := by decide
  have hdescent : baseEnd_7250562 < baseStart_7250562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250567 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 1, 8]
def baseStart_7250567 : Nat := 118140960795 + 7250567 * 2 ^ 59
def prefixEnd_7250567 : Nat := 4983230072969 + 3 ^ 40 * 7250567 * 2
def baseEnd_7250567 : Nat := 1241008629542612952322585

theorem tailTrace_7250567 : CollatzResearch.WordTrace tailWord_7250567 prefixEnd_7250567 1241008629542612952322585 := by
  unfold tailWord_7250567
  simp only [CollatzResearch.WordTrace]
  refine ⟨264449903923441532102749955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176299935948961021401833303 264449903923441532102749955)
  ·
    refine ⟨396674855885162298154124933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264449903923441532102749955 396674855885162298154124933)
    ·
      refine ⟨74376535478467930903898425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396674855885162298154124933 74376535478467930903898425)
      ·
        refine ⟨55782401608850948177923819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74376535478467930903898425 55782401608850948177923819)
        ·
          refine ⟨83673602413276422266885729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55782401608850948177923819 83673602413276422266885729)
          ·
            refine ⟨62755201809957316700164297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83673602413276422266885729 62755201809957316700164297)
            ·
              refine ⟨47066401357467987525123223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62755201809957316700164297 47066401357467987525123223)
              ·
                refine ⟨70599602036201981287684835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47066401357467987525123223 70599602036201981287684835)
                ·
                  refine ⟨105899403054302971931527253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70599602036201981287684835 105899403054302971931527253)
                  ·
                    refine ⟨1241008629542612952322585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105899403054302971931527253 1241008629542612952322585)
                    ·
                      rfl

theorem cell23_7250567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_7250567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250567 prefixEnd_7250567 := by exact prefixLift 7250567
  have htrace : WordTrace (prefixWord ++ tailWord_7250567) baseStart_7250567 baseEnd_7250567 := by
    simpa [prefixWord, tailWord_7250567, baseEnd_7250567] using wordTrace_append hprefix tailTrace_7250567
  have hstable : (prefixWord ++ tailWord_7250567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250567).length < 2 ^ (prefixWord ++ tailWord_7250567).sum := by decide
  have hdescent : baseEnd_7250567 < baseStart_7250567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250578 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_7250578 : Nat := 118140960795 + 7250578 * 2 ^ 59
def prefixEnd_7250578 : Nat := 4983230072969 + 3 ^ 40 * 7250578 * 2
def baseEnd_7250578 : Nat := 3723031536915038313930205

theorem tailTrace_7250578 : CollatzResearch.WordTrace tailWord_7250578 prefixEnd_7250578 3723031536915038313930205 := by
  unfold tailWord_7250578
  simp only [CollatzResearch.WordTrace]
  refine ⟨66112576281600420245350097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176300203417601120654266925 66112576281600420245350097)
  ·
    refine ⟨49584432211200315184012573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66112576281600420245350097 49584432211200315184012573)
    ·
      refine ⟨18594162079200118194004715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49584432211200315184012573 18594162079200118194004715)
      ·
        refine ⟨27891243118800177291007073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18594162079200118194004715 27891243118800177291007073)
        ·
          refine ⟨20918432339100132968255305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27891243118800177291007073 20918432339100132968255305)
          ·
            refine ⟨15688824254325099726191479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20918432339100132968255305 15688824254325099726191479)
            ·
              refine ⟨23533236381487649589287219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15688824254325099726191479 23533236381487649589287219)
              ·
                refine ⟨35299854572231474383930829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23533236381487649589287219 35299854572231474383930829)
                ·
                  refine ⟨13237445464586802893974061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35299854572231474383930829 13237445464586802893974061)
                  ·
                    refine ⟨4964042049220051085240273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13237445464586802893974061 4964042049220051085240273)
                    ·
                      refine ⟨3723031536915038313930205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964042049220051085240273 3723031536915038313930205)
                      ·
                        rfl

theorem cell23_7250578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_7250578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250578 prefixEnd_7250578 := by exact prefixLift 7250578
  have htrace : WordTrace (prefixWord ++ tailWord_7250578) baseStart_7250578 baseEnd_7250578 := by
    simpa [prefixWord, tailWord_7250578, baseEnd_7250578] using wordTrace_append hprefix tailTrace_7250578
  have hstable : (prefixWord ++ tailWord_7250578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250578).length < 2 ^ (prefixWord ++ tailWord_7250578).sum := by decide
  have hdescent : baseEnd_7250578 < baseStart_7250578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250602 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7250602 : Nat := 118140960795 + 7250602 * 2 ^ 59
def prefixEnd_7250602 : Nat := 4983230072969 + 3 ^ 40 * 7250602 * 2
def baseEnd_7250602 : Nat := 3723043860450746220030095

theorem tailTrace_7250602 : CollatzResearch.WordTrace tailWord_7250602 prefixEnd_7250602 3723043860450746220030095 := by
  unfold tailWord_7250602
  simp only [CollatzResearch.WordTrace]
  refine ⟨66112795119578683270068515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176300786985543155386849373 66112795119578683270068515)
  ·
    refine ⟨99169192679368024905102773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66112795119578683270068515 99169192679368024905102773)
    ·
      refine ⟨9297111813690752334853385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99169192679368024905102773 9297111813690752334853385)
      ·
        refine ⟨6972833860268064251140039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9297111813690752334853385 6972833860268064251140039)
        ·
          refine ⟨10459250790402096376710059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972833860268064251140039 10459250790402096376710059)
          ·
            refine ⟨15688876185603144565065089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10459250790402096376710059 15688876185603144565065089)
            ·
              refine ⟨11766657139202358423798817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15688876185603144565065089 11766657139202358423798817)
              ·
                refine ⟨8824992854401768817849113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11766657139202358423798817 8824992854401768817849113)
                ·
                  refine ⟨6618744640801326613386835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8824992854401768817849113 6618744640801326613386835)
                  ·
                    refine ⟨9928116961201989920080253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6618744640801326613386835 9928116961201989920080253)
                    ·
                      refine ⟨3723043860450746220030095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9928116961201989920080253 3723043860450746220030095)
                      ·
                        rfl

theorem cell23_7250602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7250602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250602 prefixEnd_7250602 := by exact prefixLift 7250602
  have htrace : WordTrace (prefixWord ++ tailWord_7250602) baseStart_7250602 baseEnd_7250602 := by
    simpa [prefixWord, tailWord_7250602, baseEnd_7250602] using wordTrace_append hprefix tailTrace_7250602
  have hstable : (prefixWord ++ tailWord_7250602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250602).length < 2 ^ (prefixWord ++ tailWord_7250602).sum := by decide
  have hdescent : baseEnd_7250602 < baseStart_7250602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250617 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7250617 : Nat := 118140960795 + 7250617 * 2 ^ 59
def prefixEnd_7250617 : Nat := 4983230072969 + 3 ^ 40 * 7250617 * 2
def baseEnd_7250617 : Nat := 3723051562660563661342525

theorem tailTrace_7250617 : CollatzResearch.WordTrace tailWord_7250617 prefixEnd_7250617 3723051562660563661342525 := by
  unfold tailWord_7250617
  simp only [CollatzResearch.WordTrace]
  refine ⟨264451727573260390642070105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176301151715506927094713403 264451727573260390642070105)
  ·
    refine ⟨198338795679945292981552579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264451727573260390642070105 198338795679945292981552579)
    ·
      refine ⟨297508193519917939472328869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198338795679945292981552579 297508193519917939472328869)
      ·
        refine ⟨55782786284984613651061663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297508193519917939472328869 55782786284984613651061663)
        ·
          refine ⟨83674179427476920476592495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55782786284984613651061663 83674179427476920476592495)
          ·
            refine ⟨125511269141215380714888743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83674179427476920476592495 125511269141215380714888743)
            ·
              refine ⟨188266903711823071072333115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125511269141215380714888743 188266903711823071072333115)
              ·
                refine ⟨282400355567734606608499673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188266903711823071072333115 282400355567734606608499673)
                ·
                  refine ⟨211800266675800954956374755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282400355567734606608499673 211800266675800954956374755)
                  ·
                    refine ⟨317700400013701432434562133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 211800266675800954956374755 317700400013701432434562133)
                    ·
                      refine ⟨3723051562660563661342525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 317700400013701432434562133 3723051562660563661342525)
                      ·
                        rfl

theorem cell23_7250617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7250617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250617 prefixEnd_7250617 := by exact prefixLift 7250617
  have htrace : WordTrace (prefixWord ++ tailWord_7250617) baseStart_7250617 baseEnd_7250617 := by
    simpa [prefixWord, tailWord_7250617, baseEnd_7250617] using wordTrace_append hprefix tailTrace_7250617
  have hstable : (prefixWord ++ tailWord_7250617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250617).length < 2 ^ (prefixWord ++ tailWord_7250617).sum := by decide
  have hdescent : baseEnd_7250617 < baseStart_7250617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250624 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 3]
def baseStart_7250624 : Nat := 118140960795 + 7250624 * 2 ^ 59
def prefixEnd_7250624 : Nat := 4983230072969 + 3 ^ 40 * 7250624 * 2
def baseEnd_7250624 : Nat := 3723055157025145133954993

theorem tailTrace_7250624 : CollatzResearch.WordTrace tailWord_7250624 prefixEnd_7250624 3723055157025145133954993 := by
  unfold tailWord_7250624
  simp only [CollatzResearch.WordTrace]
  refine ⟨132225991442117515418787463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176301321922823353891716617 132225991442117515418787463)
  ·
    refine ⟨198338987163176273128181195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132225991442117515418787463 198338987163176273128181195)
    ·
      refine ⟨297508480744764409692271793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198338987163176273128181195 297508480744764409692271793)
      ·
        refine ⟨223131360558573307269203845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297508480744764409692271793 223131360558573307269203845)
        ·
          refine ⟨41837130104732495112975721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223131360558573307269203845 41837130104732495112975721)
          ·
            refine ⟨31377847578549371334731791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41837130104732495112975721 31377847578549371334731791)
            ·
              refine ⟨47066771367824057002097687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31377847578549371334731791 47066771367824057002097687)
              ·
                refine ⟨70600157051736085503146531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47066771367824057002097687 70600157051736085503146531)
                ·
                  refine ⟨105900235577604128254719797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70600157051736085503146531 105900235577604128254719797)
                  ·
                    refine ⟨9928147085400387023879981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105900235577604128254719797 9928147085400387023879981)
                    ·
                      refine ⟨3723055157025145133954993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9928147085400387023879981 3723055157025145133954993)
                      ·
                        rfl

theorem cell23_7250624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_7250624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250624 prefixEnd_7250624 := by exact prefixLift 7250624
  have htrace : WordTrace (prefixWord ++ tailWord_7250624) baseStart_7250624 baseEnd_7250624 := by
    simpa [prefixWord, tailWord_7250624, baseEnd_7250624] using wordTrace_append hprefix tailTrace_7250624
  have hstable : (prefixWord ++ tailWord_7250624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250624).length < 2 ^ (prefixWord ++ tailWord_7250624).sum := by decide
  have hdescent : baseEnd_7250624 < baseStart_7250624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250676 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7250676 : Nat := 118140960795 + 7250676 * 2 ^ 59
def prefixEnd_7250676 : Nat := 4983230072969 + 3 ^ 40 * 7250676 * 2
def baseEnd_7250676 : Nat := 3723081858019178930504755

theorem tailTrace_7250676 : CollatzResearch.WordTrace tailWord_7250676 prefixEnd_7250676 3723081858019178930504755 := by
  unfold tailWord_7250676
  simp only [CollatzResearch.WordTrace]
  refine ⟨132226939740023321859233941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176302586320031095812311921 132226939740023321859233941)
  ·
    refine ⟨6198137800313593212151591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132226939740023321859233941 6198137800313593212151591)
    ·
      refine ⟨9297206700470389818227387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6198137800313593212151591 9297206700470389818227387)
      ·
        refine ⟨13945810050705584727341081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9297206700470389818227387 13945810050705584727341081)
        ·
          refine ⟨10459357538029188545505811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13945810050705584727341081 10459357538029188545505811)
          ·
            refine ⟨15689036307043782818258717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10459357538029188545505811 15689036307043782818258717)
            ·
              refine ⟨5883388615141418556847019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15689036307043782818258717 5883388615141418556847019)
              ·
                refine ⟨8825082922712127835270529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883388615141418556847019 8825082922712127835270529)
                ·
                  refine ⟨6618812192034095876452897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8825082922712127835270529 6618812192034095876452897)
                  ·
                    refine ⟨4964109144025571907339673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6618812192034095876452897 4964109144025571907339673)
                    ·
                      refine ⟨3723081858019178930504755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964109144025571907339673 3723081858019178930504755)
                      ·
                        rfl

theorem cell23_7250676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7250676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250676 prefixEnd_7250676 := by exact prefixLift 7250676
  have htrace : WordTrace (prefixWord ++ tailWord_7250676) baseStart_7250676 baseEnd_7250676 := by
    simpa [prefixWord, tailWord_7250676, baseEnd_7250676] using wordTrace_append hprefix tailTrace_7250676
  have hstable : (prefixWord ++ tailWord_7250676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250676).length < 2 ^ (prefixWord ++ tailWord_7250676).sum := by decide
  have hdescent : baseEnd_7250676 < baseStart_7250676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250725 : List Nat := [1, 3, 1, 2, 3, 1, 5, 2, 1, 4]
def baseStart_7250725 : Nat := 118140960795 + 7250725 * 2 ^ 59
def prefixEnd_7250725 : Nat := 4983230072969 + 3 ^ 40 * 7250725 * 2
def baseEnd_7250725 : Nat := 1241035672857083079597343

theorem tailTrace_7250725 : CollatzResearch.WordTrace tailWord_7250725 prefixEnd_7250725 1241035672857083079597343 := by
  unfold tailWord_7250725
  simp only [CollatzResearch.WordTrace]
  refine ⟨264455666656869125087001629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176303777771246083391334419 264455666656869125087001629)
  ·
    refine ⟨99170874996325921907625611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264455666656869125087001629 99170874996325921907625611)
    ·
      refine ⟨148756312494488882861438417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99170874996325921907625611 148756312494488882861438417)
      ·
        refine ⟨111567234370866662146078813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148756312494488882861438417 111567234370866662146078813)
        ·
          refine ⟨41837712889074998304779555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111567234370866662146078813 41837712889074998304779555)
          ·
            refine ⟨62756569333612497457169333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41837712889074998304779555 62756569333612497457169333)
            ·
              refine ⟨5883428375026171636609625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62756569333612497457169333 5883428375026171636609625)
              ·
                refine ⟨4412571281269628727457219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5883428375026171636609625 4412571281269628727457219)
                ·
                  refine ⟨6618856921904443091185829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4412571281269628727457219 6618856921904443091185829)
                  ·
                    refine ⟨1241035672857083079597343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6618856921904443091185829 1241035672857083079597343)
                    ·
                      rfl

theorem cell23_7250725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_7250725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250725 prefixEnd_7250725 := by exact prefixLift 7250725
  have htrace : WordTrace (prefixWord ++ tailWord_7250725) baseStart_7250725 baseEnd_7250725 := by
    simpa [prefixWord, tailWord_7250725, baseEnd_7250725] using wordTrace_append hprefix tailTrace_7250725
  have hstable : (prefixWord ++ tailWord_7250725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250725).length < 2 ^ (prefixWord ++ tailWord_7250725).sum := by decide
  have hdescent : baseEnd_7250725 < baseStart_7250725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250751 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 3, 5]
def baseStart_7250751 : Nat := 118140960795 + 7250751 * 2 ^ 59
def prefixEnd_7250751 : Nat := 4983230072969 + 3 ^ 40 * 7250751 * 2
def baseEnd_7250751 : Nat := 1241040123022755379022303

theorem tailTrace_7250751 : CollatzResearch.WordTrace tailWord_7250751 prefixEnd_7250751 1241040123022755379022303 := by
  unfold tailWord_7250751
  simp only [CollatzResearch.WordTrace]
  refine ⟨264456614954774931527448107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176304409969849954351632071 264456614954774931527448107)
  ·
    refine ⟨396684922432162397291172161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264456614954774931527448107 396684922432162397291172161)
    ·
      refine ⟨297513691824121797968379121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396684922432162397291172161 297513691824121797968379121)
      ·
        refine ⟨223135268868091348476284341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297513691824121797968379121 223135268868091348476284341)
        ·
          refine ⟨20918931456383563919651657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223135268868091348476284341 20918931456383563919651657)
          ·
            refine ⟨15689198592287672939738743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20918931456383563919651657 15689198592287672939738743)
            ·
              refine ⟨23533797888431509409608115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15689198592287672939738743 23533797888431509409608115)
              ·
                refine ⟨35300696832647264114412173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23533797888431509409608115 35300696832647264114412173)
                ·
                  refine ⟨13237761312242724042904565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35300696832647264114412173 13237761312242724042904565)
                  ·
                    refine ⟨1241040123022755379022303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13237761312242724042904565 1241040123022755379022303)
                    ·
                      rfl

theorem cell23_7250751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_7250751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250751 prefixEnd_7250751 := by exact prefixLift 7250751
  have htrace : WordTrace (prefixWord ++ tailWord_7250751) baseStart_7250751 baseEnd_7250751 := by
    simpa [prefixWord, tailWord_7250751, baseEnd_7250751] using wordTrace_append hprefix tailTrace_7250751
  have hstable : (prefixWord ++ tailWord_7250751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250751).length < 2 ^ (prefixWord ++ tailWord_7250751).sum := by decide
  have hdescent : baseEnd_7250751 < baseStart_7250751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250771 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 4]
def baseStart_7250771 : Nat := 118140960795 + 7250771 * 2 ^ 59
def prefixEnd_7250771 : Nat := 4983230072969 + 3 ^ 40 * 7250771 * 2
def baseEnd_7250771 : Nat := 3723130638681356058816817

theorem tailTrace_7250771 : CollatzResearch.WordTrace tailWord_7250771 prefixEnd_7250771 3723130638681356058816817 := by
  unfold tailWord_7250771
  simp only [CollatzResearch.WordTrace]
  refine ⟨264457344414702474943176167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176304896276468316628784111 264457344414702474943176167)
  ·
    refine ⟨396686016622053712414764251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264457344414702474943176167 396686016622053712414764251)
    ·
      refine ⟨595029024933080568622146377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396686016622053712414764251 595029024933080568622146377)
      ·
        refine ⟨446271768699810426466609783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595029024933080568622146377 446271768699810426466609783)
        ·
          refine ⟨669407653049715639699914675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446271768699810426466609783 669407653049715639699914675)
          ·
            refine ⟨1004111479574573459549872013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669407653049715639699914675 1004111479574573459549872013)
            ·
              refine ⟨376541804840465047331202005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1004111479574573459549872013 376541804840465047331202005)
              ·
                refine ⟨8825198550948399546825047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 376541804840465047331202005 8825198550948399546825047)
                ·
                  refine ⟨13237797826422599320237571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8825198550948399546825047 13237797826422599320237571)
                  ·
                    refine ⟨19856696739633898980356357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13237797826422599320237571 19856696739633898980356357)
                    ·
                      refine ⟨3723130638681356058816817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19856696739633898980356357 3723130638681356058816817)
                      ·
                        rfl

theorem cell23_7250771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 4].length) (baseStart_7250771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250771 prefixEnd_7250771 := by exact prefixLift 7250771
  have htrace : WordTrace (prefixWord ++ tailWord_7250771) baseStart_7250771 baseEnd_7250771 := by
    simpa [prefixWord, tailWord_7250771, baseEnd_7250771] using wordTrace_append hprefix tailTrace_7250771
  have hstable : (prefixWord ++ tailWord_7250771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250771).length < 2 ^ (prefixWord ++ tailWord_7250771).sum := by decide
  have hdescent : baseEnd_7250771 < baseStart_7250771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250801 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_7250801 : Nat := 118140960795 + 7250801 * 2 ^ 59
def prefixEnd_7250801 : Nat := 4983230072969 + 3 ^ 40 * 7250801 * 2
def baseEnd_7250801 : Nat := 3723146043100990941441679

theorem tailTrace_7250801 : CollatzResearch.WordTrace tailWord_7250801 prefixEnd_7250801 3723146043100990941441679 := by
  unfold tailWord_7250801
  simp only [CollatzResearch.WordTrace]
  refine ⟨264458438604593790066768257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176305625736395860044512171 264458438604593790066768257)
  ·
    refine ⟨198343828953445342550076193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264458438604593790066768257 198343828953445342550076193)
    ·
      refine ⟨148757871715084006912557145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198343828953445342550076193 148757871715084006912557145)
      ·
        refine ⟨111568403786313005184417859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148757871715084006912557145 111568403786313005184417859)
        ·
          refine ⟨167352605679469507776626789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111568403786313005184417859 167352605679469507776626789)
          ·
            refine ⟨31378613564900532708117523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167352605679469507776626789 31378613564900532708117523)
            ·
              refine ⟨47067920347350799062176285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31378613564900532708117523 47067920347350799062176285)
              ·
                refine ⟨17650470130256549648316107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47067920347350799062176285 17650470130256549648316107)
                ·
                  refine ⟨26475705195384824472474161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17650470130256549648316107 26475705195384824472474161)
                  ·
                    refine ⟨19856778896538618354355621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26475705195384824472474161 19856778896538618354355621)
                    ·
                      refine ⟨3723146043100990941441679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19856778896538618354355621 3723146043100990941441679)
                      ·
                        rfl

theorem cell23_7250801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_7250801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250801 prefixEnd_7250801 := by exact prefixLift 7250801
  have htrace : WordTrace (prefixWord ++ tailWord_7250801) baseStart_7250801 baseEnd_7250801 := by
    simpa [prefixWord, tailWord_7250801, baseEnd_7250801] using wordTrace_append hprefix tailTrace_7250801
  have hstable : (prefixWord ++ tailWord_7250801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250801).length < 2 ^ (prefixWord ++ tailWord_7250801).sum := by decide
  have hdescent : baseEnd_7250801 < baseStart_7250801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250805 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_7250805 : Nat := 118140960795 + 7250805 * 2 ^ 59
def prefixEnd_7250805 : Nat := 4983230072969 + 3 ^ 40 * 7250805 * 2
def baseEnd_7250805 : Nat := 3723148097023608925791661

theorem tailTrace_7250805 : CollatzResearch.WordTrace tailWord_7250805 prefixEnd_7250805 3723148097023608925791661 := by
  unfold tailWord_7250805
  simp only [CollatzResearch.WordTrace]
  refine ⟨264458584496579298749913869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176305722997719532499942579 264458584496579298749913869)
  ·
    refine ⟨99171969186217237031217701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264458584496579298749913869 99171969186217237031217701)
    ·
      refine ⟨18594744222415731943353319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99171969186217237031217701 18594744222415731943353319)
      ·
        refine ⟨27892116333623597915029979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18594744222415731943353319 27892116333623597915029979)
        ·
          refine ⟨41838174500435396872544969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27892116333623597915029979 41838174500435396872544969)
          ·
            refine ⟨31378630875326547654408727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41838174500435396872544969 31378630875326547654408727)
            ·
              refine ⟨47067946312989821481613091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31378630875326547654408727 47067946312989821481613091)
              ·
                refine ⟨70601919469484732222419637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47067946312989821481613091 70601919469484732222419637)
                ·
                  refine ⟨6618929950264193645851841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70601919469484732222419637 6618929950264193645851841)
                  ·
                    refine ⟨4964197462698145234388881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6618929950264193645851841 4964197462698145234388881)
                    ·
                      refine ⟨3723148097023608925791661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964197462698145234388881 3723148097023608925791661)
                      ·
                        rfl

theorem cell23_7250805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_7250805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250805 prefixEnd_7250805 := by exact prefixLift 7250805
  have htrace : WordTrace (prefixWord ++ tailWord_7250805) baseStart_7250805 baseEnd_7250805 := by
    simpa [prefixWord, tailWord_7250805, baseEnd_7250805] using wordTrace_append hprefix tailTrace_7250805
  have hstable : (prefixWord ++ tailWord_7250805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250805).length < 2 ^ (prefixWord ++ tailWord_7250805).sum := by decide
  have hdescent : baseEnd_7250805 < baseStart_7250805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250825 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 1, 2, 3]
def baseStart_7250825 : Nat := 118140960795 + 7250825 * 2 ^ 59
def prefixEnd_7250825 : Nat := 4983230072969 + 3 ^ 40 * 7250825 * 2
def baseEnd_7250825 : Nat := 3723158366636698847541569

theorem tailTrace_7250825 : CollatzResearch.WordTrace tailWord_7250825 prefixEnd_7250825 3723158366636698847541569 := by
  unfold tailWord_7250825
  simp only [CollatzResearch.WordTrace]
  refine ⟨264459313956506842165641929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176306209304337894777094619 264459313956506842165641929)
  ·
    refine ⟨198344485467380131624231447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264459313956506842165641929 198344485467380131624231447)
    ·
      refine ⟨297516728201070197436347171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198344485467380131624231447 297516728201070197436347171)
      ·
        refine ⟨446275092301605296154520757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297516728201070197436347171 446275092301605296154520757)
        ·
          refine ⟨41838289903275496514486321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 446275092301605296154520757 41838289903275496514486321)
          ·
            refine ⟨31378717427456622385864741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41838289903275496514486321 31378717427456622385864741)
            ·
              refine ⟨5883509517648116697349639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31378717427456622385864741 5883509517648116697349639)
              ·
                refine ⟨8825264276472175046024459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5883509517648116697349639 8825264276472175046024459)
                ·
                  refine ⟨13237896414708262569036689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8825264276472175046024459 13237896414708262569036689)
                  ·
                    refine ⟨9928422311031196926777517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13237896414708262569036689 9928422311031196926777517)
                    ·
                      refine ⟨3723158366636698847541569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9928422311031196926777517 3723158366636698847541569)
                      ·
                        rfl

theorem cell23_7250825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 2, 3].length) (baseStart_7250825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250825 prefixEnd_7250825 := by exact prefixLift 7250825
  have htrace : WordTrace (prefixWord ++ tailWord_7250825) baseStart_7250825 baseEnd_7250825 := by
    simpa [prefixWord, tailWord_7250825, baseEnd_7250825] using wordTrace_append hprefix tailTrace_7250825
  have hstable : (prefixWord ++ tailWord_7250825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250825).length < 2 ^ (prefixWord ++ tailWord_7250825).sum := by decide
  have hdescent : baseEnd_7250825 < baseStart_7250825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250848 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 5, 3, 2]
def baseStart_7250848 : Nat := 118140960795 + 7250848 * 2 ^ 59
def prefixEnd_7250848 : Nat := 4983230072969 + 3 ^ 40 * 7250848 * 2
def baseEnd_7250848 : Nat := 3723170176691752257553963

theorem tailTrace_7250848 : CollatzResearch.WordTrace tailWord_7250848 prefixEnd_7250848 3723170176691752257553963 := by
  unfold tailWord_7250848
  simp only [CollatzResearch.WordTrace]
  refine ⟨132230076417711758546864599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176306768556949011395819465 132230076417711758546864599)
  ·
    refine ⟨198345114626567637820296899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132230076417711758546864599 198345114626567637820296899)
    ·
      refine ⟨297517671939851456730445349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198345114626567637820296899 297517671939851456730445349)
      ·
        refine ⟨55784563488722148136958503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297517671939851456730445349 55784563488722148136958503)
        ·
          refine ⟨83676845233083222205437755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55784563488722148136958503 83676845233083222205437755)
          ·
            refine ⟨125515267849624833308156633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83676845233083222205437755 125515267849624833308156633)
            ·
              refine ⟨94136450887218624981117475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125515267849624833308156633 94136450887218624981117475)
              ·
                refine ⟨141204676330827937471676213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94136450887218624981117475 141204676330827937471676213)
                ·
                  refine ⟨13237938406015119137969645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141204676330827937471676213 13237938406015119137969645)
                  ·
                    refine ⟨4964226902255669676738617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13237938406015119137969645 4964226902255669676738617)
                    ·
                      refine ⟨3723170176691752257553963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964226902255669676738617 3723170176691752257553963)
                      ·
                        rfl

theorem cell23_7250848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_7250848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250848 prefixEnd_7250848 := by exact prefixLift 7250848
  have htrace : WordTrace (prefixWord ++ tailWord_7250848) baseStart_7250848 baseEnd_7250848 := by
    simpa [prefixWord, tailWord_7250848, baseEnd_7250848] using wordTrace_append hprefix tailTrace_7250848
  have hstable : (prefixWord ++ tailWord_7250848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250848).length < 2 ^ (prefixWord ++ tailWord_7250848).sum := by decide
  have hdescent : baseEnd_7250848 < baseStart_7250848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250895 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 4, 2, 2]
def baseStart_7250895 : Nat := 118140960795 + 7250895 * 2 ^ 59
def prefixEnd_7250895 : Nat := 4983230072969 + 3 ^ 40 * 7250895 * 2
def baseEnd_7250895 : Nat := 3723194310282513573666247

theorem tailTrace_7250895 : CollatzResearch.WordTrace tailWord_7250895 prefixEnd_7250895 3723194310282513573666247 := by
  unfold tailWord_7250895
  simp only [CollatzResearch.WordTrace]
  refine ⟨264461867066253244120690139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176307911377502162747126759 264461867066253244120690139)
  ·
    refine ⟨396692800599379866181035209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264461867066253244120690139 396692800599379866181035209)
    ·
      refine ⟨297519600449534899635776407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396692800599379866181035209 297519600449534899635776407)
      ·
        refine ⟨446279400674302349453664611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297519600449534899635776407 446279400674302349453664611)
        ·
          refine ⟨669419101011453524180496917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446279400674302349453664611 669419101011453524180496917)
          ·
            refine ⟨31379020359911883945960793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 669419101011453524180496917 31379020359911883945960793)
            ·
              refine ⟨23534265269933912959470595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31379020359911883945960793 23534265269933912959470595)
              ·
                refine ⟨35301397904900869439205893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23534265269933912959470595 35301397904900869439205893)
                ·
                  refine ⟨6619012107168913019851105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35301397904900869439205893 6619012107168913019851105)
                  ·
                    refine ⟨4964259080376684764888329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6619012107168913019851105 4964259080376684764888329)
                    ·
                      refine ⟨3723194310282513573666247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964259080376684764888329 3723194310282513573666247)
                      ·
                        rfl

theorem cell23_7250895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 2, 2].length) (baseStart_7250895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250895 prefixEnd_7250895 := by exact prefixLift 7250895
  have htrace : WordTrace (prefixWord ++ tailWord_7250895) baseStart_7250895 baseEnd_7250895 := by
    simpa [prefixWord, tailWord_7250895, baseEnd_7250895] using wordTrace_append hprefix tailTrace_7250895
  have hstable : (prefixWord ++ tailWord_7250895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250895).length < 2 ^ (prefixWord ++ tailWord_7250895).sum := by decide
  have hdescent : baseEnd_7250895 < baseStart_7250895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250938 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2]
def baseStart_7250938 : Nat := 118140960795 + 7250938 * 2 ^ 59
def prefixEnd_7250938 : Nat := 4983230072969 + 3 ^ 40 * 7250938 * 2
def baseEnd_7250938 : Nat := 3723216389950656905428549

theorem tailTrace_7250938 : CollatzResearch.WordTrace tailWord_7250938 prefixEnd_7250938 3723216389950656905428549 := by
  unfold tailWord_7250938
  simp only [CollatzResearch.WordTrace]
  refine ⟨66115858851274365616126367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176308956936731641643003645 66115858851274365616126367)
  ·
    refine ⟨99173788276911548424189551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66115858851274365616126367 99173788276911548424189551)
    ·
      refine ⟨148760682415367322636284327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99173788276911548424189551 148760682415367322636284327)
      ·
        refine ⟨223141023623050983954426491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148760682415367322636284327 223141023623050983954426491)
        ·
          refine ⟨334711535434576475931639737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223141023623050983954426491 334711535434576475931639737)
          ·
            refine ⟨251033651575932356948729803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334711535434576475931639737 251033651575932356948729803)
            ·
              refine ⟨376550477363898535423094705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251033651575932356948729803 376550477363898535423094705)
              ·
                refine ⟨282412858022923901567321029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376550477363898535423094705 282412858022923901567321029)
                ·
                  refine ⟨52952410879298231543872693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282412858022923901567321029 52952410879298231543872693)
                  ·
                    refine ⟨4964288519934209207238065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52952410879298231543872693 4964288519934209207238065)
                    ·
                      refine ⟨3723216389950656905428549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964288519934209207238065 3723216389950656905428549)
                      ·
                        rfl

theorem cell23_7250938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2].length) (baseStart_7250938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250938 prefixEnd_7250938 := by exact prefixLift 7250938
  have htrace : WordTrace (prefixWord ++ tailWord_7250938) baseStart_7250938 baseEnd_7250938 := by
    simpa [prefixWord, tailWord_7250938, baseEnd_7250938] using wordTrace_append hprefix tailTrace_7250938
  have hstable : (prefixWord ++ tailWord_7250938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250938).length < 2 ^ (prefixWord ++ tailWord_7250938).sum := by decide
  have hdescent : baseEnd_7250938 < baseStart_7250938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250952 : List Nat := [2, 1, 3, 2, 1, 5, 2, 2, 5]
def baseStart_7250952 : Nat := 118140960795 + 7250952 * 2 ^ 59
def prefixEnd_7250952 : Nat := 4983230072969 + 3 ^ 40 * 7250952 * 2
def baseEnd_7250952 : Nat := 413691508742202205628165

theorem tailTrace_7250952 : CollatzResearch.WordTrace tailWord_7250952 prefixEnd_7250952 413691508742202205628165 := by
  unfold tailWord_7250952
  simp only [CollatzResearch.WordTrace]
  refine ⟨132231973013523371427757555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176309297351364495237010073 132231973013523371427757555)
  ·
    refine ⟨198347959520285057141636333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132231973013523371427757555 198347959520285057141636333)
    ·
      refine ⟨74380484820106896428113625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198347959520285057141636333 74380484820106896428113625)
      ·
        refine ⟨55785363615080172321085219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74380484820106896428113625 55785363615080172321085219)
        ·
          refine ⟨83678045422620258481627829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55785363615080172321085219 83678045422620258481627829)
          ·
            refine ⟨7844816758370649232652609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83678045422620258481627829 7844816758370649232652609)
            ·
              refine ⟨5883612568777986924489457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7844816758370649232652609 5883612568777986924489457)
              ·
                refine ⟨4412709426583490193367093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5883612568777986924489457 4412709426583490193367093)
                ·
                  refine ⟨413691508742202205628165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4412709426583490193367093 413691508742202205628165)
                  ·
                    rfl

theorem cell23_7250952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 5].length) (baseStart_7250952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250952 prefixEnd_7250952 := by exact prefixLift 7250952
  have htrace : WordTrace (prefixWord ++ tailWord_7250952) baseStart_7250952 baseEnd_7250952 := by
    simpa [prefixWord, tailWord_7250952, baseEnd_7250952] using wordTrace_append hprefix tailTrace_7250952
  have hstable : (prefixWord ++ tailWord_7250952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250952).length < 2 ^ (prefixWord ++ tailWord_7250952).sum := by decide
  have hdescent : baseEnd_7250952 < baseStart_7250952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250958 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_7250958 : Nat := 118140960795 + 7250958 * 2 ^ 59
def prefixEnd_7250958 : Nat := 4983230072969 + 3 ^ 40 * 7250958 * 2
def baseEnd_7250958 : Nat := 3723226659563746827178457

theorem tailTrace_7250958 : CollatzResearch.WordTrace tailWord_7250958 prefixEnd_7250958 3723226659563746827178457 := by
  unfold tailWord_7250958
  simp only [CollatzResearch.WordTrace]
  refine ⟨33058020608128125735029191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176309443243350003920155685 33058020608128125735029191)
  ·
    refine ⟨49587030912192188602543787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33058020608128125735029191 49587030912192188602543787)
    ·
      refine ⟨74380546368288282903815681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49587030912192188602543787 74380546368288282903815681)
      ·
        refine ⟨55785409776216212177861761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74380546368288282903815681 55785409776216212177861761)
        ·
          refine ⟨41839057332162159133396321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55785409776216212177861761 41839057332162159133396321)
          ·
            refine ⟨31379292999121619350047241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41839057332162159133396321 31379292999121619350047241)
            ·
              refine ⟨23534469749341214512535431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31379292999121619350047241 23534469749341214512535431)
              ·
                refine ⟨35301704624011821768803147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23534469749341214512535431 35301704624011821768803147)
                ·
                  refine ⟨52952556936017732653204721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35301704624011821768803147 52952556936017732653204721)
                  ·
                    refine ⟨39714417702013299489903541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52952556936017732653204721 39714417702013299489903541)
                    ·
                      refine ⟨3723226659563746827178457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39714417702013299489903541 3723226659563746827178457)
                      ·
                        rfl

theorem cell23_7250958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_7250958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250958 prefixEnd_7250958 := by exact prefixLift 7250958
  have htrace : WordTrace (prefixWord ++ tailWord_7250958) baseStart_7250958 baseEnd_7250958 := by
    simpa [prefixWord, tailWord_7250958, baseEnd_7250958] using wordTrace_append hprefix tailTrace_7250958
  have hstable : (prefixWord ++ tailWord_7250958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250958).length < 2 ^ (prefixWord ++ tailWord_7250958).sum := by decide
  have hdescent : baseEnd_7250958 < baseStart_7250958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7250988 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 3]
def baseStart_7250988 : Nat := 118140960795 + 7250988 * 2 ^ 59
def prefixEnd_7250988 : Nat := 4983230072969 + 3 ^ 40 * 7250988 * 2
def baseEnd_7250988 : Nat := 3723242063983381709803319

theorem tailTrace_7250988 : CollatzResearch.WordTrace tailWord_7250988 prefixEnd_7250988 3723242063983381709803319 := by
  unfold tailWord_7250988
  simp only [CollatzResearch.WordTrace]
  refine ⟨132232629527458160501912809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176310172703277547335883745 132232629527458160501912809)
  ·
    refine ⟨99174472145593620376434607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132232629527458160501912809 99174472145593620376434607)
    ·
      refine ⟨148761708218390430564651911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99174472145593620376434607 148761708218390430564651911)
      ·
        refine ⟨223142562327585645846977867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148761708218390430564651911 223142562327585645846977867)
        ·
          refine ⟨334713843491378468770466801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223142562327585645846977867 334713843491378468770466801)
          ·
            refine ⟨251035382618533851577850101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334713843491378468770466801 251035382618533851577850101)
            ·
              refine ⟨23534567120487548585423447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251035382618533851577850101 23534567120487548585423447)
              ·
                refine ⟨35301850680731322878135171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23534567120487548585423447 35301850680731322878135171)
                ·
                  refine ⟨52952776021096984317202757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35301850680731322878135171 52952776021096984317202757)
                  ·
                    refine ⟨9928645503955684559475517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52952776021096984317202757 9928645503955684559475517)
                    ·
                      refine ⟨3723242063983381709803319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9928645503955684559475517 3723242063983381709803319)
                      ·
                        rfl

theorem cell23_7250988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_7250988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7250988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7250988 prefixEnd_7250988 := by exact prefixLift 7250988
  have htrace : WordTrace (prefixWord ++ tailWord_7250988) baseStart_7250988 baseEnd_7250988 := by
    simpa [prefixWord, tailWord_7250988, baseEnd_7250988] using wordTrace_append hprefix tailTrace_7250988
  have hstable : (prefixWord ++ tailWord_7250988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7250988).length < 2 ^ (prefixWord ++ tailWord_7250988).sum := by decide
  have hdescent : baseEnd_7250988 < baseStart_7250988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7250988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251011 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 8]
def baseStart_7251011 : Nat := 118140960795 + 7251011 * 2 ^ 59
def prefixEnd_7251011 : Nat := 4983230072969 + 3 ^ 40 * 7251011 * 2
def baseEnd_7251011 : Nat := 3723253874038435119815713

theorem tailTrace_7251011 : CollatzResearch.WordTrace tailWord_7251011 prefixEnd_7251011 3723253874038435119815713 := by
  unfold tailWord_7251011
  simp only [CollatzResearch.WordTrace]
  refine ⟨264466097933832995931912887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176310731955888663954608591 264466097933832995931912887)
  ·
    refine ⟨396699146900749493897869331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264466097933832995931912887 396699146900749493897869331)
    ·
      refine ⟨595048720351124240846803997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396699146900749493897869331 595048720351124240846803997)
      ·
        refine ⟨223143270131671590317551499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 595048720351124240846803997 223143270131671590317551499)
        ·
          refine ⟨334714905197507385476327249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223143270131671590317551499 334714905197507385476327249)
          ·
            refine ⟨251036178898130539107245437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334714905197507385476327249 251036178898130539107245437)
            ·
              refine ⟨94138567086798952165217039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251036178898130539107245437 94138567086798952165217039)
              ·
                refine ⟨141207850630198428247825559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94138567086798952165217039 141207850630198428247825559)
                ·
                  refine ⟨211811775945297642371738339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141207850630198428247825559 211811775945297642371738339)
                  ·
                    refine ⟨317717663917946463557607509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 211811775945297642371738339 317717663917946463557607509)
                    ·
                      refine ⟨3723253874038435119815713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 317717663917946463557607509 3723253874038435119815713)
                      ·
                        rfl

theorem cell23_7251011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_7251011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251011 prefixEnd_7251011 := by exact prefixLift 7251011
  have htrace : WordTrace (prefixWord ++ tailWord_7251011) baseStart_7251011 baseEnd_7251011 := by
    simpa [prefixWord, tailWord_7251011, baseEnd_7251011] using wordTrace_append hprefix tailTrace_7251011
  have hstable : (prefixWord ++ tailWord_7251011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251011).length < 2 ^ (prefixWord ++ tailWord_7251011).sum := by decide
  have hdescent : baseEnd_7251011 < baseStart_7251011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251045 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 1, 5, 2]
def baseStart_7251045 : Nat := 118140960795 + 7251045 * 2 ^ 59
def prefixEnd_7251045 : Nat := 4983230072969 + 3 ^ 40 * 7251045 * 2
def baseEnd_7251045 : Nat := 3723271332380687986790557

theorem tailTrace_7251045 : CollatzResearch.WordTrace tailWord_7251045 prefixEnd_7251045 3723271332380687986790557 := by
  unfold tailWord_7251045
  simp only [CollatzResearch.WordTrace]
  refine ⟨264467338015709819738650589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176311558677139879825767059 264467338015709819738650589)
  ·
    refine ⟨99175251755891182401993971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264467338015709819738650589 99175251755891182401993971)
    ·
      refine ⟨148762877633836773602990957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99175251755891182401993971 148762877633836773602990957)
      ·
        refine ⟨55786079112688790101121609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148762877633836773602990957 55786079112688790101121609)
        ·
          refine ⟨41839559334516592575841207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55786079112688790101121609 41839559334516592575841207)
          ·
            refine ⟨62759339001774888863761811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41839559334516592575841207 62759339001774888863761811)
            ·
              refine ⟨94139008502662333295642717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62759339001774888863761811 94139008502662333295642717)
              ·
                refine ⟨35302128188498374985866019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94139008502662333295642717 35302128188498374985866019)
                ·
                  refine ⟨52953192282747562478799029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35302128188498374985866019 52953192282747562478799029)
                  ·
                    refine ⟨4964361776507583982387409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52953192282747562478799029 4964361776507583982387409)
                    ·
                      refine ⟨3723271332380687986790557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964361776507583982387409 3723271332380687986790557)
                      ·
                        rfl

theorem cell23_7251045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_7251045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251045 prefixEnd_7251045 := by exact prefixLift 7251045
  have htrace : WordTrace (prefixWord ++ tailWord_7251045) baseStart_7251045 baseEnd_7251045 := by
    simpa [prefixWord, tailWord_7251045, baseEnd_7251045] using wordTrace_append hprefix tailTrace_7251045
  have hstable : (prefixWord ++ tailWord_7251045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251045).length < 2 ^ (prefixWord ++ tailWord_7251045).sum := by decide
  have hdescent : baseEnd_7251045 < baseStart_7251045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251102 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_7251102 : Nat := 118140960795 + 7251102 * 2 ^ 59
def prefixEnd_7251102 : Nat := 4983230072969 + 3 ^ 40 * 7251102 * 2
def baseEnd_7251102 : Nat := 1241100200259331421259265

theorem tailTrace_7251102 : CollatzResearch.WordTrace tailWord_7251102 prefixEnd_7251102 1241100200259331421259265 := by
  unfold tailWord_7251102
  simp only [CollatzResearch.WordTrace]
  refine ⟨33058677122062914809184445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176312944651002212315650373 33058677122062914809184445)
  ·
    refine ⟨12397003920773593053444167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33058677122062914809184445 12397003920773593053444167)
    ·
      refine ⟨18595505881160389580166251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12397003920773593053444167 18595505881160389580166251)
      ·
        refine ⟨27893258821740584370249377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18595505881160389580166251 27893258821740584370249377)
        ·
          refine ⟨20919944116305438277687033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27893258821740584370249377 20919944116305438277687033)
          ·
            refine ⟨15689958087229078708265275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20919944116305438277687033 15689958087229078708265275)
            ·
              refine ⟨23534937130843618062397913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15689958087229078708265275 23534937130843618062397913)
              ·
                refine ⟨17651202848132713546798435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23534937130843618062397913 17651202848132713546798435)
                ·
                  refine ⟨26476804272199070320197653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17651202848132713546798435 26476804272199070320197653)
                  ·
                    refine ⟨1241100200259331421259265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26476804272199070320197653 1241100200259331421259265)
                    ·
                      rfl

theorem cell23_7251102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_7251102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251102 prefixEnd_7251102 := by exact prefixLift 7251102
  have htrace : WordTrace (prefixWord ++ tailWord_7251102) baseStart_7251102 baseEnd_7251102 := by
    simpa [prefixWord, tailWord_7251102, baseEnd_7251102] using wordTrace_append hprefix tailTrace_7251102
  have hstable : (prefixWord ++ tailWord_7251102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251102).length < 2 ^ (prefixWord ++ tailWord_7251102).sum := by decide
  have hdescent : baseEnd_7251102 < baseStart_7251102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251105 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_7251105 : Nat := 118140960795 + 7251105 * 2 ^ 59
def prefixEnd_7251105 : Nat := 4983230072969 + 3 ^ 40 * 7251105 * 2
def baseEnd_7251105 : Nat := 3723302141219957752040281

theorem tailTrace_7251105 : CollatzResearch.WordTrace tailWord_7251105 prefixEnd_7251105 3723302141219957752040281 := by
  unfold tailWord_7251105
  simp only [CollatzResearch.WordTrace]
  refine ⟨264469526395492449985834769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176313017596994966657223179 264469526395492449985834769)
  ·
    refine ⟨198352144796619337489376077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264469526395492449985834769 198352144796619337489376077)
    ·
      refine ⟨74382054298732251558516029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198352144796619337489376077 74382054298732251558516029)
      ·
        refine ⟨27893270362024594334443511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74382054298732251558516029 27893270362024594334443511)
        ·
          refine ⟨41839905543036891501665267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27893270362024594334443511 41839905543036891501665267)
          ·
            refine ⟨62759858314555337252497901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41839905543036891501665267 62759858314555337252497901)
            ·
              refine ⟨23534946867958251469686713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62759858314555337252497901 23534946867958251469686713)
              ·
                refine ⟨17651210150968688602265035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23534946867958251469686713 17651210150968688602265035)
                ·
                  refine ⟨26476815226453032903397553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17651210150968688602265035 26476815226453032903397553)
                  ·
                    refine ⟨19857611419839774677548165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26476815226453032903397553 19857611419839774677548165)
                    ·
                      refine ⟨3723302141219957752040281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19857611419839774677548165 3723302141219957752040281)
                      ·
                        rfl

theorem cell23_7251105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_7251105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251105 prefixEnd_7251105 := by exact prefixLift 7251105
  have htrace : WordTrace (prefixWord ++ tailWord_7251105) baseStart_7251105 baseEnd_7251105 := by
    simpa [prefixWord, tailWord_7251105, baseEnd_7251105] using wordTrace_append hprefix tailTrace_7251105
  have hstable : (prefixWord ++ tailWord_7251105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251105).length < 2 ^ (prefixWord ++ tailWord_7251105).sum := by decide
  have hdescent : baseEnd_7251105 < baseStart_7251105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251169 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 1, 3, 2]
def baseStart_7251169 : Nat := 118140960795 + 7251169 * 2 ^ 59
def prefixEnd_7251169 : Nat := 4983230072969 + 3 ^ 40 * 7251169 * 2
def baseEnd_7251169 : Nat := 3723335003981845501639987

theorem tailTrace_7251169 : CollatzResearch.WordTrace tailWord_7251169 prefixEnd_7251169 3723335003981845501639987 := by
  unfold tailWord_7251169
  simp only [CollatzResearch.WordTrace]
  refine ⟨264471860667260588916164561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176314573778173725944109707 264471860667260588916164561)
  ·
    refine ⟨198353895500445441687123421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264471860667260588916164561 198353895500445441687123421)
    ·
      refine ⟨74382710812667040632671283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198353895500445441687123421 74382710812667040632671283)
      ·
        refine ⟨111574066219000560949006925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74382710812667040632671283 111574066219000560949006925)
        ·
          refine ⟨41840274832125210355877597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111574066219000560949006925 41840274832125210355877597)
          ·
            refine ⟨15690103062046953883454099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41840274832125210355877597 15690103062046953883454099)
            ·
              refine ⟨23535154593070430825181149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15690103062046953883454099 23535154593070430825181149)
              ·
                refine ⟨8825682972401411559442931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23535154593070430825181149 8825682972401411559442931)
                ·
                  refine ⟨13238524458602117339164397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8825682972401411559442931 13238524458602117339164397)
                  ·
                    refine ⟨4964446671975794002186649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13238524458602117339164397 4964446671975794002186649)
                    ·
                      refine ⟨3723335003981845501639987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964446671975794002186649 3723335003981845501639987)
                      ·
                        rfl

theorem cell23_7251169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_7251169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251169 prefixEnd_7251169 := by exact prefixLift 7251169
  have htrace : WordTrace (prefixWord ++ tailWord_7251169) baseStart_7251169 baseEnd_7251169 := by
    simpa [prefixWord, tailWord_7251169, baseEnd_7251169] using wordTrace_append hprefix tailTrace_7251169
  have hstable : (prefixWord ++ tailWord_7251169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251169).length < 2 ^ (prefixWord ++ tailWord_7251169).sum := by decide
  have hdescent : baseEnd_7251169 < baseStart_7251169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251182 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_7251182 : Nat := 118140960795 + 7251182 * 2 ^ 59
def prefixEnd_7251182 : Nat := 4983230072969 + 3 ^ 40 * 7251182 * 2
def baseEnd_7251182 : Nat := 3723341679230353950777427

theorem tailTrace_7251182 : CollatzResearch.WordTrace tailWord_7251182 prefixEnd_7251182 3723341679230353950777427 := by
  unfold tailWord_7251182
  simp only [CollatzResearch.WordTrace]
  refine ⟨33059041852026686517048475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176314889877475661424258533 33059041852026686517048475)
  ·
    refine ⟨49588562778040029775572713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33059041852026686517048475 49588562778040029775572713)
    ·
      refine ⟨37191422083530022331679535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49588562778040029775572713 37191422083530022331679535)
      ·
        refine ⟨55787133125295033497519303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37191422083530022331679535 55787133125295033497519303)
        ·
          refine ⟨83680699687942550246278955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55787133125295033497519303 83680699687942550246278955)
          ·
            refine ⟨125521049531913825369418433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83680699687942550246278955 125521049531913825369418433)
            ·
              refine ⟨94140787148935369027063825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125521049531913825369418433 94140787148935369027063825)
              ·
                refine ⟨70605590361701526770297869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94140787148935369027063825 70605590361701526770297869)
                ·
                  refine ⟨26477096385638072538861701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70605590361701526770297869 26477096385638072538861701)
                  ·
                    refine ⟨4964455572307138601036569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26477096385638072538861701 4964455572307138601036569)
                    ·
                      refine ⟨3723341679230353950777427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964455572307138601036569 3723341679230353950777427)
                      ·
                        rfl

theorem cell23_7251182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_7251182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251182 prefixEnd_7251182 := by exact prefixLift 7251182
  have htrace : WordTrace (prefixWord ++ tailWord_7251182) baseStart_7251182 baseEnd_7251182 := by
    simpa [prefixWord, tailWord_7251182, baseEnd_7251182] using wordTrace_append hprefix tailTrace_7251182
  have hstable : (prefixWord ++ tailWord_7251182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251182).length < 2 ^ (prefixWord ++ tailWord_7251182).sum := by decide
  have hdescent : baseEnd_7251182 < baseStart_7251182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251199 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 1, 4, 2]
def baseStart_7251199 : Nat := 118140960795 + 7251199 * 2 ^ 59
def prefixEnd_7251199 : Nat := 4983230072969 + 3 ^ 40 * 7251199 * 2
def baseEnd_7251199 : Nat := 3723350408401480384264849

theorem tailTrace_7251199 : CollatzResearch.WordTrace tailWord_7251199 prefixEnd_7251199 3723350408401480384264849 := by
  unfold tailWord_7251199
  simp only [CollatzResearch.WordTrace]
  refine ⟨264472954857151904039756651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176315303238101269359837767 264472954857151904039756651)
  ·
    refine ⟨396709432285727856059634977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264472954857151904039756651 396709432285727856059634977)
    ·
      refine ⟨297532074214295892044726233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396709432285727856059634977 297532074214295892044726233)
      ·
        refine ⟨223149055660721919033544675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297532074214295892044726233 223149055660721919033544675)
        ·
          refine ⟨334723583491082878550317013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223149055660721919033544675 334723583491082878550317013)
          ·
            refine ⟨7845083988072254966023055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 334723583491082878550317013 7845083988072254966023055)
            ·
              refine ⟨11767625982108382449034583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7845083988072254966023055 11767625982108382449034583)
              ·
                refine ⟨17651438973162573673551875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11767625982108382449034583 17651438973162573673551875)
                ·
                  refine ⟨26477158459743860510327813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17651438973162573673551875 26477158459743860510327813)
                  ·
                    refine ⟨4964467211201973845686465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26477158459743860510327813 4964467211201973845686465)
                    ·
                      refine ⟨3723350408401480384264849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964467211201973845686465 3723350408401480384264849)
                      ·
                        rfl

theorem cell23_7251199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 4, 2].length) (baseStart_7251199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251199 prefixEnd_7251199 := by exact prefixLift 7251199
  have htrace : WordTrace (prefixWord ++ tailWord_7251199) baseStart_7251199 baseEnd_7251199 := by
    simpa [prefixWord, tailWord_7251199, baseEnd_7251199] using wordTrace_append hprefix tailTrace_7251199
  have hstable : (prefixWord ++ tailWord_7251199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251199).length < 2 ^ (prefixWord ++ tailWord_7251199).sum := by decide
  have hdescent : baseEnd_7251199 < baseStart_7251199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251235 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 4, 5]
def baseStart_7251235 : Nat := 118140960795 + 7251235 * 2 ^ 59
def prefixEnd_7251235 : Nat := 4983230072969 + 3 ^ 40 * 7251235 * 2
def baseEnd_7251235 : Nat := 1241122964568347414471561

theorem tailTrace_7251235 : CollatzResearch.WordTrace tailWord_7251235 prefixEnd_7251235 1241122964568347414471561 := by
  unfold tailWord_7251235
  simp only [CollatzResearch.WordTrace]
  refine ⟨264474267885021482188067159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176316178590014321458711439 264474267885021482188067159)
  ·
    refine ⟨396711401827532223282100739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264474267885021482188067159 396711401827532223282100739)
    ·
      refine ⟨595067102741298334923151109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396711401827532223282100739 595067102741298334923151109)
      ·
        refine ⟨111575081763993437798090833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 595067102741298334923151109 111575081763993437798090833)
        ·
          refine ⟨83681311322995078348568125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111575081763993437798090833 83681311322995078348568125)
          ·
            refine ⟨31380491746123154380713047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83681311322995078348568125 31380491746123154380713047)
            ·
              refine ⟨47070737619184731571069571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31380491746123154380713047 47070737619184731571069571)
              ·
                refine ⟨70606106428777097356604357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47070737619184731571069571 70606106428777097356604357)
                ·
                  refine ⟨13238644955395705754363317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70606106428777097356604357 13238644955395705754363317)
                  ·
                    refine ⟨1241122964568347414471561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13238644955395705754363317 1241122964568347414471561)
                    ·
                      rfl

theorem cell23_7251235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 5].length) (baseStart_7251235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251235 prefixEnd_7251235 := by exact prefixLift 7251235
  have htrace : WordTrace (prefixWord ++ tailWord_7251235) baseStart_7251235 baseEnd_7251235 := by
    simpa [prefixWord, tailWord_7251235, baseEnd_7251235] using wordTrace_append hprefix tailTrace_7251235
  have hstable : (prefixWord ++ tailWord_7251235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251235).length < 2 ^ (prefixWord ++ tailWord_7251235).sum := by decide
  have hdescent : baseEnd_7251235 < baseStart_7251235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251252 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_7251252 : Nat := 118140960795 + 7251252 * 2 ^ 59
def prefixEnd_7251252 : Nat := 4983230072969 + 3 ^ 40 * 7251252 * 2
def baseEnd_7251252 : Nat := 1241125874292056225634035

theorem tailTrace_7251252 : CollatzResearch.WordTrace tailWord_7251252 prefixEnd_7251252 1241125874292056225634035 := by
  unfold tailWord_7251252
  simp only [CollatzResearch.WordTrace]
  refine ⟨132237443962979947045718005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176316591950639929394290673 132237443962979947045718005)
  ·
    refine ⟨12397260371529370035536063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132237443962979947045718005 12397260371529370035536063)
    ·
      refine ⟨18595890557294055053304095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12397260371529370035536063 18595890557294055053304095)
      ·
        refine ⟨27893835835941082579956143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18595890557294055053304095 27893835835941082579956143)
        ·
          refine ⟨41840753753911623869934215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27893835835941082579956143 41840753753911623869934215)
          ·
            refine ⟨62761130630867435804901323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41840753753911623869934215 62761130630867435804901323)
            ·
              refine ⟨94141695946301153707351985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62761130630867435804901323 94141695946301153707351985)
              ·
                refine ⟨70606271959725865280513989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94141695946301153707351985 70606271959725865280513989)
                ·
                  refine ⟨13238675992448599740096373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70606271959725865280513989 13238675992448599740096373)
                  ·
                    refine ⟨1241125874292056225634035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13238675992448599740096373 1241125874292056225634035)
                    ·
                      rfl

theorem cell23_7251252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_7251252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251252 prefixEnd_7251252 := by exact prefixLift 7251252
  have htrace : WordTrace (prefixWord ++ tailWord_7251252) baseStart_7251252 baseEnd_7251252 := by
    simpa [prefixWord, tailWord_7251252, baseEnd_7251252] using wordTrace_append hprefix tailTrace_7251252
  have hstable : (prefixWord ++ tailWord_7251252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251252).length < 2 ^ (prefixWord ++ tailWord_7251252).sum := by decide
  have hdescent : baseEnd_7251252 < baseStart_7251252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251272 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 4, 4, 2]
def baseStart_7251272 : Nat := 118140960795 + 7251272 * 2 ^ 59
def prefixEnd_7251272 : Nat := 4983230072969 + 3 ^ 40 * 7251272 * 2
def baseEnd_7251272 : Nat := 3723387892489258598652013

theorem tailTrace_7251272 : CollatzResearch.WordTrace tailWord_7251272 prefixEnd_7251272 3723387892489258598652013 := by
  unfold tailWord_7251272
  simp only [CollatzResearch.WordTrace]
  refine ⟨132237808692943718753582035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176317078257258291671442713 132237808692943718753582035)
  ·
    refine ⟨198356713039415578130373053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132237808692943718753582035 198356713039415578130373053)
    ·
      refine ⟨74383767389780841798889895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198356713039415578130373053 74383767389780841798889895)
      ·
        refine ⟨111575651084671262698334843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74383767389780841798889895 111575651084671262698334843)
        ·
          refine ⟨167363476627006894047502265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111575651084671262698334843 167363476627006894047502265)
          ·
            refine ⟨125522607470255170535626699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167363476627006894047502265 125522607470255170535626699)
            ·
              refine ⟨188283911205382755803440049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125522607470255170535626699 188283911205382755803440049)
              ·
                refine ⟨141212933404037066852580037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188283911205382755803440049 141212933404037066852580037)
                ·
                  refine ⟨26477425013256950034858757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141212933404037066852580037 26477425013256950034858757)
                  ·
                    refine ⟨4964517189985678131536017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26477425013256950034858757 4964517189985678131536017)
                    ·
                      refine ⟨3723387892489258598652013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964517189985678131536017 3723387892489258598652013)
                      ·
                        rfl

theorem cell23_7251272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_7251272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251272 prefixEnd_7251272 := by exact prefixLift 7251272
  have htrace : WordTrace (prefixWord ++ tailWord_7251272) baseStart_7251272 baseEnd_7251272 := by
    simpa [prefixWord, tailWord_7251272, baseEnd_7251272] using wordTrace_append hprefix tailTrace_7251272
  have hstable : (prefixWord ++ tailWord_7251272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251272).length < 2 ^ (prefixWord ++ tailWord_7251272).sum := by decide
  have hdescent : baseEnd_7251272 < baseStart_7251272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251275 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 3]
def baseStart_7251275 : Nat := 118140960795 + 7251275 * 2 ^ 59
def prefixEnd_7251275 : Nat := 4983230072969 + 3 ^ 40 * 7251275 * 2
def baseEnd_7251275 : Nat := 3723389432931222086914499

theorem tailTrace_7251275 : CollatzResearch.WordTrace tailWord_7251275 prefixEnd_7251275 3723389432931222086914499 := by
  unfold tailWord_7251275
  simp only [CollatzResearch.WordTrace]
  refine ⟨264475726804876569019523279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176317151203251046013015519 264475726804876569019523279)
  ·
    refine ⟨396713590207314853529284919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264475726804876569019523279 396713590207314853529284919)
    ·
      refine ⟨595070385310972280293927379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396713590207314853529284919 595070385310972280293927379)
      ·
        refine ⟨892605577966458420440891069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595070385310972280293927379 892605577966458420440891069)
        ·
          refine ⟨334727091737421907665334151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 892605577966458420440891069 334727091737421907665334151)
          ·
            refine ⟨502090637606132861498001227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334727091737421907665334151 502090637606132861498001227)
            ·
              refine ⟨753135956409199292247001841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502090637606132861498001227 753135956409199292247001841)
              ·
                refine ⟨564851967306899469185251381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753135956409199292247001841 564851967306899469185251381)
                ·
                  refine ⟨52954871935021825236117317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 564851967306899469185251381 52954871935021825236117317)
                  ·
                    refine ⟨9929038487816592231771997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52954871935021825236117317 9929038487816592231771997)
                    ·
                      refine ⟨3723389432931222086914499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9929038487816592231771997 3723389432931222086914499)
                      ·
                        rfl

theorem cell23_7251275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 3].length) (baseStart_7251275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251275 prefixEnd_7251275 := by exact prefixLift 7251275
  have htrace : WordTrace (prefixWord ++ tailWord_7251275) baseStart_7251275 baseEnd_7251275 := by
    simpa [prefixWord, tailWord_7251275, baseEnd_7251275] using wordTrace_append hprefix tailTrace_7251275
  have hstable : (prefixWord ++ tailWord_7251275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251275).length < 2 ^ (prefixWord ++ tailWord_7251275).sum := by decide
  have hdescent : baseEnd_7251275 < baseStart_7251275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251306 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_7251306 : Nat := 118140960795 + 7251306 * 2 ^ 59
def prefixEnd_7251306 : Nat := 4983230072969 + 3 ^ 40 * 7251306 * 2
def baseEnd_7251306 : Nat := 3723405350831511465626857

theorem tailTrace_7251306 : CollatzResearch.WordTrace tailWord_7251306 prefixEnd_7251306 3723405350831511465626857 := by
  unfold tailWord_7251306
  simp only [CollatzResearch.WordTrace]
  refine ⟨66119214366941065328475443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176317904978509507542601181 66119214366941065328475443)
  ·
    refine ⟨99178821550411597992713165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66119214366941065328475443 99178821550411597992713165)
    ·
      refine ⟨37192058081404349247267437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99178821550411597992713165 37192058081404349247267437)
      ·
        refine ⟨13947021780526630967725289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37192058081404349247267437 13947021780526630967725289)
        ·
          refine ⟨10460266335394973225793967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13947021780526630967725289 10460266335394973225793967)
          ·
            refine ⟨15690399503092459838690951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10460266335394973225793967 15690399503092459838690951)
            ·
              refine ⟨23535599254638689758036427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15690399503092459838690951 23535599254638689758036427)
              ·
                refine ⟨35303398881958034637054641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23535599254638689758036427 35303398881958034637054641)
                ·
                  refine ⟨26477549161468525977790981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35303398881958034637054641 26477549161468525977790981)
                  ·
                    refine ⟨4964540467775348620835809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26477549161468525977790981 4964540467775348620835809)
                    ·
                      refine ⟨3723405350831511465626857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964540467775348620835809 3723405350831511465626857)
                      ·
                        rfl

theorem cell23_7251306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_7251306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251306 prefixEnd_7251306 := by exact prefixLift 7251306
  have htrace : WordTrace (prefixWord ++ tailWord_7251306) baseStart_7251306 baseEnd_7251306 := by
    simpa [prefixWord, tailWord_7251306, baseEnd_7251306] using wordTrace_append hprefix tailTrace_7251306
  have hstable : (prefixWord ++ tailWord_7251306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251306).length < 2 ^ (prefixWord ++ tailWord_7251306).sum := by decide
  have hdescent : baseEnd_7251306 < baseStart_7251306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251349 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 2, 3, 2]
def baseStart_7251349 : Nat := 118140960795 + 7251349 * 2 ^ 59
def prefixEnd_7251349 : Nat := 4983230072969 + 3 ^ 40 * 7251349 * 2
def baseEnd_7251349 : Nat := 3723427430499654797389159

theorem tailTrace_7251349 : CollatzResearch.WordTrace tailWord_7251349 prefixEnd_7251349 3723427430499654797389159 := by
  unfold tailWord_7251349
  simp only [CollatzResearch.WordTrace]
  refine ⟨264478425806608479657717101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176318950537738986438478067 264478425806608479657717101)
  ·
    refine ⟨99179409677478179871643913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264478425806608479657717101 99179409677478179871643913)
    ·
      refine ⟨74384557258108634903732935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99179409677478179871643913 74384557258108634903732935)
      ·
        refine ⟨111576835887162952355599403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74384557258108634903732935 111576835887162952355599403)
        ·
          refine ⟨167365253830744428533399105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111576835887162952355599403 167365253830744428533399105)
          ·
            refine ⟨125523940373058321400049329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167365253830744428533399105 125523940373058321400049329)
            ·
              refine ⟨94142955279793741050036997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125523940373058321400049329 94142955279793741050036997)
              ·
                refine ⟨17651804114961326446881937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94142955279793741050036997 17651804114961326446881937)
                ·
                  refine ⟨13238853086220994835161453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17651804114961326446881937 13238853086220994835161453)
                  ·
                    refine ⟨4964569907332873063185545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13238853086220994835161453 4964569907332873063185545)
                    ·
                      refine ⟨3723427430499654797389159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964569907332873063185545 3723427430499654797389159)
                      ·
                        rfl

theorem cell23_7251349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_7251349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251349 prefixEnd_7251349 := by exact prefixLift 7251349
  have htrace : WordTrace (prefixWord ++ tailWord_7251349) baseStart_7251349 baseEnd_7251349 := by
    simpa [prefixWord, tailWord_7251349, baseEnd_7251349] using wordTrace_append hprefix tailTrace_7251349
  have hstable : (prefixWord ++ tailWord_7251349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251349).length < 2 ^ (prefixWord ++ tailWord_7251349).sum := by decide
  have hdescent : baseEnd_7251349 < baseStart_7251349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251372 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 1, 6]
def baseStart_7251372 : Nat := 118140960795 + 7251372 * 2 ^ 59
def prefixEnd_7251372 : Nat := 4983230072969 + 3 ^ 40 * 7251372 * 2
def baseEnd_7251372 : Nat := 1241146413518236069133851

theorem tailTrace_7251372 : CollatzResearch.WordTrace tailWord_7251372 prefixEnd_7251372 1241146413518236069133851 := by
  unfold tailWord_7251372
  simp only [CollatzResearch.WordTrace]
  refine ⟨132239632342762577292902185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176319509790350103057202913 132239632342762577292902185)
  ·
    refine ⟨99179724257071932969676639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132239632342762577292902185 99179724257071932969676639)
    ·
      refine ⟨148769586385607899454514959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99179724257071932969676639 148769586385607899454514959)
      ·
        refine ⟨223154379578411849181772439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148769586385607899454514959 223154379578411849181772439)
        ·
          refine ⟨334731569367617773772658659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223154379578411849181772439 334731569367617773772658659)
          ·
            refine ⟨502097354051426660658987989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334731569367617773772658659 502097354051426660658987989)
            ·
              refine ⟨11767906735580312359195031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 502097354051426660658987989 11767906735580312359195031)
              ·
                refine ⟨17651860103370468538792547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11767906735580312359195031 17651860103370468538792547)
                ·
                  refine ⟨26477790155055702808188821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17651860103370468538792547 26477790155055702808188821)
                  ·
                    refine ⟨1241146413518236069133851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26477790155055702808188821 1241146413518236069133851)
                    ·
                      rfl

theorem cell23_7251372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_7251372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251372 prefixEnd_7251372 := by exact prefixLift 7251372
  have htrace : WordTrace (prefixWord ++ tailWord_7251372) baseStart_7251372 baseEnd_7251372 := by
    simpa [prefixWord, tailWord_7251372, baseEnd_7251372] using wordTrace_append hprefix tailTrace_7251372
  have hstable : (prefixWord ++ tailWord_7251372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251372).length < 2 ^ (prefixWord ++ tailWord_7251372).sum := by decide
  have hdescent : baseEnd_7251372 < baseStart_7251372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251392 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 4]
def baseStart_7251392 : Nat := 118140960795 + 7251392 * 2 ^ 59
def prefixEnd_7251392 : Nat := 4983230072969 + 3 ^ 40 * 7251392 * 2
def baseEnd_7251392 : Nat := 3723449510167798129151461

theorem tailTrace_7251392 : CollatzResearch.WordTrace tailWord_7251392 prefixEnd_7251392 3723449510167798129151461 := by
  unfold tailWord_7251392
  simp only [CollatzResearch.WordTrace]
  refine ⟨132239997072726349000766215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176319996096968465334354953 132239997072726349000766215)
  ·
    refine ⟨198359995609089523501149323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132239997072726349000766215 198359995609089523501149323)
    ·
      refine ⟨297539993413634285251723985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198359995609089523501149323 297539993413634285251723985)
      ·
        refine ⟨223154995060225713938792989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297539993413634285251723985 223154995060225713938792989)
        ·
          refine ⟨83683123147584642727047371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223154995060225713938792989 83683123147584642727047371)
          ·
            refine ⟨125524684721376964090571057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83683123147584642727047371 125524684721376964090571057)
            ·
              refine ⟨94143513541032723067928293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125524684721376964090571057 94143513541032723067928293)
              ·
                refine ⟨17651908788943635575236555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94143513541032723067928293 17651908788943635575236555)
                ·
                  refine ⟨26477863183415453362854833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17651908788943635575236555 26477863183415453362854833)
                  ·
                    refine ⟨19858397387561590022141125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26477863183415453362854833 19858397387561590022141125)
                    ·
                      refine ⟨3723449510167798129151461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19858397387561590022141125 3723449510167798129151461)
                      ·
                        rfl

theorem cell23_7251392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_7251392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251392 prefixEnd_7251392 := by exact prefixLift 7251392
  have htrace : WordTrace (prefixWord ++ tailWord_7251392) baseStart_7251392 baseEnd_7251392 := by
    simpa [prefixWord, tailWord_7251392, baseEnd_7251392] using wordTrace_append hprefix tailTrace_7251392
  have hstable : (prefixWord ++ tailWord_7251392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251392).length < 2 ^ (prefixWord ++ tailWord_7251392).sum := by decide
  have hdescent : baseEnd_7251392 < baseStart_7251392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251396 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_7251396 : Nat := 118140960795 + 7251396 * 2 ^ 59
def prefixEnd_7251396 : Nat := 4983230072969 + 3 ^ 40 * 7251396 * 2
def baseEnd_7251396 : Nat := 3723451564090416113501443

theorem tailTrace_7251396 : CollatzResearch.WordTrace tailWord_7251396 prefixEnd_7251396 3723451564090416113501443 := by
  unfold tailWord_7251396
  simp only [CollatzResearch.WordTrace]
  refine ⟨132240070018719103342339021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176320093358292137789785361 132240070018719103342339021)
  ·
    refine ⟨49590026257019663753377133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132240070018719103342339021 49590026257019663753377133)
    ·
      refine ⟨18596259846382373907516425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49590026257019663753377133 18596259846382373907516425)
      ·
        refine ⟨13947194884786780430637319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18596259846382373907516425 13947194884786780430637319)
        ·
          refine ⟨20920792327180170645955979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13947194884786780430637319 20920792327180170645955979)
          ·
            refine ⟨31381188490770255968933969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20920792327180170645955979 31381188490770255968933969)
            ·
              refine ⟨23535891368077691976700477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31381188490770255968933969 23535891368077691976700477)
              ·
                refine ⟨8825959263029134491262679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23535891368077691976700477 8825959263029134491262679)
                ·
                  refine ⟨13238938894543701736894019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8825959263029134491262679 13238938894543701736894019)
                  ·
                    refine ⟨19858408341815552605341029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13238938894543701736894019 19858408341815552605341029)
                    ·
                      refine ⟨3723451564090416113501443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19858408341815552605341029 3723451564090416113501443)
                      ·
                        rfl

theorem cell23_7251396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_7251396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251396 prefixEnd_7251396 := by exact prefixLift 7251396
  have htrace : WordTrace (prefixWord ++ tailWord_7251396) baseStart_7251396 baseEnd_7251396 := by
    simpa [prefixWord, tailWord_7251396, baseEnd_7251396] using wordTrace_append hprefix tailTrace_7251396
  have hstable : (prefixWord ++ tailWord_7251396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251396).length < 2 ^ (prefixWord ++ tailWord_7251396).sum := by decide
  have hdescent : baseEnd_7251396 < baseStart_7251396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251399 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_7251399 : Nat := 118140960795 + 7251399 * 2 ^ 59
def prefixEnd_7251399 : Nat := 4983230072969 + 3 ^ 40 * 7251399 * 2
def baseEnd_7251399 : Nat := 3723453104532379601763929

theorem tailTrace_7251399 : CollatzResearch.WordTrace tailWord_7251399 prefixEnd_7251399 3723453104532379601763929 := by
  unfold tailWord_7251399
  simp only [CollatzResearch.WordTrace]
  refine ⟨264480249456427338197037251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176320166304284892131358167 264480249456427338197037251)
  ·
    refine ⟨396720374184641007295555877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264480249456427338197037251 396720374184641007295555877)
    ·
      refine ⟨74385070159620188867916727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396720374184641007295555877 74385070159620188867916727)
      ·
        refine ⟨111577605239430283301875091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74385070159620188867916727 111577605239430283301875091)
        ·
          refine ⟨167366407859145424952812637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111577605239430283301875091 167366407859145424952812637)
          ·
            refine ⟨62762402947179534357304739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167366407859145424952812637 62762402947179534357304739)
            ·
              refine ⟨94143604420769301535957109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62762402947179534357304739 94143604420769301535957109)
              ·
                refine ⟨8825962914447122018995979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94143604420769301535957109 8825962914447122018995979)
                ·
                  refine ⟨13238944371670683028493969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8825962914447122018995979 13238944371670683028493969)
                  ·
                    refine ⟨9929208278753012271370477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13238944371670683028493969 9929208278753012271370477)
                    ·
                      refine ⟨3723453104532379601763929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9929208278753012271370477 3723453104532379601763929)
                      ·
                        rfl

theorem cell23_7251399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_7251399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251399 prefixEnd_7251399 := by exact prefixLift 7251399
  have htrace : WordTrace (prefixWord ++ tailWord_7251399) baseStart_7251399 baseEnd_7251399 := by
    simpa [prefixWord, tailWord_7251399, baseEnd_7251399] using wordTrace_append hprefix tailTrace_7251399
  have hstable : (prefixWord ++ tailWord_7251399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251399).length < 2 ^ (prefixWord ++ tailWord_7251399).sum := by decide
  have hdescent : baseEnd_7251399 < baseStart_7251399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251402 : List Nat := [3, 1, 2, 1, 2, 5, 9]
def baseStart_7251402 : Nat := 118140960795 + 7251402 * 2 ^ 59
def prefixEnd_7251402 : Nat := 4983230072969 + 3 ^ 40 * 7251402 * 2
def baseEnd_7251402 : Nat := 45968575863880778889215

theorem tailTrace_7251402 : CollatzResearch.WordTrace tailWord_7251402 prefixEnd_7251402 45968575863880778889215 := by
  unfold tailWord_7251402
  simp only [CollatzResearch.WordTrace]
  refine ⟨66120089718854117427349115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176320239250277646472930973 66120089718854117427349115)
  ·
    refine ⟨99180134578281176141023673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66120089718854117427349115 99180134578281176141023673)
    ·
      refine ⟨74385100933710882105767755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99180134578281176141023673 74385100933710882105767755)
      ·
        refine ⟨111577651400566323158651633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74385100933710882105767755 111577651400566323158651633)
        ·
          refine ⟨83683238550424742368988725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111577651400566323158651633 83683238550424742368988725)
          ·
            refine ⟨7845303614102319597092693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83683238550424742368988725 7845303614102319597092693)
            ·
              refine ⟨45968575863880778889215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7845303614102319597092693 45968575863880778889215)
              ·
                rfl

theorem cell23_7251402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 9].length) (baseStart_7251402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251402 prefixEnd_7251402 := by exact prefixLift 7251402
  have htrace : WordTrace (prefixWord ++ tailWord_7251402) baseStart_7251402 baseEnd_7251402 := by
    simpa [prefixWord, tailWord_7251402, baseEnd_7251402] using wordTrace_append hprefix tailTrace_7251402
  have hstable : (prefixWord ++ tailWord_7251402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251402).length < 2 ^ (prefixWord ++ tailWord_7251402).sum := by decide
  have hdescent : baseEnd_7251402 < baseStart_7251402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251446 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_7251446 : Nat := 118140960795 + 7251446 * 2 ^ 59
def prefixEnd_7251446 : Nat := 4983230072969 + 3 ^ 40 * 7251446 * 2
def baseEnd_7251446 : Nat := 3723477238123140917876213

theorem tailTrace_7251446 : CollatzResearch.WordTrace tailWord_7251446 prefixEnd_7251446 3723477238123140917876213 := by
  unfold tailWord_7251446
  simp only [CollatzResearch.WordTrace]
  refine ⟨16530122730453566576499887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176321309124838043482665461 16530122730453566576499887)
  ·
    refine ⟨24795184095680349864749831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16530122730453566576499887 24795184095680349864749831)
    ·
      refine ⟨37192776143520524797124747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24795184095680349864749831 37192776143520524797124747)
      ·
        refine ⟨55789164215280787195687121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37192776143520524797124747 55789164215280787195687121)
        ·
          refine ⟨41841873161460590396765341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55789164215280787195687121 41841873161460590396765341)
          ·
            refine ⟨15690702435547721398787003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41841873161460590396765341 15690702435547721398787003)
            ·
              refine ⟨23536053653321582098180505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15690702435547721398787003 23536053653321582098180505)
              ·
                refine ⟨17652040239991186573635379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23536053653321582098180505 17652040239991186573635379)
                ·
                  refine ⟨26478060359986779860453069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17652040239991186573635379 26478060359986779860453069)
                  ·
                    refine ⟨9929272634995042447669901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26478060359986779860453069 9929272634995042447669901)
                    ·
                      refine ⟨3723477238123140917876213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9929272634995042447669901 3723477238123140917876213)
                      ·
                        rfl

theorem cell23_7251446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_7251446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251446 prefixEnd_7251446 := by exact prefixLift 7251446
  have htrace : WordTrace (prefixWord ++ tailWord_7251446) baseStart_7251446 baseEnd_7251446 := by
    simpa [prefixWord, tailWord_7251446, baseEnd_7251446] using wordTrace_append hprefix tailTrace_7251446
  have hstable : (prefixWord ++ tailWord_7251446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251446).length < 2 ^ (prefixWord ++ tailWord_7251446).sum := by decide
  have hdescent : baseEnd_7251446 < baseStart_7251446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251463 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_7251463 : Nat := 118140960795 + 7251463 * 2 ^ 59
def prefixEnd_7251463 : Nat := 4983230072969 + 3 ^ 40 * 7251463 * 2
def baseEnd_7251463 : Nat := 3723485967294267351363635

theorem tailTrace_7251463 : CollatzResearch.WordTrace tailWord_7251463 prefixEnd_7251463 3723485967294267351363635 := by
  unfold tailWord_7251463
  simp only [CollatzResearch.WordTrace]
  refine ⟨264482583728195477127367043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176321722485463651418244695 264482583728195477127367043)
  ·
    refine ⟨396723875592293215691050565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264482583728195477127367043 396723875592293215691050565)
    ·
      refine ⟨74385726673554977942071981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396723875592293215691050565 74385726673554977942071981)
      ·
        refine ⟨27894647502583116728276993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74385726673554977942071981 27894647502583116728276993)
        ·
          refine ⟨20920985626937337546207745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27894647502583116728276993 20920985626937337546207745)
          ·
            refine ⟨15690739220203003159655809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20920985626937337546207745 15690739220203003159655809)
            ·
              refine ⟨11768054415152252369741857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15690739220203003159655809 11768054415152252369741857)
              ·
                refine ⟨8826040811364189277306393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11768054415152252369741857 8826040811364189277306393)
                ·
                  refine ⟨6619530608523141957979795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8826040811364189277306393 6619530608523141957979795)
                  ·
                    refine ⟨9929295912784712936969693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6619530608523141957979795 9929295912784712936969693)
                    ·
                      refine ⟨3723485967294267351363635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9929295912784712936969693 3723485967294267351363635)
                      ·
                        rfl

theorem cell23_7251463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_7251463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251463 prefixEnd_7251463 := by exact prefixLift 7251463
  have htrace : WordTrace (prefixWord ++ tailWord_7251463) baseStart_7251463 baseEnd_7251463 := by
    simpa [prefixWord, tailWord_7251463, baseEnd_7251463] using wordTrace_append hprefix tailTrace_7251463
  have hstable : (prefixWord ++ tailWord_7251463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251463).length < 2 ^ (prefixWord ++ tailWord_7251463).sum := by decide
  have hdescent : baseEnd_7251463 < baseStart_7251463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251519 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 3]
def baseStart_7251519 : Nat := 118140960795 + 7251519 * 2 ^ 59
def prefixEnd_7251519 : Nat := 4983230072969 + 3 ^ 40 * 7251519 * 2
def baseEnd_7251519 : Nat := 3723514722210919132263377

theorem tailTrace_7251519 : CollatzResearch.WordTrace tailWord_7251519 prefixEnd_7251519 3723514722210919132263377 := by
  unfold tailWord_7251519
  simp only [CollatzResearch.WordTrace]
  refine ⟨264484626215992598691405611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176323084143995065794270407 264484626215992598691405611)
  ·
    refine ⟨396726939323988898037108417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264484626215992598691405611 396726939323988898037108417)
    ·
      refine ⟨297545204492991673527831313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396726939323988898037108417 297545204492991673527831313)
      ·
        refine ⟨223158903369743755145873485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297545204492991673527831313 223158903369743755145873485)
        ·
          refine ⟨83684588763653908179702557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223158903369743755145873485 83684588763653908179702557)
          ·
            refine ⟨31381720786370215567388459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83684588763653908179702557 31381720786370215567388459)
            ·
              refine ⟨47072581179555323351082689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31381720786370215567388459 47072581179555323351082689)
              ·
                refine ⟨35304435884666492513312017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47072581179555323351082689 35304435884666492513312017)
                ·
                  refine ⟨26478326913499869384984013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35304435884666492513312017 26478326913499869384984013)
                  ·
                    refine ⟨9929372592562451019369005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26478326913499869384984013 9929372592562451019369005)
                    ·
                      refine ⟨3723514722210919132263377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9929372592562451019369005 3723514722210919132263377)
                      ·
                        rfl

theorem cell23_7251519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_7251519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251519 prefixEnd_7251519 := by exact prefixLift 7251519
  have htrace : WordTrace (prefixWord ++ tailWord_7251519) baseStart_7251519 baseEnd_7251519 := by
    simpa [prefixWord, tailWord_7251519, baseEnd_7251519] using wordTrace_append hprefix tailTrace_7251519
  have hstable : (prefixWord ++ tailWord_7251519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251519).length < 2 ^ (prefixWord ++ tailWord_7251519).sum := by decide
  have hdescent : baseEnd_7251519 < baseStart_7251519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251529 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 1, 7, 2]
def baseStart_7251529 : Nat := 118140960795 + 7251529 * 2 ^ 59
def prefixEnd_7251529 : Nat := 4983230072969 + 3 ^ 40 * 7251529 * 2
def baseEnd_7251529 : Nat := 3723519857017464093138331

theorem tailTrace_7251529 : CollatzResearch.WordTrace tailWord_7251529 prefixEnd_7251529 3723519857017464093138331 := by
  unfold tailWord_7251529
  simp only [CollatzResearch.WordTrace]
  refine ⟨264484990945956370399269641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176323327297304246932846427 264484990945956370399269641)
  ·
    refine ⟨198363743209467277799452231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264484990945956370399269641 198363743209467277799452231)
    ·
      refine ⟨297545614814200916699178347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198363743209467277799452231 297545614814200916699178347)
      ·
        refine ⟨446318422221301375048767521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297545614814200916699178347 446318422221301375048767521)
        ·
          refine ⟨334738816665976031286575641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446318422221301375048767521 334738816665976031286575641)
          ·
            refine ⟨251054112499482023464931731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334738816665976031286575641 251054112499482023464931731)
            ·
              refine ⟨376581168749223035197397597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251054112499482023464931731 376581168749223035197397597)
              ·
                refine ⟨141217938280958638199024099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376581168749223035197397597 141217938280958638199024099)
                ·
                  refine ⟨211826907421437957298536149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141217938280958638199024099 211826907421437957298536149)
                  ·
                    refine ⟨4964693142689952124184441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 211826907421437957298536149 4964693142689952124184441)
                    ·
                      refine ⟨3723519857017464093138331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964693142689952124184441 3723519857017464093138331)
                      ·
                        rfl

theorem cell23_7251529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 7, 2].length) (baseStart_7251529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251529 prefixEnd_7251529 := by exact prefixLift 7251529
  have htrace : WordTrace (prefixWord ++ tailWord_7251529) baseStart_7251529 baseEnd_7251529 := by
    simpa [prefixWord, tailWord_7251529, baseEnd_7251529] using wordTrace_append hprefix tailTrace_7251529
  have hstable : (prefixWord ++ tailWord_7251529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251529).length < 2 ^ (prefixWord ++ tailWord_7251529).sum := by decide
  have hdescent : baseEnd_7251529 < baseStart_7251529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251552 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 1, 10]
def baseStart_7251552 : Nat := 118140960795 + 7251552 * 2 ^ 59
def prefixEnd_7251552 : Nat := 4983230072969 + 3 ^ 40 * 7251552 * 2
def baseEnd_7251552 : Nat := 1241177222357505834383575

theorem tailTrace_7251552 : CollatzResearch.WordTrace tailWord_7251552 prefixEnd_7251552 1241177222357505834383575 := by
  unfold tailWord_7251552
  simp only [CollatzResearch.WordTrace]
  refine ⟨132242914912436522663678455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176323886549915363551571273 132242914912436522663678455)
  ·
    refine ⟨198364372368654783995517683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132242914912436522663678455 198364372368654783995517683)
    ·
      refine ⟨297546558552982175993276525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198364372368654783995517683 297546558552982175993276525)
      ·
        refine ⟨111579959457368315997478697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297546558552982175993276525 111579959457368315997478697)
        ·
          refine ⟨83684969593026236998109023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111579959457368315997478697 83684969593026236998109023)
          ·
            refine ⟨125527454389539355497163535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83684969593026236998109023 125527454389539355497163535)
            ·
              refine ⟨188291181584309033245745303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125527454389539355497163535 188291181584309033245745303)
              ·
                refine ⟨282436772376463549868617955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188291181584309033245745303 282436772376463549868617955)
                ·
                  refine ⟨423655158564695324802926933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282436772376463549868617955 423655158564695324802926933)
                  ·
                    refine ⟨1241177222357505834383575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 423655158564695324802926933 1241177222357505834383575)
                    ·
                      rfl

theorem cell23_7251552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_7251552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251552 prefixEnd_7251552 := by exact prefixLift 7251552
  have htrace : WordTrace (prefixWord ++ tailWord_7251552) baseStart_7251552 baseEnd_7251552 := by
    simpa [prefixWord, tailWord_7251552, baseEnd_7251552] using wordTrace_append hprefix tailTrace_7251552
  have hstable : (prefixWord ++ tailWord_7251552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251552).length < 2 ^ (prefixWord ++ tailWord_7251552).sum := by decide
  have hdescent : baseEnd_7251552 < baseStart_7251552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251559 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_7251559 : Nat := 118140960795 + 7251559 * 2 ^ 59
def prefixEnd_7251559 : Nat := 4983230072969 + 3 ^ 40 * 7251559 * 2
def baseEnd_7251559 : Nat := 3723535261437098975763193

theorem tailTrace_7251559 : CollatzResearch.WordTrace tailWord_7251559 prefixEnd_7251559 3723535261437098975763193 := by
  unfold tailWord_7251559
  simp only [CollatzResearch.WordTrace]
  refine ⟨264486085135847685522861731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176324056757231790348574487 264486085135847685522861731)
  ·
    refine ⟨396729127703771528284292597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264486085135847685522861731 396729127703771528284292597)
    ·
      refine ⟨37193355722228580776652431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 396729127703771528284292597 37193355722228580776652431)
      ·
        refine ⟨55790033583342871164978647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37193355722228580776652431 55790033583342871164978647)
        ·
          refine ⟨83685050375014306747467971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55790033583342871164978647 83685050375014306747467971)
          ·
            refine ⟨125527575562521460121201957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83685050375014306747467971 125527575562521460121201957)
            ·
              refine ⟨23536420417972773772725367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125527575562521460121201957 23536420417972773772725367)
              ·
                refine ⟨35304630626959160659088051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23536420417972773772725367 35304630626959160659088051)
                ·
                  refine ⟨52956945940438740988632077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35304630626959160659088051 52956945940438740988632077)
                  ·
                    refine ⟨19858854727664527870737029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52956945940438740988632077 19858854727664527870737029)
                    ·
                      refine ⟨3723535261437098975763193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19858854727664527870737029 3723535261437098975763193)
                      ·
                        rfl

theorem cell23_7251559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_7251559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251559 prefixEnd_7251559 := by exact prefixLift 7251559
  have htrace : WordTrace (prefixWord ++ tailWord_7251559) baseStart_7251559 baseEnd_7251559 := by
    simpa [prefixWord, tailWord_7251559, baseEnd_7251559] using wordTrace_append hprefix tailTrace_7251559
  have hstable : (prefixWord ++ tailWord_7251559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251559).length < 2 ^ (prefixWord ++ tailWord_7251559).sum := by decide
  have hdescent : baseEnd_7251559 < baseStart_7251559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251569 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 5, 4]
def baseStart_7251569 : Nat := 118140960795 + 7251569 * 2 ^ 59
def prefixEnd_7251569 : Nat := 4983230072969 + 3 ^ 40 * 7251569 * 2
def baseEnd_7251569 : Nat := 1241180132081214645546049

theorem tailTrace_7251569 : CollatzResearch.WordTrace tailWord_7251569 prefixEnd_7251569 1241180132081214645546049 := by
  unfold tailWord_7251569
  simp only [CollatzResearch.WordTrace]
  refine ⟨264486449865811457230725761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176324299910540971487150507 264486449865811457230725761)
  ·
    refine ⟨198364837399358592923044321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264486449865811457230725761 198364837399358592923044321)
    ·
      refine ⟨148773628049518944692283241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198364837399358592923044321 148773628049518944692283241)
      ·
        refine ⟨111580221037139208519212431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148773628049518944692283241 111580221037139208519212431)
        ·
          refine ⟨167370331555708812778818647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111580221037139208519212431 167370331555708812778818647)
          ·
            refine ⟨251055497333563219168227971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167370331555708812778818647 251055497333563219168227971)
            ·
              refine ⟨376583246000344828752341957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251055497333563219168227971 376583246000344828752341957)
              ·
                refine ⟨70609358625064655391064117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376583246000344828752341957 70609358625064655391064117)
                ·
                  refine ⟨6619627371099811442912261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70609358625064655391064117 6619627371099811442912261)
                  ·
                    refine ⟨1241180132081214645546049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6619627371099811442912261 1241180132081214645546049)
                    ·
                      rfl

theorem cell23_7251569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_7251569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251569 prefixEnd_7251569 := by exact prefixLift 7251569
  have htrace : WordTrace (prefixWord ++ tailWord_7251569) baseStart_7251569 baseEnd_7251569 := by
    simpa [prefixWord, tailWord_7251569, baseEnd_7251569] using wordTrace_append hprefix tailTrace_7251569
  have hstable : (prefixWord ++ tailWord_7251569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251569).length < 2 ^ (prefixWord ++ tailWord_7251569).sum := by decide
  have hdescent : baseEnd_7251569 < baseStart_7251569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251646 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_7251646 : Nat := 118140960795 + 7251646 * 2 ^ 59
def prefixEnd_7251646 : Nat := 4983230072969 + 3 ^ 40 * 7251646 * 2
def baseEnd_7251646 : Nat := 1241193311418013378458431

theorem tailTrace_7251646 : CollatzResearch.WordTrace tailWord_7251646 prefixEnd_7251646 1241193311418013378458431 := by
  unfold tailWord_7251646
  simp only [CollatzResearch.WordTrace]
  refine ⟨33061157285816562422659849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176326172191021666254185861 33061157285816562422659849)
  ·
    refine ⟨24795867964362421816994887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33061157285816562422659849 24795867964362421816994887)
    ·
      refine ⟨37193801946543632725492331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24795867964362421816994887 37193801946543632725492331)
      ·
        refine ⟨55790702919815449088238497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37193801946543632725492331 55790702919815449088238497)
        ·
          refine ⟨41843027189861586816178873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55790702919815449088238497 41843027189861586816178873)
          ·
            refine ⟨31382270392396190112134155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41843027189861586816178873 31382270392396190112134155)
            ·
              refine ⟨47073405588594285168201233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31382270392396190112134155 47073405588594285168201233)
              ·
                refine ⟨35305054191445713876150925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47073405588594285168201233 35305054191445713876150925)
                ·
                  refine ⟨13239395321792142703556597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35305054191445713876150925 13239395321792142703556597)
                  ·
                    refine ⟨1241193311418013378458431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13239395321792142703556597 1241193311418013378458431)
                    ·
                      rfl

theorem cell23_7251646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_7251646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251646 prefixEnd_7251646 := by exact prefixLift 7251646
  have htrace : WordTrace (prefixWord ++ tailWord_7251646) baseStart_7251646 baseEnd_7251646 := by
    simpa [prefixWord, tailWord_7251646, baseEnd_7251646] using wordTrace_append hprefix tailTrace_7251646
  have hstable : (prefixWord ++ tailWord_7251646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251646).length < 2 ^ (prefixWord ++ tailWord_7251646).sum := by decide
  have hdescent : baseEnd_7251646 < baseStart_7251646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251660 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 3, 1, 3]
def baseStart_7251660 : Nat := 118140960795 + 7251660 * 2 ^ 59
def prefixEnd_7251660 : Nat := 4983230072969 + 3 ^ 40 * 7251660 * 2
def baseEnd_7251660 : Nat := 3723587122983203080600229

theorem tailTrace_7251660 : CollatzResearch.WordTrace tailWord_7251660 prefixEnd_7251660 3723587122983203080600229 := by
  unfold tailWord_7251660
  simp only [CollatzResearch.WordTrace]
  refine ⟨132244884454240889886144217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176326512605654519848192289 132244884454240889886144217)
  ·
    refine ⟨99183663340680667414608163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132244884454240889886144217 99183663340680667414608163)
    ·
      refine ⟨148775495011021001121912245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99183663340680667414608163 148775495011021001121912245)
      ·
        refine ⟨13947702657283218855179273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148775495011021001121912245 13947702657283218855179273)
        ·
          refine ⟨10460776992962414141384455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13947702657283218855179273 10460776992962414141384455)
          ·
            refine ⟨15691165489443621212076683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10460776992962414141384455 15691165489443621212076683)
            ·
              refine ⟨23536748234165431818115025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15691165489443621212076683 23536748234165431818115025)
              ·
                refine ⟨17652561175624073863586269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23536748234165431818115025 17652561175624073863586269)
                ·
                  refine ⟨6619710440859027698844851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17652561175624073863586269 6619710440859027698844851)
                  ·
                    refine ⟨9929565661288541548267277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6619710440859027698844851 9929565661288541548267277)
                    ·
                      refine ⟨3723587122983203080600229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9929565661288541548267277 3723587122983203080600229)
                      ·
                        rfl

theorem cell23_7251660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_7251660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251660 prefixEnd_7251660 := by exact prefixLift 7251660
  have htrace : WordTrace (prefixWord ++ tailWord_7251660) baseStart_7251660 baseEnd_7251660 := by
    simpa [prefixWord, tailWord_7251660, baseEnd_7251660] using wordTrace_append hprefix tailTrace_7251660
  have hstable : (prefixWord ++ tailWord_7251660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251660).length < 2 ^ (prefixWord ++ tailWord_7251660).sum := by decide
  have hdescent : baseEnd_7251660 < baseStart_7251660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251693 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_7251693 : Nat := 118140960795 + 7251693 * 2 ^ 59
def prefixEnd_7251693 : Nat := 4983230072969 + 3 ^ 40 * 7251693 * 2
def baseEnd_7251693 : Nat := 1241201355948267150495859

theorem tailTrace_7251693 : CollatzResearch.WordTrace tailWord_7251693 prefixEnd_7251693 1241201355948267150495859 := by
  unfold tailWord_7251693
  simp only [CollatzResearch.WordTrace]
  refine ⟨264490972517362226408239733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176327315011574817605493155 264490972517362226408239733)
  ·
    refine ⟨24796028673502708725772475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264490972517362226408239733 24796028673502708725772475)
    ·
      refine ⟨37194043010254063088658713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24796028673502708725772475 37194043010254063088658713)
      ·
        refine ⟨27895532257690547316494035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37194043010254063088658713 27895532257690547316494035)
        ·
          refine ⟨41843298386535820974741053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27895532257690547316494035 41843298386535820974741053)
          ·
            refine ⟨15691236894950932865527895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41843298386535820974741053 15691236894950932865527895)
            ·
              refine ⟨23536855342426399298291843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15691236894950932865527895 23536855342426399298291843)
              ·
                refine ⟨35305283013639598947437765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23536855342426399298291843 35305283013639598947437765)
                ·
                  refine ⟨6619740565057424802644581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35305283013639598947437765 6619740565057424802644581)
                  ·
                    refine ⟨1241201355948267150495859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6619740565057424802644581 1241201355948267150495859)
                    ·
                      rfl

theorem cell23_7251693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_7251693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251693 prefixEnd_7251693 := by exact prefixLift 7251693
  have htrace : WordTrace (prefixWord ++ tailWord_7251693) baseStart_7251693 baseEnd_7251693 := by
    simpa [prefixWord, tailWord_7251693, baseEnd_7251693] using wordTrace_append hprefix tailTrace_7251693
  have hstable : (prefixWord ++ tailWord_7251693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251693).length < 2 ^ (prefixWord ++ tailWord_7251693).sum := by decide
  have hdescent : baseEnd_7251693 < baseStart_7251693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251709 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_7251709 : Nat := 118140960795 + 7251709 * 2 ^ 59
def prefixEnd_7251709 : Nat := 4983230072969 + 3 ^ 40 * 7251709 * 2
def baseEnd_7251709 : Nat := 3723612283535273388887503

theorem tailTrace_7251709 : CollatzResearch.WordTrace tailWord_7251709 prefixEnd_7251709 3723612283535273388887503 := by
  unfold tailWord_7251709
  simp only [CollatzResearch.WordTrace]
  refine ⟨264491556085304261140822181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176327704056869507427214787 264491556085304261140822181)
  ·
    refine ⟨49592166765994548963904159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264491556085304261140822181 49592166765994548963904159)
    ·
      refine ⟨74388250148991823445856239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49592166765994548963904159 74388250148991823445856239)
      ·
        refine ⟨111582375223487735168784359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74388250148991823445856239 111582375223487735168784359)
        ·
          refine ⟨167373562835231602753176539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111582375223487735168784359 167373562835231602753176539)
          ·
            refine ⟨251060344252847404129764809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167373562835231602753176539 251060344252847404129764809)
            ·
              refine ⟨188295258189635553097323607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251060344252847404129764809 188295258189635553097323607)
              ·
                refine ⟨282442887284453329645985411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188295258189635553097323607 282442887284453329645985411)
                ·
                  refine ⟨423664330926679994468978117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282442887284453329645985411 423664330926679994468978117)
                  ·
                    refine ⟨79437062048752498962933397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 423664330926679994468978117 79437062048752498962933397)
                    ·
                      refine ⟨3723612283535273388887503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79437062048752498962933397 3723612283535273388887503)
                      ·
                        rfl

theorem cell23_7251709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_7251709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251709 prefixEnd_7251709 := by exact prefixLift 7251709
  have htrace : WordTrace (prefixWord ++ tailWord_7251709) baseStart_7251709 baseEnd_7251709 := by
    simpa [prefixWord, tailWord_7251709, baseEnd_7251709] using wordTrace_append hprefix tailTrace_7251709
  have hstable : (prefixWord ++ tailWord_7251709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251709).length < 2 ^ (prefixWord ++ tailWord_7251709).sum := by decide
  have hdescent : baseEnd_7251709 < baseStart_7251709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251710 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_7251710 : Nat := 118140960795 + 7251710 * 2 ^ 59
def prefixEnd_7251710 : Nat := 4983230072969 + 3 ^ 40 * 7251710 * 2
def baseEnd_7251710 : Nat := 1241204265671975961658333

theorem tailTrace_7251710 : CollatzResearch.WordTrace tailWord_7251710 prefixEnd_7251710 1241204265671975961658333 := by
  unfold tailWord_7251710
  simp only [CollatzResearch.WordTrace]
  refine ⟨33061449069787579788951073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176327728372200425541072389 33061449069787579788951073)
  ·
    refine ⟨24796086802340684841713305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33061449069787579788951073 24796086802340684841713305)
    ·
      refine ⟨18597065101755513631284979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24796086802340684841713305 18597065101755513631284979)
      ·
        refine ⟨27895597652633270446927469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18597065101755513631284979 27895597652633270446927469)
        ·
          refine ⟨10460849119737476417597801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27895597652633270446927469 10460849119737476417597801)
          ·
            refine ⟨7845636839803107313198351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10460849119737476417597801 7845636839803107313198351)
            ·
              refine ⟨11768455259704660969797527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7845636839803107313198351 11768455259704660969797527)
              ·
                refine ⟨17652682889556991454696291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11768455259704660969797527 17652682889556991454696291)
                ·
                  refine ⟨26479024334335487182044437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17652682889556991454696291 26479024334335487182044437)
                  ·
                    refine ⟨1241204265671975961658333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26479024334335487182044437 1241204265671975961658333)
                    ·
                      rfl

theorem cell23_7251710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_7251710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251710 prefixEnd_7251710 := by exact prefixLift 7251710
  have htrace : WordTrace (prefixWord ++ tailWord_7251710) baseStart_7251710 baseEnd_7251710 := by
    simpa [prefixWord, tailWord_7251710, baseEnd_7251710] using wordTrace_append hprefix tailTrace_7251710
  have hstable : (prefixWord ++ tailWord_7251710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251710).length < 2 ^ (prefixWord ++ tailWord_7251710).sum := by decide
  have hdescent : baseEnd_7251710 < baseStart_7251710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251733 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_7251733 : Nat := 118140960795 + 7251733 * 2 ^ 59
def prefixEnd_7251733 : Nat := 4983230072969 + 3 ^ 40 * 7251733 * 2
def baseEnd_7251733 : Nat := 3723624607070981294987393

theorem tailTrace_7251733 : CollatzResearch.WordTrace tailWord_7251733 prefixEnd_7251733 3723624607070981294987393 := by
  unfold tailWord_7251733
  simp only [CollatzResearch.WordTrace]
  refine ⟨264492431437217313239695853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176328287624811542159797235 264492431437217313239695853)
  ·
    refine ⟨99184661788956492464885945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264492431437217313239695853 99184661788956492464885945)
    ·
      refine ⟨74388496341717369348664459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99184661788956492464885945 74388496341717369348664459)
      ·
        refine ⟨111582744512576054022996689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74388496341717369348664459 111582744512576054022996689)
        ·
          refine ⟨83687058384432040517247517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111582744512576054022996689 83687058384432040517247517)
          ·
            refine ⟨31382646894162015193967819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83687058384432040517247517 31382646894162015193967819)
            ·
              refine ⟨47073970341243022790951729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31382646894162015193967819 47073970341243022790951729)
              ·
                refine ⟨35305477755932267093213797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47073970341243022790951729 35305477755932267093213797)
                ·
                  refine ⟨6619777079237300079977587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35305477755932267093213797 6619777079237300079977587)
                  ·
                    refine ⟨9929665618855950119966381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6619777079237300079977587 9929665618855950119966381)
                    ·
                      refine ⟨3723624607070981294987393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9929665618855950119966381 3723624607070981294987393)
                      ·
                        rfl

theorem cell23_7251733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_7251733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251733 prefixEnd_7251733 := by exact prefixLift 7251733
  have htrace : WordTrace (prefixWord ++ tailWord_7251733) baseStart_7251733 baseEnd_7251733 := by
    simpa [prefixWord, tailWord_7251733, baseEnd_7251733] using wordTrace_append hprefix tailTrace_7251733
  have hstable : (prefixWord ++ tailWord_7251733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251733).length < 2 ^ (prefixWord ++ tailWord_7251733).sum := by decide
  have hdescent : baseEnd_7251733 < baseStart_7251733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251746 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_7251746 : Nat := 118140960795 + 7251746 * 2 ^ 59
def prefixEnd_7251746 : Nat := 4983230072969 + 3 ^ 40 * 7251746 * 2
def baseEnd_7251746 : Nat := 3723631282319489744124833

theorem tailTrace_7251746 : CollatzResearch.WordTrace tailWord_7251746 prefixEnd_7251746 3723631282319489744124833 := by
  unfold tailWord_7251746
  simp only [CollatzResearch.WordTrace]
  refine ⟨66123226396542554114979773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176328603724113477639946061 66123226396542554114979773)
  ·
    refine ⟨24796209898703457793117415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66123226396542554114979773 24796209898703457793117415)
    ·
      refine ⟨37194314848055186689676123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24796209898703457793117415 37194314848055186689676123)
      ·
        refine ⟨55791472272082780034514185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37194314848055186689676123 55791472272082780034514185)
        ·
          refine ⟨41843604204062085025885639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55791472272082780034514185 41843604204062085025885639)
          ·
            refine ⟨62765406306093127538828459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41843604204062085025885639 62765406306093127538828459)
            ·
              refine ⟨94148109459139691308242689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62765406306093127538828459 94148109459139691308242689)
              ·
                refine ⟨70611082094354768481182017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94148109459139691308242689 70611082094354768481182017)
                ·
                  refine ⟨52958311570766076360886513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70611082094354768481182017 52958311570766076360886513)
                  ·
                    refine ⟨39718733678074557270664885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52958311570766076360886513 39718733678074557270664885)
                    ·
                      refine ⟨3723631282319489744124833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39718733678074557270664885 3723631282319489744124833)
                      ·
                        rfl

theorem cell23_7251746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_7251746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251746 prefixEnd_7251746 := by exact prefixLift 7251746
  have htrace : WordTrace (prefixWord ++ tailWord_7251746) baseStart_7251746 baseEnd_7251746 := by
    simpa [prefixWord, tailWord_7251746, baseEnd_7251746] using wordTrace_append hprefix tailTrace_7251746
  have hstable : (prefixWord ++ tailWord_7251746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251746).length < 2 ^ (prefixWord ++ tailWord_7251746).sum := by decide
  have hdescent : baseEnd_7251746 < baseStart_7251746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251807 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 2, 2, 2]
def baseStart_7251807 : Nat := 118140960795 + 7251807 * 2 ^ 59
def prefixEnd_7251807 : Nat := 4983230072969 + 3 ^ 40 * 7251807 * 2
def baseEnd_7251807 : Nat := 3723662604639414005462053

theorem tailTrace_7251807 : CollatzResearch.WordTrace tailWord_7251807 prefixEnd_7251807 3723662604639414005462053 := by
  unfold tailWord_7251807
  simp only [CollatzResearch.WordTrace]
  refine ⟨264495130438949223877889675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176330086959299482585259783 264495130438949223877889675)
  ·
    refine ⟨396742695658423835816834513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264495130438949223877889675 396742695658423835816834513)
    ·
      refine ⟨297557021743817876862625885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396742695658423835816834513 297557021743817876862625885)
      ·
        refine ⟨111583883153931703823484707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297557021743817876862625885 111583883153931703823484707)
        ·
          refine ⟨167375824730897555735227061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111583883153931703823484707 167375824730897555735227061)
          ·
            refine ⟨15691483568521645850177537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167375824730897555735227061 15691483568521645850177537)
            ·
              refine ⟨11768612676391234387633153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15691483568521645850177537 11768612676391234387633153)
              ·
                refine ⟨8826459507293425790724865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11768612676391234387633153 8826459507293425790724865)
                ·
                  refine ⟨6619844630470069343043649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8826459507293425790724865 6619844630470069343043649)
                  ·
                    refine ⟨4964883472852552007282737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6619844630470069343043649 4964883472852552007282737)
                    ·
                      refine ⟨3723662604639414005462053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964883472852552007282737 3723662604639414005462053)
                      ·
                        rfl

theorem cell23_7251807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_7251807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251807 prefixEnd_7251807 := by exact prefixLift 7251807
  have htrace : WordTrace (prefixWord ++ tailWord_7251807) baseStart_7251807 baseEnd_7251807 := by
    simpa [prefixWord, tailWord_7251807, baseEnd_7251807] using wordTrace_append hprefix tailTrace_7251807
  have hstable : (prefixWord ++ tailWord_7251807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251807).length < 2 ^ (prefixWord ++ tailWord_7251807).sum := by decide
  have hdescent : baseEnd_7251807 < baseStart_7251807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251826 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_7251826 : Nat := 118140960795 + 7251826 * 2 ^ 59
def prefixEnd_7251826 : Nat := 4983230072969 + 3 ^ 40 * 7251826 * 2
def baseEnd_7251826 : Nat := 1241224120257283143708155

theorem tailTrace_7251826 : CollatzResearch.WordTrace tailWord_7251826 prefixEnd_7251826 1241224120257283143708155 := by
  unfold tailWord_7251826
  simp only [CollatzResearch.WordTrace]
  refine ⟨66123955856470097530707833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176330548950586926748554221 66123955856470097530707833)
  ·
    refine ⟨49592966892352573148030875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66123955856470097530707833 49592966892352573148030875)
    ·
      refine ⟨74389450338528859722046313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49592966892352573148030875 74389450338528859722046313)
      ·
        refine ⟨55792087753896644791534735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74389450338528859722046313 55792087753896644791534735)
        ·
          refine ⟨83688131630844967187302103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55792087753896644791534735 83688131630844967187302103)
          ·
            refine ⟨125532197446267450780953155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83688131630844967187302103 125532197446267450780953155)
            ·
              refine ⟨188298296169401176171429733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125532197446267450780953155 188298296169401176171429733)
              ·
                refine ⟨35305930531762720532143075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188298296169401176171429733 35305930531762720532143075)
                ·
                  refine ⟨52958895797644080798214613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35305930531762720532143075 52958895797644080798214613)
                  ·
                    refine ⟨1241224120257283143708155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52958895797644080798214613 1241224120257283143708155)
                    ·
                      rfl

theorem cell23_7251826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_7251826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251826 prefixEnd_7251826 := by exact prefixLift 7251826
  have htrace : WordTrace (prefixWord ++ tailWord_7251826) baseStart_7251826 baseEnd_7251826 := by
    simpa [prefixWord, tailWord_7251826, baseEnd_7251826] using wordTrace_append hprefix tailTrace_7251826
  have hstable : (prefixWord ++ tailWord_7251826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251826).length < 2 ^ (prefixWord ++ tailWord_7251826).sum := by decide
  have hdescent : baseEnd_7251826 < baseStart_7251826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251830 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_7251830 : Nat := 118140960795 + 7251830 * 2 ^ 59
def prefixEnd_7251830 : Nat := 4983230072969 + 3 ^ 40 * 7251830 * 2
def baseEnd_7251830 : Nat := 413741601632718601719383

theorem tailTrace_7251830 : CollatzResearch.WordTrace tailWord_7251830 prefixEnd_7251830 413741601632718601719383 := by
  unfold tailWord_7251830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16530998082366618675373559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176330646211910599203984629 16530998082366618675373559)
  ·
    refine ⟨24796497123549928013060339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16530998082366618675373559 24796497123549928013060339)
    ·
      refine ⟨37194745685324892019590509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24796497123549928013060339 37194745685324892019590509)
      ·
        refine ⟨13948029631996834507346441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37194745685324892019590509 13948029631996834507346441)
        ·
          refine ⟨10461022223997625880509831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13948029631996834507346441 10461022223997625880509831)
          ·
            refine ⟨15691533335996438820764747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10461022223997625880509831 15691533335996438820764747)
            ·
              refine ⟨23537300003994658231147121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15691533335996438820764747 23537300003994658231147121)
              ·
                refine ⟨17652975002995993673360341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23537300003994658231147121 17652975002995993673360341)
                ·
                  refine ⟨413741601632718601719383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17652975002995993673360341 413741601632718601719383)
                  ·
                    rfl

theorem cell23_7251830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_7251830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251830 prefixEnd_7251830 := by exact prefixLift 7251830
  have htrace : WordTrace (prefixWord ++ tailWord_7251830) baseStart_7251830 baseEnd_7251830 := by
    simpa [prefixWord, tailWord_7251830, baseEnd_7251830] using wordTrace_append hprefix tailTrace_7251830
  have hstable : (prefixWord ++ tailWord_7251830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251830).length < 2 ^ (prefixWord ++ tailWord_7251830).sum := by decide
  have hdescent : baseEnd_7251830 < baseStart_7251830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251833 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 2, 5, 2]
def baseStart_7251833 : Nat := 118140960795 + 7251833 * 2 ^ 59
def prefixEnd_7251833 : Nat := 4983230072969 + 3 ^ 40 * 7251833 * 2
def baseEnd_7251833 : Nat := 3723675955136430903736933

theorem tailTrace_7251833 : CollatzResearch.WordTrace tailWord_7251833 prefixEnd_7251833 3723675955136430903736933 := by
  unfold tailWord_7251833
  simp only [CollatzResearch.WordTrace]
  refine ⟨264496078736855030318336153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176330719157903353545557435 264496078736855030318336153)
  ·
    refine ⟨198372059052641272738752115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264496078736855030318336153 198372059052641272738752115)
    ·
      refine ⟨297558088578961909108128173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198372059052641272738752115 297558088578961909108128173)
      ·
        refine ⟨111584283217110715915548065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297558088578961909108128173 111584283217110715915548065)
        ·
          refine ⟨83688212412833036936661049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111584283217110715915548065 83688212412833036936661049)
          ·
            refine ⟨62766159309624777702495787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83688212412833036936661049 62766159309624777702495787)
            ·
              refine ⟨94149238964437166553743681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62766159309624777702495787 94149238964437166553743681)
              ·
                refine ⟨70611929223327874915307761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94149238964437166553743681 70611929223327874915307761)
                ·
                  refine ⟨52958946917495906186480821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70611929223327874915307761 52958946917495906186480821)
                  ·
                    refine ⟨4964901273515241204982577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52958946917495906186480821 4964901273515241204982577)
                    ·
                      refine ⟨3723675955136430903736933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964901273515241204982577 3723675955136430903736933)
                      ·
                        rfl

theorem cell23_7251833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_7251833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251833 prefixEnd_7251833 := by exact prefixLift 7251833
  have htrace : WordTrace (prefixWord ++ tailWord_7251833) baseStart_7251833 baseEnd_7251833 := by
    simpa [prefixWord, tailWord_7251833, baseEnd_7251833] using wordTrace_append hprefix tailTrace_7251833
  have hstable : (prefixWord ++ tailWord_7251833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251833).length < 2 ^ (prefixWord ++ tailWord_7251833).sum := by decide
  have hdescent : baseEnd_7251833 < baseStart_7251833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251843 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 2, 5]
def baseStart_7251843 : Nat := 118140960795 + 7251843 * 2 ^ 59
def prefixEnd_7251843 : Nat := 4983230072969 + 3 ^ 40 * 7251843 * 2
def baseEnd_7251843 : Nat := 1241227029980991954870629

theorem tailTrace_7251843 : CollatzResearch.WordTrace tailWord_7251843 prefixEnd_7251843 1241227029980991954870629 := by
  unfold tailWord_7251843
  simp only [CollatzResearch.WordTrace]
  refine ⟨264496443466818802026200183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176330962311212534684133455 264496443466818802026200183)
  ·
    refine ⟨396744665200228203039300275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264496443466818802026200183 396744665200228203039300275)
    ·
      refine ⟨595116997800342304558950413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396744665200228203039300275 595116997800342304558950413)
      ·
        refine ⟨223168874175128364209606405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 595116997800342304558950413 223168874175128364209606405)
        ·
          refine ⟨41844163907836568289301201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223168874175128364209606405 41844163907836568289301201)
          ·
            refine ⟨31383122930877426216975901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41844163907836568289301201 31383122930877426216975901)
            ·
              refine ⟨11768671099079034831365963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31383122930877426216975901 11768671099079034831365963)
              ·
                refine ⟨17653006648618552247048945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11768671099079034831365963 17653006648618552247048945)
                ·
                  refine ⟨13239754986463914185286709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17653006648618552247048945 13239754986463914185286709)
                  ·
                    refine ⟨1241227029980991954870629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13239754986463914185286709 1241227029980991954870629)
                    ·
                      rfl

theorem cell23_7251843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 5].length) (baseStart_7251843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251843 prefixEnd_7251843 := by exact prefixLift 7251843
  have htrace : WordTrace (prefixWord ++ tailWord_7251843) baseStart_7251843 baseEnd_7251843 := by
    simpa [prefixWord, tailWord_7251843, baseEnd_7251843] using wordTrace_append hprefix tailTrace_7251843
  have hstable : (prefixWord ++ tailWord_7251843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251843).length < 2 ^ (prefixWord ++ tailWord_7251843).sum := by decide
  have hdescent : baseEnd_7251843 < baseStart_7251843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251923 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 11, 2]
def baseStart_7251923 : Nat := 118140960795 + 7251923 * 2 ^ 59
def prefixEnd_7251923 : Nat := 4983230072969 + 3 ^ 40 * 7251923 * 2
def baseEnd_7251923 : Nat := 3723722168395335551611519

theorem tailTrace_7251923 : CollatzResearch.WordTrace tailWord_7251923 prefixEnd_7251923 3723722168395335551611519 := by
  unfold tailWord_7251923
  simp only [CollatzResearch.WordTrace]
  refine ⟨264499361306528975689112423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176332907537685983792741615 264499361306528975689112423)
  ·
    refine ⟨396749041959793463533668635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264499361306528975689112423 396749041959793463533668635)
    ·
      refine ⟨595123562939690195300502953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396749041959793463533668635 595123562939690195300502953)
      ·
        refine ⟨446342672204767646475377215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595123562939690195300502953 446342672204767646475377215)
        ·
          refine ⟨669514008307151469713065823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446342672204767646475377215 669514008307151469713065823)
          ·
            refine ⟨1004271012460727204569598735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669514008307151469713065823 1004271012460727204569598735)
            ·
              refine ⟨1506406518691090806854398103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004271012460727204569598735 1506406518691090806854398103)
              ·
                refine ⟨2259609778036636210281597155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506406518691090806854398103 2259609778036636210281597155)
                ·
                  refine ⟨3389414667054954315422395733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259609778036636210281597155 3389414667054954315422395733)
                  ·
                    refine ⟨4964962891193780735482025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 3389414667054954315422395733 4964962891193780735482025)
                    ·
                      refine ⟨3723722168395335551611519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964962891193780735482025 3723722168395335551611519)
                      ·
                        rfl

theorem cell23_7251923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 11, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 11, 2].length) (baseStart_7251923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251923 prefixEnd_7251923 := by exact prefixLift 7251923
  have htrace : WordTrace (prefixWord ++ tailWord_7251923) baseStart_7251923 baseEnd_7251923 := by
    simpa [prefixWord, tailWord_7251923, baseEnd_7251923] using wordTrace_append hprefix tailTrace_7251923
  have hstable : (prefixWord ++ tailWord_7251923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251923).length < 2 ^ (prefixWord ++ tailWord_7251923).sum := by decide
  have hdescent : baseEnd_7251923 < baseStart_7251923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251924 : List Nat := [2, 4, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_7251924 : Nat := 118140960795 + 7251924 * 2 ^ 59
def prefixEnd_7251924 : Nat := 4983230072969 + 3 ^ 40 * 7251924 * 2
def baseEnd_7251924 : Nat := 1241240893958663349233005

theorem tailTrace_7251924 : CollatzResearch.WordTrace tailWord_7251924 prefixEnd_7251924 1241240893958663349233005 := by
  unfold tailWord_7251924
  simp only [CollatzResearch.WordTrace]
  refine ⟨132249698889762676429949413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176332931853016901906599217 132249698889762676429949413)
  ·
    refine ⟨24796818541830501830615515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132249698889762676429949413 24796818541830501830615515)
    ·
      refine ⟨37195227812745752745923273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24796818541830501830615515 37195227812745752745923273)
      ·
        refine ⟨27896420859559314559442455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37195227812745752745923273 27896420859559314559442455)
        ·
          refine ⟨41844631289338971839163683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27896420859559314559442455 41844631289338971839163683)
          ·
            refine ⟨62766946934008457758745525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41844631289338971839163683 62766946934008457758745525)
            ·
              refine ⟨5884401275063292914882393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62766946934008457758745525 5884401275063292914882393)
              ·
                refine ⟨4413300956297469686161795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5884401275063292914882393 4413300956297469686161795)
                ·
                  refine ⟨6619951434446204529242693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413300956297469686161795 6619951434446204529242693)
                  ·
                    refine ⟨1241240893958663349233005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6619951434446204529242693 1241240893958663349233005)
                    ·
                      rfl

theorem cell23_7251924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_7251924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251924 prefixEnd_7251924 := by exact prefixLift 7251924
  have htrace : WordTrace (prefixWord ++ tailWord_7251924) baseStart_7251924 baseEnd_7251924 := by
    simpa [prefixWord, tailWord_7251924, baseEnd_7251924] using wordTrace_append hprefix tailTrace_7251924
  have hstable : (prefixWord ++ tailWord_7251924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251924).length < 2 ^ (prefixWord ++ tailWord_7251924).sum := by decide
  have hdescent : baseEnd_7251924 < baseStart_7251924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251940 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 4, 3, 2]
def baseStart_7251940 : Nat := 118140960795 + 7251940 * 2 ^ 59
def prefixEnd_7251940 : Nat := 4983230072969 + 3 ^ 40 * 7251940 * 2
def baseEnd_7251940 : Nat := 3723730897566461985098941

theorem tailTrace_7251940 : CollatzResearch.WordTrace tailWord_7251940 prefixEnd_7251940 3723730897566461985098941 := by
  unfold tailWord_7251940
  simp only [CollatzResearch.WordTrace]
  refine ⟨132249990673733693796240637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176333320898311591728320849 132249990673733693796240637)
  ·
    refine ⟨49593746502650135173590239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132249990673733693796240637 49593746502650135173590239)
    ·
      refine ⟨74390619753975202760385359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49593746502650135173590239 74390619753975202760385359)
      ·
        refine ⟨111585929630962804140578039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74390619753975202760385359 111585929630962804140578039)
        ·
          refine ⟨167378894446444206210867059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111585929630962804140578039 167378894446444206210867059)
          ·
            refine ⟨251068341669666309316300589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167378894446444206210867059 251068341669666309316300589)
            ·
              refine ⟨94150628126124865993612721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251068341669666309316300589 94150628126124865993612721)
              ·
                refine ⟨70612971094593649495209541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94150628126124865993612721 70612971094593649495209541)
                ·
                  refine ⟨13239932080236309280351789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70612971094593649495209541 13239932080236309280351789)
                  ·
                    refine ⟨4964974530088615980131921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13239932080236309280351789 4964974530088615980131921)
                    ·
                      refine ⟨3723730897566461985098941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4964974530088615980131921 3723730897566461985098941)
                      ·
                        rfl

theorem cell23_7251940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_7251940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251940 prefixEnd_7251940 := by exact prefixLift 7251940
  have htrace : WordTrace (prefixWord ++ tailWord_7251940) baseStart_7251940 baseEnd_7251940 := by
    simpa [prefixWord, tailWord_7251940, baseEnd_7251940] using wordTrace_append hprefix tailTrace_7251940
  have hstable : (prefixWord ++ tailWord_7251940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251940).length < 2 ^ (prefixWord ++ tailWord_7251940).sum := by decide
  have hdescent : baseEnd_7251940 < baseStart_7251940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251950 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_7251950 : Nat := 118140960795 + 7251950 * 2 ^ 59
def prefixEnd_7251950 : Nat := 4983230072969 + 3 ^ 40 * 7251950 * 2
def baseEnd_7251950 : Nat := 1241245344124335648657965

theorem tailTrace_7251950 : CollatzResearch.WordTrace tailWord_7251950 prefixEnd_7251950 1241245344124335648657965 := by
  unfold tailWord_7251950
  simp only [CollatzResearch.WordTrace]
  refine ⟨33062543259678894912543163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176333564051620772866896869 33062543259678894912543163)
  ·
    refine ⟨49593814889518342368814745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33062543259678894912543163 49593814889518342368814745)
    ·
      refine ⟨37195361167138756776611059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49593814889518342368814745 37195361167138756776611059)
      ·
        refine ⟨55793041750708135164916589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37195361167138756776611059 55793041750708135164916589)
        ·
          refine ⟨20922390656515550686843721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55793041750708135164916589 20922390656515550686843721)
          ·
            refine ⟨15691792992386663015132791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20922390656515550686843721 15691792992386663015132791)
            ·
              refine ⟨23537689488579994522699187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15691792992386663015132791 23537689488579994522699187)
              ·
                refine ⟨35306534232869991784048781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23537689488579994522699187 35306534232869991784048781)
                ·
                  refine ⟨13239950337326246919018293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35306534232869991784048781 13239950337326246919018293)
                  ·
                    refine ⟨1241245344124335648657965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13239950337326246919018293 1241245344124335648657965)
                    ·
                      rfl

theorem cell23_7251950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_7251950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251950 prefixEnd_7251950 := by exact prefixLift 7251950
  have htrace : WordTrace (prefixWord ++ tailWord_7251950) baseStart_7251950 baseEnd_7251950 := by
    simpa [prefixWord, tailWord_7251950, baseEnd_7251950] using wordTrace_append hprefix tailTrace_7251950
  have hstable : (prefixWord ++ tailWord_7251950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251950).length < 2 ^ (prefixWord ++ tailWord_7251950).sum := by decide
  have hdescent : baseEnd_7251950 < baseStart_7251950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251963 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 6, 4]
def baseStart_7251963 : Nat := 118140960795 + 7251963 * 2 ^ 59
def prefixEnd_7251963 : Nat := 4983230072969 + 3 ^ 40 * 7251963 * 2
def baseEnd_7251963 : Nat := 1241247569207171798370445

theorem tailTrace_7251963 : CollatzResearch.WordTrace tailWord_7251963 prefixEnd_7251963 1241247569207171798370445 := by
  unfold tailWord_7251963
  simp only [CollatzResearch.WordTrace]
  refine ⟨264500820226384062520568543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176333880150922708347045695 264500820226384062520568543)
  ·
    refine ⟨396751230339576093780852815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264500820226384062520568543 396751230339576093780852815)
    ·
      refine ⟨595126845509364140671279223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396751230339576093780852815 595126845509364140671279223)
      ·
        refine ⟨892690268264046211006918835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595126845509364140671279223 892690268264046211006918835)
        ·
          refine ⟨1339035402396069316510378253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892690268264046211006918835 1339035402396069316510378253)
          ·
            refine ⟨502138275898525993691391845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1339035402396069316510378253 502138275898525993691391845)
            ·
              refine ⟨94150926730973623817135971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502138275898525993691391845 94150926730973623817135971)
              ·
                refine ⟨141226390096460435725703957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94150926730973623817135971 141226390096460435725703957)
                ·
                  refine ⟨6619987035771582924642373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141226390096460435725703957 6619987035771582924642373)
                  ·
                    refine ⟨1241247569207171798370445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6619987035771582924642373 1241247569207171798370445)
                    ·
                      rfl

theorem cell23_7251963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 4].length) (baseStart_7251963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251963 prefixEnd_7251963 := by exact prefixLift 7251963
  have htrace : WordTrace (prefixWord ++ tailWord_7251963) baseStart_7251963 baseEnd_7251963 := by
    simpa [prefixWord, tailWord_7251963, baseEnd_7251963] using wordTrace_append hprefix tailTrace_7251963
  have hstable : (prefixWord ++ tailWord_7251963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251963).length < 2 ^ (prefixWord ++ tailWord_7251963).sum := by decide
  have hdescent : baseEnd_7251963 < baseStart_7251963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7251997 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_7251997 : Nat := 118140960795 + 7251997 * 2 ^ 59
def prefixEnd_7251997 : Nat := 4983230072969 + 3 ^ 40 * 7251997 * 2
def baseEnd_7251997 : Nat := 1241253388654589420695393

theorem tailTrace_7251997 : CollatzResearch.WordTrace tailWord_7251997 prefixEnd_7251997 1241253388654589420695393 := by
  unfold tailWord_7251997
  simp only [CollatzResearch.WordTrace]
  refine ⟨264502060308260886327306245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176334706872173924218204163 264502060308260886327306245)
  ·
    refine ⟨49594136307798916186369921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264502060308260886327306245 49594136307798916186369921)
    ·
      refine ⟨37195602230849187139777441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49594136307798916186369921 37195602230849187139777441)
      ·
        refine ⟨27896701673136890354833081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37195602230849187139777441 27896701673136890354833081)
        ·
          refine ⟨20922526254852667766124811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27896701673136890354833081 20922526254852667766124811)
          ·
            refine ⟨31383789382279001649187217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20922526254852667766124811 31383789382279001649187217)
            ·
              refine ⟨23537842036709251236890413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31383789382279001649187217 23537842036709251236890413)
              ·
                refine ⟨8826690763765969213833905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23537842036709251236890413 8826690763765969213833905)
                ·
                  refine ⟨6620018072824476910375429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8826690763765969213833905 6620018072824476910375429)
                  ·
                    refine ⟨1241253388654589420695393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6620018072824476910375429 1241253388654589420695393)
                    ·
                      rfl

theorem cell23_7251997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_7251997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7251997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7251997 prefixEnd_7251997 := by exact prefixLift 7251997
  have htrace : WordTrace (prefixWord ++ tailWord_7251997) baseStart_7251997 baseEnd_7251997 := by
    simpa [prefixWord, tailWord_7251997, baseEnd_7251997] using wordTrace_append hprefix tailTrace_7251997
  have hstable : (prefixWord ++ tailWord_7251997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7251997).length < 2 ^ (prefixWord ++ tailWord_7251997).sum := by decide
  have hdescent : baseEnd_7251997 < baseStart_7251997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7251997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252008 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_7252008 : Nat := 118140960795 + 7252008 * 2 ^ 59
def prefixEnd_7252008 : Nat := 4983230072969 + 3 ^ 40 * 7252008 * 2
def baseEnd_7252008 : Nat := 3723765814250967719048629

theorem tailTrace_7252008 : CollatzResearch.WordTrace tailWord_7252008 prefixEnd_7252008 3723765814250967719048629 := by
  unfold tailWord_7252008
  simp only [CollatzResearch.WordTrace]
  refine ⟨132251230755610517602978339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176334974340814023470637785 132251230755610517602978339)
  ·
    refine ⟨198376846133415776404467509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132251230755610517602978339 198376846133415776404467509)
    ·
      refine ⟨18597829325007729037918829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198376846133415776404467509 18597829325007729037918829)
      ·
        refine ⟨6974185996877898389219561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18597829325007729037918829 6974185996877898389219561)
        ·
          refine ⟨5230639497658423791914671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6974185996877898389219561 5230639497658423791914671)
          ·
            refine ⟨7845959246487635687872007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230639497658423791914671 7845959246487635687872007)
            ·
              refine ⟨11768938869731453531808011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7845959246487635687872007 11768938869731453531808011)
              ·
                refine ⟨17653408304597180297712017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11768938869731453531808011 17653408304597180297712017)
                ·
                  refine ⟨13240056228447885223284013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17653408304597180297712017 13240056228447885223284013)
                  ·
                    refine ⟨4965021085667956958731505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13240056228447885223284013 4965021085667956958731505)
                    ·
                      refine ⟨3723765814250967719048629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965021085667956958731505 3723765814250967719048629)
                      ·
                        rfl

theorem cell23_7252008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_7252008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252008 prefixEnd_7252008 := by exact prefixLift 7252008
  have htrace : WordTrace (prefixWord ++ tailWord_7252008) baseStart_7252008 baseEnd_7252008 := by
    simpa [prefixWord, tailWord_7252008, baseEnd_7252008] using wordTrace_append hprefix tailTrace_7252008
  have hstable : (prefixWord ++ tailWord_7252008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252008).length < 2 ^ (prefixWord ++ tailWord_7252008).sum := by decide
  have hdescent : baseEnd_7252008 < baseStart_7252008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252038 : List Nat := [6, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_7252038 : Nat := 118140960795 + 7252038 * 2 ^ 59
def prefixEnd_7252038 : Nat := 4983230072969 + 3 ^ 40 * 7252038 * 2
def baseEnd_7252038 : Nat := 3723781218670602601673491

theorem tailTrace_7252038 : CollatzResearch.WordTrace tailWord_7252038 prefixEnd_7252038 3723781218670602601673491 := by
  unfold tailWord_7252038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8265736115659760947798399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176335703800741566886365845 8265736115659760947798399)
  ·
    refine ⟨12398604173489641421697599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8265736115659760947798399 12398604173489641421697599)
    ·
      refine ⟨18597906260234462132546399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12398604173489641421697599 18597906260234462132546399)
      ·
        refine ⟨27896859390351693198819599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18597906260234462132546399 27896859390351693198819599)
        ·
          refine ⟨41845289085527539798229399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27896859390351693198819599 41845289085527539798229399)
          ·
            refine ⟨62767933628291309697344099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41845289085527539798229399 62767933628291309697344099)
            ·
              refine ⟨94151900442436964546016149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62767933628291309697344099 94151900442436964546016149)
              ·
                refine ⟨4413370333239232713094507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94151900442436964546016149 4413370333239232713094507)
                ·
                  refine ⟨6620055499858849069641761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413370333239232713094507 6620055499858849069641761)
                  ·
                    refine ⟨4965041624894136802231321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6620055499858849069641761 4965041624894136802231321)
                    ·
                      refine ⟨3723781218670602601673491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965041624894136802231321 3723781218670602601673491)
                      ·
                        rfl

theorem cell23_7252038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_7252038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252038 prefixEnd_7252038 := by exact prefixLift 7252038
  have htrace : WordTrace (prefixWord ++ tailWord_7252038) baseStart_7252038 baseEnd_7252038 := by
    simpa [prefixWord, tailWord_7252038, baseEnd_7252038] using wordTrace_append hprefix tailTrace_7252038
  have hstable : (prefixWord ++ tailWord_7252038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252038).length < 2 ^ (prefixWord ++ tailWord_7252038).sum := by decide
  have hdescent : baseEnd_7252038 < baseStart_7252038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252064 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 1, 3, 2]
def baseStart_7252064 : Nat := 118140960795 + 7252064 * 2 ^ 59
def prefixEnd_7252064 : Nat := 4983230072969 + 3 ^ 40 * 7252064 * 2
def baseEnd_7252064 : Nat := 3723794569167619499948371

theorem tailTrace_7252064 : CollatzResearch.WordTrace tailWord_7252064 prefixEnd_7252064 3723794569167619499948371 := by
  unfold tailWord_7252064
  simp only [CollatzResearch.WordTrace]
  refine ⟨132252251999509078384997623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176336335999345437846663497 132252251999509078384997623)
  ·
    refine ⟨198378377999263617577496435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132252251999509078384997623 198378377999263617577496435)
    ·
      refine ⟨297567566998895426366244653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198378377999263617577496435 297567566998895426366244653)
      ·
        refine ⟨111587837624585784887341745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297567566998895426366244653 111587837624585784887341745)
        ·
          refine ⟨83690878218439338665506309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111587837624585784887341745 83690878218439338665506309)
          ·
            refine ⟨15692039665957375999782433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83690878218439338665506309 15692039665957375999782433)
            ·
              refine ⟨11769029749468031999836825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15692039665957375999782433 11769029749468031999836825)
              ·
                refine ⟨8826772312101023999877619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11769029749468031999836825 8826772312101023999877619)
                ·
                  refine ⟨13240158468151535999816429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8826772312101023999877619 13240158468151535999816429)
                  ·
                    refine ⟨4965059425556825999931161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13240158468151535999816429 4965059425556825999931161)
                    ·
                      refine ⟨3723794569167619499948371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965059425556825999931161 3723794569167619499948371)
                      ·
                        rfl

theorem cell23_7252064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_7252064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252064 prefixEnd_7252064 := by exact prefixLift 7252064
  have htrace : WordTrace (prefixWord ++ tailWord_7252064) baseStart_7252064 baseEnd_7252064 := by
    simpa [prefixWord, tailWord_7252064, baseEnd_7252064] using wordTrace_append hprefix tailTrace_7252064
  have hstable : (prefixWord ++ tailWord_7252064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252064).length < 2 ^ (prefixWord ++ tailWord_7252064).sum := by decide
  have hdescent : baseEnd_7252064 < baseStart_7252064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252077 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_7252077 : Nat := 118140960795 + 7252077 * 2 ^ 59
def prefixEnd_7252077 : Nat := 4983230072969 + 3 ^ 40 * 7252077 * 2
def baseEnd_7252077 : Nat := 3723801244416127949085811

theorem tailTrace_7252077 : CollatzResearch.WordTrace tailWord_7252077 prefixEnd_7252077 3723801244416127949085811 := by
  unfold tailWord_7252077
  simp only [CollatzResearch.WordTrace]
  refine ⟨264504978147971059990218485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176336652098647373326812323 264504978147971059990218485)
  ·
    refine ⟨24797341701372286874082983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264504978147971059990218485 24797341701372286874082983)
    ·
      refine ⟨37196012552058430311124475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24797341701372286874082983 37196012552058430311124475)
      ·
        refine ⟨55794018828087645466686713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37196012552058430311124475 55794018828087645466686713)
        ·
          refine ⟨41845514121065734100015035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55794018828087645466686713 41845514121065734100015035)
          ·
            refine ⟨62768271181598601150022553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41845514121065734100015035 62768271181598601150022553)
            ·
              refine ⟨47076203386198950862516915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62768271181598601150022553 47076203386198950862516915)
              ·
                refine ⟨70614305079298426293775373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47076203386198950862516915 70614305079298426293775373)
                ·
                  refine ⟨26480364404736909860165765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70614305079298426293775373 26480364404736909860165765)
                  ·
                    refine ⟨4965068325888170598781081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26480364404736909860165765 4965068325888170598781081)
                    ·
                      refine ⟨3723801244416127949085811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965068325888170598781081 3723801244416127949085811)
                      ·
                        rfl

theorem cell23_7252077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_7252077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252077 prefixEnd_7252077 := by exact prefixLift 7252077
  have htrace : WordTrace (prefixWord ++ tailWord_7252077) baseStart_7252077 baseEnd_7252077 := by
    simpa [prefixWord, tailWord_7252077, baseEnd_7252077] using wordTrace_append hprefix tailTrace_7252077
  have hstable : (prefixWord ++ tailWord_7252077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252077).length < 2 ^ (prefixWord ++ tailWord_7252077).sum := by decide
  have hdescent : baseEnd_7252077 < baseStart_7252077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252080 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 5]
def baseStart_7252080 : Nat := 118140960795 + 7252080 * 2 ^ 59
def prefixEnd_7252080 : Nat := 4983230072969 + 3 ^ 40 * 7252080 * 2
def baseEnd_7252080 : Nat := 3723802784858091437348297

theorem tailTrace_7252080 : CollatzResearch.WordTrace tailWord_7252080 prefixEnd_7252080 3723802784858091437348297 := by
  unfold tailWord_7252080
  simp only [CollatzResearch.WordTrace]
  refine ⟨132252543783480095751288847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176336725044640127668385129 132252543783480095751288847)
  ·
    refine ⟨198378815675220143626933271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132252543783480095751288847 198378815675220143626933271)
    ·
      refine ⟨297568223512830215440399907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198378815675220143626933271 297568223512830215440399907)
      ·
        refine ⟨446352335269245323160599861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297568223512830215440399907 446352335269245323160599861)
        ·
          refine ⟨41845531431491749046306237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 446352335269245323160599861 41845531431491749046306237)
          ·
            refine ⟨15692074286809405892364839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41845531431491749046306237 15692074286809405892364839)
            ·
              refine ⟨23538111430214108838547259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15692074286809405892364839 23538111430214108838547259)
              ·
                refine ⟨35307167145321163257820889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23538111430214108838547259 35307167145321163257820889)
                ·
                  refine ⟨26480375358990872443365667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35307167145321163257820889 26480375358990872443365667)
                  ·
                    refine ⟨39720563038486308665048501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26480375358990872443365667 39720563038486308665048501)
                    ·
                      refine ⟨3723802784858091437348297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39720563038486308665048501 3723802784858091437348297)
                      ·
                        rfl

theorem cell23_7252080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_7252080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252080 prefixEnd_7252080 := by exact prefixLift 7252080
  have htrace : WordTrace (prefixWord ++ tailWord_7252080) baseStart_7252080 baseEnd_7252080 := by
    simpa [prefixWord, tailWord_7252080, baseEnd_7252080] using wordTrace_append hprefix tailTrace_7252080
  have hstable : (prefixWord ++ tailWord_7252080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252080).length < 2 ^ (prefixWord ++ tailWord_7252080).sum := by decide
  have hdescent : baseEnd_7252080 < baseStart_7252080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252123 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 7]
def baseStart_7252123 : Nat := 118140960795 + 7252123 * 2 ^ 59
def prefixEnd_7252123 : Nat := 4983230072969 + 3 ^ 40 * 7252123 * 2
def baseEnd_7252123 : Nat := 3723824864526234769110599

theorem tailTrace_7252123 : CollatzResearch.WordTrace tailWord_7252123 prefixEnd_7252123 3723824864526234769110599 := by
  unfold tailWord_7252123
  simp only [CollatzResearch.WordTrace]
  refine ⟨264506655905804409846393023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176337770603869606564262015 264506655905804409846393023)
  ·
    refine ⟨396759983858706614769589535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264506655905804409846393023 396759983858706614769589535)
    ·
      refine ⟨595139975788059922154384303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396759983858706614769589535 595139975788059922154384303)
      ·
        refine ⟨892709963682089883231576455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595139975788059922154384303 892709963682089883231576455)
        ·
          refine ⟨1339064945523134824847364683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892709963682089883231576455 1339064945523134824847364683)
          ·
            refine ⟨2008597418284702237271047025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339064945523134824847364683 2008597418284702237271047025)
            ·
              refine ⟨1506448063713526677953285269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2008597418284702237271047025 1506448063713526677953285269)
              ·
                refine ⟨70614752986571563029060247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1506448063713526677953285269 70614752986571563029060247)
                ·
                  refine ⟨105922129479857344543590371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70614752986571563029060247 105922129479857344543590371)
                  ·
                    refine ⟨158883194219786016815385557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105922129479857344543590371 158883194219786016815385557)
                    ·
                      refine ⟨3723824864526234769110599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158883194219786016815385557 3723824864526234769110599)
                      ·
                        rfl

theorem cell23_7252123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_7252123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252123 prefixEnd_7252123 := by exact prefixLift 7252123
  have htrace : WordTrace (prefixWord ++ tailWord_7252123) baseStart_7252123 baseEnd_7252123 := by
    simpa [prefixWord, tailWord_7252123, baseEnd_7252123] using wordTrace_append hprefix tailTrace_7252123
  have hstable : (prefixWord ++ tailWord_7252123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252123).length < 2 ^ (prefixWord ++ tailWord_7252123).sum := by decide
  have hdescent : baseEnd_7252123 < baseStart_7252123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252181 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 2, 5]
def baseStart_7252181 : Nat := 118140960795 + 7252181 * 2 ^ 59
def prefixEnd_7252181 : Nat := 4983230072969 + 3 ^ 40 * 7252181 * 2
def baseEnd_7252181 : Nat := 1241284882134731847395111

theorem tailTrace_7252181 : CollatzResearch.WordTrace tailWord_7252181 prefixEnd_7252181 1241284882134731847395111 := by
  unfold tailWord_7252181
  simp only [CollatzResearch.WordTrace]
  refine ⟨264508771339594285752004397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176339180893062857168002931 264508771339594285752004397)
  ·
    refine ⟨99190789252347857157001649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264508771339594285752004397 99190789252347857157001649)
    ·
      refine ⟨74393091939260892867751237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99190789252347857157001649 74393091939260892867751237)
      ·
        refine ⟨13948704738611417412703357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74393091939260892867751237 13948704738611417412703357)
        ·
          refine ⟨5230764276979281529763759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13948704738611417412703357 5230764276979281529763759)
          ·
            refine ⟨7846146415468922294645639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230764276979281529763759 7846146415468922294645639)
            ·
              refine ⟨11769219623203383441968459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7846146415468922294645639 11769219623203383441968459)
              ·
                refine ⟨17653829434805075162952689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11769219623203383441968459 17653829434805075162952689)
                ·
                  refine ⟨13240372076103806372214517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17653829434805075162952689 13240372076103806372214517)
                  ·
                    refine ⟨1241284882134731847395111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13240372076103806372214517 1241284882134731847395111)
                    ·
                      rfl

theorem cell23_7252181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_7252181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252181 prefixEnd_7252181 := by exact prefixLift 7252181
  have htrace : WordTrace (prefixWord ++ tailWord_7252181) baseStart_7252181 baseEnd_7252181 := by
    simpa [prefixWord, tailWord_7252181, baseEnd_7252181] using wordTrace_append hprefix tailTrace_7252181
  have hstable : (prefixWord ++ tailWord_7252181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252181).length < 2 ^ (prefixWord ++ tailWord_7252181).sum := by decide
  have hdescent : baseEnd_7252181 < baseStart_7252181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252184 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 2, 1, 4]
def baseStart_7252184 : Nat := 118140960795 + 7252184 * 2 ^ 59
def prefixEnd_7252184 : Nat := 4983230072969 + 3 ^ 40 * 7252184 * 2
def baseEnd_7252184 : Nat := 3723856186846159030447819

theorem tailTrace_7252184 : CollatzResearch.WordTrace tailWord_7252184 prefixEnd_7252184 3723856186846159030447819 := by
  unfold tailWord_7252184
  simp only [CollatzResearch.WordTrace]
  refine ⟨132254440379291708632181803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176339253839055611509575737 132254440379291708632181803)
  ·
    refine ⟨198381660568937562948272705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132254440379291708632181803 198381660568937562948272705)
    ·
      refine ⟨148786245426703172211204529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198381660568937562948272705 148786245426703172211204529)
      ·
        refine ⟨111589684070027379158403397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148786245426703172211204529 111589684070027379158403397)
        ·
          refine ⟨20923065763130133592200637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111589684070027379158403397 20923065763130133592200637)
          ·
            refine ⟨7846149661173800097075239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20923065763130133592200637 7846149661173800097075239)
            ·
              refine ⟨11769224491760700145612859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7846149661173800097075239 11769224491760700145612859)
              ·
                refine ⟨17653836737641050218419289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11769224491760700145612859 17653836737641050218419289)
                ·
                  refine ⟨13240377553230787663814467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17653836737641050218419289 13240377553230787663814467)
                  ·
                    refine ⟨19860566329846181495721701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13240377553230787663814467 19860566329846181495721701)
                    ·
                      refine ⟨3723856186846159030447819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19860566329846181495721701 3723856186846159030447819)
                      ·
                        rfl

theorem cell23_7252184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_7252184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252184 prefixEnd_7252184 := by exact prefixLift 7252184
  have htrace : WordTrace (prefixWord ++ tailWord_7252184) baseStart_7252184 baseEnd_7252184 := by
    simpa [prefixWord, tailWord_7252184, baseEnd_7252184] using wordTrace_append hprefix tailTrace_7252184
  have hstable : (prefixWord ++ tailWord_7252184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252184).length < 2 ^ (prefixWord ++ tailWord_7252184).sum := by decide
  have hdescent : baseEnd_7252184 < baseStart_7252184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252207 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 6]
def baseStart_7252207 : Nat := 118140960795 + 7252207 * 2 ^ 59
def prefixEnd_7252207 : Nat := 4983230072969 + 3 ^ 40 * 7252207 * 2
def baseEnd_7252207 : Nat := 413763110766801382273357

theorem tailTrace_7252207 : CollatzResearch.WordTrace tailWord_7252207 prefixEnd_7252207 413763110766801382273357 := by
  unfold tailWord_7252207
  simp only [CollatzResearch.WordTrace]
  refine ⟨264509719637500092192450875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176339813091666728128300583 264509719637500092192450875)
  ·
    refine ⟨396764579456250138288676313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264509719637500092192450875 396764579456250138288676313)
    ·
      refine ⟨297573434592187603716507235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396764579456250138288676313 297573434592187603716507235)
      ·
        refine ⟨446360151888281405574760853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297573434592187603716507235 446360151888281405574760853)
        ·
          refine ⟨20923132119763190886316915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 446360151888281405574760853 20923132119763190886316915)
          ·
            refine ⟨31384698179644786329475373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20923132119763190886316915 31384698179644786329475373)
            ·
              refine ⟨11769261817366794873553265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31384698179644786329475373 11769261817366794873553265)
              ·
                refine ⟨8826946363025096155164949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11769261817366794873553265 8826946363025096155164949)
                ·
                  refine ⟨413763110766801382273357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8826946363025096155164949 413763110766801382273357)
                  ·
                    rfl

theorem cell23_7252207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 6].length) (baseStart_7252207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252207 prefixEnd_7252207 := by exact prefixLift 7252207
  have htrace : WordTrace (prefixWord ++ tailWord_7252207) baseStart_7252207 baseEnd_7252207 := by
    simpa [prefixWord, tailWord_7252207, baseEnd_7252207] using wordTrace_append hprefix tailTrace_7252207
  have hstable : (prefixWord ++ tailWord_7252207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252207).length < 2 ^ (prefixWord ++ tailWord_7252207).sum := by decide
  have hdescent : baseEnd_7252207 < baseStart_7252207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252227 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 3, 5, 2]
def baseStart_7252227 : Nat := 118140960795 + 7252227 * 2 ^ 59
def prefixEnd_7252227 : Nat := 4983230072969 + 3 ^ 40 * 7252227 * 2
def baseEnd_7252227 : Nat := 3723878266514302362210121

theorem tailTrace_7252227 : CollatzResearch.WordTrace tailWord_7252227 prefixEnd_7252227 3723878266514302362210121 := by
  unfold tailWord_7252227
  simp only [CollatzResearch.WordTrace]
  refine ⟨264510449097427635608178935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176340299398285090405452623 264510449097427635608178935)
  ·
    refine ⟨396765673646141453412268403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264510449097427635608178935 396765673646141453412268403)
    ·
      refine ⟨595148510469212180118402605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396765673646141453412268403 595148510469212180118402605)
      ·
        refine ⟨223180691425954567544400977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 595148510469212180118402605 223180691425954567544400977)
        ·
          refine ⟨167385518569465925658300733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223180691425954567544400977 167385518569465925658300733)
          ·
            refine ⟨62769569463549722121862775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167385518569465925658300733 62769569463549722121862775)
            ·
              refine ⟨94154354195324583182794163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62769569463549722121862775 94154354195324583182794163)
              ·
                refine ⟨141231531292986874774191245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94154354195324583182794163 141231531292986874774191245)
                ·
                  refine ⟨52961824234870078040321717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141231531292986874774191245 52961824234870078040321717)
                  ·
                    refine ⟨4965171022019069816280161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52961824234870078040321717 4965171022019069816280161)
                    ·
                      refine ⟨3723878266514302362210121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965171022019069816280161 3723878266514302362210121)
                      ·
                        rfl

theorem cell23_7252227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 5, 2].length) (baseStart_7252227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252227 prefixEnd_7252227 := by exact prefixLift 7252227
  have htrace : WordTrace (prefixWord ++ tailWord_7252227) baseStart_7252227 baseEnd_7252227 := by
    simpa [prefixWord, tailWord_7252227, baseEnd_7252227] using wordTrace_append hprefix tailTrace_7252227
  have hstable : (prefixWord ++ tailWord_7252227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252227).length < 2 ^ (prefixWord ++ tailWord_7252227).sum := by decide
  have hdescent : baseEnd_7252227 < baseStart_7252227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252234 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_7252234 : Nat := 118140960795 + 7252234 * 2 ^ 59
def prefixEnd_7252234 : Nat := 4983230072969 + 3 ^ 40 * 7252234 * 2
def baseEnd_7252234 : Nat := 3723881860878883834822589

theorem tailTrace_7252234 : CollatzResearch.WordTrace tailWord_7252234 prefixEnd_7252234 3723881860878883834822589 := by
  unfold tailWord_7252234
  simp only [CollatzResearch.WordTrace]
  refine ⟨66127676102100568950920939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176340469605601517202455837 66127676102100568950920939)
  ·
    refine ⟨99191514153150853426381409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66127676102100568950920939 99191514153150853426381409)
    ·
      refine ⟨74393635614863140069786057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99191514153150853426381409 74393635614863140069786057)
      ·
        refine ⟨55795226711147355052339543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74393635614863140069786057 55795226711147355052339543)
        ·
          refine ⟨83692840066721032578509315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55795226711147355052339543 83692840066721032578509315)
          ·
            refine ⟨125539260100081548867763973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83692840066721032578509315 125539260100081548867763973)
            ·
              refine ⟨23538611268765290412705745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125539260100081548867763973 23538611268765290412705745)
              ·
                refine ⟨17653958451573967809529309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23538611268765290412705745 17653958451573967809529309)
                ·
                  refine ⟨6620234419340237928573491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17653958451573967809529309 6620234419340237928573491)
                  ·
                    refine ⟨9930351629010356892860237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6620234419340237928573491 9930351629010356892860237)
                    ·
                      refine ⟨3723881860878883834822589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9930351629010356892860237 3723881860878883834822589)
                      ·
                        rfl

theorem cell23_7252234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_7252234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252234 prefixEnd_7252234 := by exact prefixLift 7252234
  have htrace : WordTrace (prefixWord ++ tailWord_7252234) baseStart_7252234 baseEnd_7252234 := by
    simpa [prefixWord, tailWord_7252234, baseEnd_7252234] using wordTrace_append hprefix tailTrace_7252234
  have hstable : (prefixWord ++ tailWord_7252234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252234).length < 2 ^ (prefixWord ++ tailWord_7252234).sum := by decide
  have hdescent : baseEnd_7252234 < baseStart_7252234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252251 : List Nat := [1, 1, 1, 1, 1, 1, 9, 3, 1, 1, 3]
def baseStart_7252251 : Nat := 118140960795 + 7252251 * 2 ^ 59
def prefixEnd_7252251 : Nat := 4983230072969 + 3 ^ 40 * 7252251 * 2
def baseEnd_7252251 : Nat := 3723890590050010268310011

theorem tailTrace_7252251 : CollatzResearch.WordTrace tailWord_7252251 prefixEnd_7252251 3723890590050010268310011 := by
  unfold tailWord_7252251
  simp only [CollatzResearch.WordTrace]
  refine ⟨264511324449340687707052607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176340882966227125138035071 264511324449340687707052607)
  ·
    refine ⟨396766986674011031560578911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264511324449340687707052607 396766986674011031560578911)
    ·
      refine ⟨595150480011016547340868367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396766986674011031560578911 595150480011016547340868367)
      ·
        refine ⟨892725720016524821011302551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595150480011016547340868367 892725720016524821011302551)
        ·
          refine ⟨1339088580024787231516953827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892725720016524821011302551 1339088580024787231516953827)
          ·
            refine ⟨2008632870037180847275430741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339088580024787231516953827 2008632870037180847275430741)
            ·
              refine ⟨11769333222874106527004477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2008632870037180847275430741 11769333222874106527004477)
              ·
                refine ⟨4413499958577789947626679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11769333222874106527004477 4413499958577789947626679)
                ·
                  refine ⟨6620249937866684921440019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413499958577789947626679 6620249937866684921440019)
                  ·
                    refine ⟨9930374906800027382160029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6620249937866684921440019 9930374906800027382160029)
                    ·
                      refine ⟨3723890590050010268310011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9930374906800027382160029 3723890590050010268310011)
                      ·
                        rfl

theorem cell23_7252251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 1, 1, 3].length) (baseStart_7252251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252251 prefixEnd_7252251 := by exact prefixLift 7252251
  have htrace : WordTrace (prefixWord ++ tailWord_7252251) baseStart_7252251 baseEnd_7252251 := by
    simpa [prefixWord, tailWord_7252251, baseEnd_7252251] using wordTrace_append hprefix tailTrace_7252251
  have hstable : (prefixWord ++ tailWord_7252251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252251).length < 2 ^ (prefixWord ++ tailWord_7252251).sum := by decide
  have hdescent : baseEnd_7252251 < baseStart_7252251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252261 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 2, 3, 2]
def baseStart_7252261 : Nat := 118140960795 + 7252261 * 2 ^ 59
def prefixEnd_7252261 : Nat := 4983230072969 + 3 ^ 40 * 7252261 * 2
def baseEnd_7252261 : Nat := 3723895724856555229184965

theorem tailTrace_7252261 : CollatzResearch.WordTrace tailWord_7252261 prefixEnd_7252261 3723895724856555229184965 := by
  unfold tailWord_7252261
  simp only [CollatzResearch.WordTrace]
  refine ⟨264511689179304459414916637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176341126119536306276611091 264511689179304459414916637)
  ·
    refine ⟨99191883442239172280593739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264511689179304459414916637 99191883442239172280593739)
    ·
      refine ⟨148787825163358758420890609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99191883442239172280593739 148787825163358758420890609)
      ·
        refine ⟨111590868872519068815667957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148787825163358758420890609 111590868872519068815667957)
        ·
          refine ⟨10461643956798662701468871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111590868872519068815667957 10461643956798662701468871)
          ·
            refine ⟨15692465935197994052203307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10461643956798662701468871 15692465935197994052203307)
            ·
              refine ⟨23538698902796991078304961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15692465935197994052203307 23538698902796991078304961)
              ·
                refine ⟨17654024177097743308728721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23538698902796991078304961 17654024177097743308728721)
                ·
                  refine ⟨13240518132823307481546541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17654024177097743308728721 13240518132823307481546541)
                  ·
                    refine ⟨4965194299808740305579953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13240518132823307481546541 4965194299808740305579953)
                    ·
                      refine ⟨3723895724856555229184965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965194299808740305579953 3723895724856555229184965)
                      ·
                        rfl

theorem cell23_7252261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_7252261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252261 prefixEnd_7252261 := by exact prefixLift 7252261
  have htrace : WordTrace (prefixWord ++ tailWord_7252261) baseStart_7252261 baseEnd_7252261 := by
    simpa [prefixWord, tailWord_7252261, baseEnd_7252261] using wordTrace_append hprefix tailTrace_7252261
  have hstable : (prefixWord ++ tailWord_7252261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252261).length < 2 ^ (prefixWord ++ tailWord_7252261).sum := by decide
  have hdescent : baseEnd_7252261 < baseStart_7252261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252277 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_7252277 : Nat := 118140960795 + 7252277 * 2 ^ 59
def prefixEnd_7252277 : Nat := 4983230072969 + 3 ^ 40 * 7252277 * 2
def baseEnd_7252277 : Nat := 3723903940547027166584891

theorem tailTrace_7252277 : CollatzResearch.WordTrace tailWord_7252277 prefixEnd_7252277 3723903940547027166584891 := by
  unfold tailWord_7252277
  simp only [CollatzResearch.WordTrace]
  refine ⟨264512272747246494147499085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176341515164830996098332723 264512272747246494147499085)
  ·
    refine ⟨99192102280217435305312157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264512272747246494147499085 99192102280217435305312157)
    ·
      refine ⟨37197038355081538239492059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99192102280217435305312157 37197038355081538239492059)
      ·
        refine ⟨55795557532622307359238089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37197038355081538239492059 55795557532622307359238089)
        ·
          refine ⟨41846668149466730519428567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55795557532622307359238089 41846668149466730519428567)
          ·
            refine ⟨62770002224200095779142851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41846668149466730519428567 62770002224200095779142851)
            ·
              refine ⟨94155003336300143668714277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62770002224200095779142851 94155003336300143668714277)
              ·
                refine ⟨17654063125556276937883927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94155003336300143668714277 17654063125556276937883927)
                ·
                  refine ⟨26481094688334415406825891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17654063125556276937883927 26481094688334415406825891)
                  ·
                    refine ⟨39721642032501623110238837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26481094688334415406825891 39721642032501623110238837)
                    ·
                      refine ⟨3723903940547027166584891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39721642032501623110238837 3723903940547027166584891)
                      ·
                        rfl

theorem cell23_7252277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_7252277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252277 prefixEnd_7252277 := by exact prefixLift 7252277
  have htrace : WordTrace (prefixWord ++ tailWord_7252277) baseStart_7252277 baseEnd_7252277 := by
    simpa [prefixWord, tailWord_7252277, baseEnd_7252277] using wordTrace_append hprefix tailTrace_7252277
  have hstable : (prefixWord ++ tailWord_7252277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252277).length < 2 ^ (prefixWord ++ tailWord_7252277).sum := by decide
  have hdescent : baseEnd_7252277 < baseStart_7252277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252280 : List Nat := [2, 1, 2, 1, 3, 1, 3, 10]
def baseStart_7252280 : Nat := 118140960795 + 7252280 * 2 ^ 59
def prefixEnd_7252280 : Nat := 4983230072969 + 3 ^ 40 * 7252280 * 2
def baseEnd_7252280 : Nat := 137922425221814468698051

theorem tailTrace_7252280 : CollatzResearch.WordTrace tailWord_7252280 prefixEnd_7252280 137922425221814468698051 := by
  unfold tailWord_7252280
  simp only [CollatzResearch.WordTrace]
  refine ⟨132256191083117812829929147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176341588110823750439905529 132256191083117812829929147)
  ·
    refine ⟨198384286624676719244893721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132256191083117812829929147 198384286624676719244893721)
    ·
      refine ⟨148788214968507539433670291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198384286624676719244893721 148788214968507539433670291)
      ·
        refine ⟨223182322452761309150505437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148788214968507539433670291 223182322452761309150505437)
        ·
          refine ⟨83693370919785490931439539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223182322452761309150505437 83693370919785490931439539)
          ·
            refine ⟨125540056379678236397159309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83693370919785490931439539 125540056379678236397159309)
            ·
              refine ⟨47077521142379338648934741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125540056379678236397159309 47077521142379338648934741)
              ·
                refine ⟨137922425221814468698051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47077521142379338648934741 137922425221814468698051)
                ·
                  rfl

theorem cell23_7252280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 10].length) (baseStart_7252280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252280 prefixEnd_7252280 := by exact prefixLift 7252280
  have htrace : WordTrace (prefixWord ++ tailWord_7252280) baseStart_7252280 baseEnd_7252280 := by
    simpa [prefixWord, tailWord_7252280, baseEnd_7252280] using wordTrace_append hprefix tailTrace_7252280
  have hstable : (prefixWord ++ tailWord_7252280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252280).length < 2 ^ (prefixWord ++ tailWord_7252280).sum := by decide
  have hdescent : baseEnd_7252280 < baseStart_7252280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252284 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 2, 4]
def baseStart_7252284 : Nat := 118140960795 + 7252284 * 2 ^ 59
def prefixEnd_7252284 : Nat := 4983230072969 + 3 ^ 40 * 7252284 * 2
def baseEnd_7252284 : Nat := 1241302511637202879732453

theorem tailTrace_7252284 : CollatzResearch.WordTrace tailWord_7252284 prefixEnd_7252284 1241302511637202879732453 := by
  unfold tailWord_7252284
  simp only [CollatzResearch.WordTrace]
  refine ⟨132256264029110567171501953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176341685372147422895335937 132256264029110567171501953)
  ·
    refine ⟨99192198021832925378626465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132256264029110567171501953 99192198021832925378626465)
    ·
      refine ⟨74394148516374694033969849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99192198021832925378626465 74394148516374694033969849)
      ·
        refine ⟨55795611387281020525477387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74394148516374694033969849 55795611387281020525477387)
        ·
          refine ⟨83693417080921530788216081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55795611387281020525477387 83693417080921530788216081)
          ·
            refine ⟨62770062810691148091162061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83693417080921530788216081 62770062810691148091162061)
            ·
              refine ⟨23538773554009180534185773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62770062810691148091162061 23538773554009180534185773)
              ·
                refine ⟨8827040082753442700319665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23538773554009180534185773 8827040082753442700319665)
                ·
                  refine ⟨6620280062065082025239749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8827040082753442700319665 6620280062065082025239749)
                  ·
                    refine ⟨1241302511637202879732453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6620280062065082025239749 1241302511637202879732453)
                    ·
                      rfl

theorem cell23_7252284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_7252284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252284 prefixEnd_7252284 := by exact prefixLift 7252284
  have htrace : WordTrace (prefixWord ++ tailWord_7252284) baseStart_7252284 baseEnd_7252284 := by
    simpa [prefixWord, tailWord_7252284, baseEnd_7252284] using wordTrace_append hprefix tailTrace_7252284
  have hstable : (prefixWord ++ tailWord_7252284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252284).length < 2 ^ (prefixWord ++ tailWord_7252284).sum := by decide
  have hdescent : baseEnd_7252284 < baseStart_7252284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252287 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 4]
def baseStart_7252287 : Nat := 118140960795 + 7252287 * 2 ^ 59
def prefixEnd_7252287 : Nat := 4983230072969 + 3 ^ 40 * 7252287 * 2
def baseEnd_7252287 : Nat := 3723909075353572127459845

theorem tailTrace_7252287 : CollatzResearch.WordTrace tailWord_7252287 prefixEnd_7252287 3723909075353572127459845 := by
  unfold tailWord_7252287
  simp only [CollatzResearch.WordTrace]
  refine ⟨264512637477210265855363115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176341758318140177236908743 264512637477210265855363115)
  ·
    refine ⟨396768956215815398783044673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264512637477210265855363115 396768956215815398783044673)
    ·
      refine ⟨297576717161861549087283505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396768956215815398783044673 297576717161861549087283505)
      ·
        refine ⟨223182537871396161815462629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297576717161861549087283505 223182537871396161815462629)
        ·
          refine ⟨41846725850886780340399243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223182537871396161815462629 41846725850886780340399243)
          ·
            refine ⟨62770088776330170510598865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41846725850886780340399243 62770088776330170510598865)
            ·
              refine ⟨47077566582247627882949149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62770088776330170510598865 47077566582247627882949149)
              ·
                refine ⟨17654087468342860456105931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47077566582247627882949149 17654087468342860456105931)
                ·
                  refine ⟨26481131202514290684158897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17654087468342860456105931 26481131202514290684158897)
                  ·
                    refine ⟨19860848401885718013119173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26481131202514290684158897 19860848401885718013119173)
                    ·
                      refine ⟨3723909075353572127459845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19860848401885718013119173 3723909075353572127459845)
                      ·
                        rfl

theorem cell23_7252287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_7252287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252287 prefixEnd_7252287 := by exact prefixLift 7252287
  have htrace : WordTrace (prefixWord ++ tailWord_7252287) baseStart_7252287 baseEnd_7252287 := by
    simpa [prefixWord, tailWord_7252287, baseEnd_7252287] using wordTrace_append hprefix tailTrace_7252287
  have hstable : (prefixWord ++ tailWord_7252287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252287).length < 2 ^ (prefixWord ++ tailWord_7252287).sum := by decide
  have hdescent : baseEnd_7252287 < baseStart_7252287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252311 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 1, 2, 3]
def baseStart_7252311 : Nat := 118140960795 + 7252311 * 2 ^ 59
def prefixEnd_7252311 : Nat := 4983230072969 + 3 ^ 40 * 7252311 * 2
def baseEnd_7252311 : Nat := 3723921398889280033559735

theorem tailTrace_7252311 : CollatzResearch.WordTrace tailWord_7252311 prefixEnd_7252311 3723921398889280033559735 := by
  unfold tailWord_7252311
  simp only [CollatzResearch.WordTrace]
  refine ⟨264513512829123317954236787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176342341886082211969491191 264513512829123317954236787)
  ·
    refine ⟨396770269243684976931355181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264513512829123317954236787 396770269243684976931355181)
    ·
      refine ⟨148788850966381866349258193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396770269243684976931355181 148788850966381866349258193)
      ·
        refine ⟨111591638224786399761943645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148788850966381866349258193 111591638224786399761943645)
        ·
          refine ⟨41846864334294899910728867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111591638224786399761943645 41846864334294899910728867)
          ·
            refine ⟨62770296501442349866093301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41846864334294899910728867 62770296501442349866093301)
            ·
              refine ⟨5884715297010220299946247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62770296501442349866093301 5884715297010220299946247)
              ·
                refine ⟨8827072945515330449919371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5884715297010220299946247 8827072945515330449919371)
                ·
                  refine ⟨13240609418272995674879057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8827072945515330449919371 13240609418272995674879057)
                  ·
                    refine ⟨9930457063704746756159293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13240609418272995674879057 9930457063704746756159293)
                    ·
                      refine ⟨3723921398889280033559735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9930457063704746756159293 3723921398889280033559735)
                      ·
                        rfl

theorem cell23_7252311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_7252311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252311 prefixEnd_7252311 := by exact prefixLift 7252311
  have htrace : WordTrace (prefixWord ++ tailWord_7252311) baseStart_7252311 baseEnd_7252311 := by
    simpa [prefixWord, tailWord_7252311, baseEnd_7252311] using wordTrace_append hprefix tailTrace_7252311
  have hstable : (prefixWord ++ tailWord_7252311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252311).length < 2 ^ (prefixWord ++ tailWord_7252311).sum := by decide
  have hdescent : baseEnd_7252311 < baseStart_7252311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252325 : List Nat := [1, 3, 1, 3, 1, 3, 4, 2, 1, 2, 2]
def baseStart_7252325 : Nat := 118140960795 + 7252325 * 2 ^ 59
def prefixEnd_7252325 : Nat := 4983230072969 + 3 ^ 40 * 7252325 * 2
def baseEnd_7252325 : Nat := 3723928587618442978784671

theorem tailTrace_7252325 : CollatzResearch.WordTrace tailWord_7252325 prefixEnd_7252325 3723928587618442978784671 := by
  unfold tailWord_7252325
  simp only [CollatzResearch.WordTrace]
  refine ⟨264514023451072598345246429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176342682300715065563497619 264514023451072598345246429)
  ·
    refine ⟨99192758794152224379467411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264514023451072598345246429 99192758794152224379467411)
    ·
      refine ⟨148789138191228336569201117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99192758794152224379467411 148789138191228336569201117)
      ·
        refine ⟨55795926821710626213450419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148789138191228336569201117 55795926821710626213450419)
        ·
          refine ⟨83693890232565939320175629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55795926821710626213450419 83693890232565939320175629)
          ·
            refine ⟨31385208837212227245065861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83693890232565939320175629 31385208837212227245065861)
            ·
              refine ⟨5884726656977292608449849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31385208837212227245065861 5884726656977292608449849)
              ·
                refine ⟨4413544992732969456337387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5884726656977292608449849 4413544992732969456337387)
                ·
                  refine ⟨6620317489099454184506081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413544992732969456337387 6620317489099454184506081)
                  ·
                    refine ⟨4965238116824590638379561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6620317489099454184506081 4965238116824590638379561)
                    ·
                      refine ⟨3723928587618442978784671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965238116824590638379561 3723928587618442978784671)
                      ·
                        rfl

theorem cell23_7252325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_7252325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252325 prefixEnd_7252325 := by exact prefixLift 7252325
  have htrace : WordTrace (prefixWord ++ tailWord_7252325) baseStart_7252325 baseEnd_7252325 := by
    simpa [prefixWord, tailWord_7252325, baseEnd_7252325] using wordTrace_append hprefix tailTrace_7252325
  have hstable : (prefixWord ++ tailWord_7252325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252325).length < 2 ^ (prefixWord ++ tailWord_7252325).sum := by decide
  have hdescent : baseEnd_7252325 < baseStart_7252325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252327 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 2, 7]
def baseStart_7252327 : Nat := 118140960795 + 7252327 * 2 ^ 59
def prefixEnd_7252327 : Nat := 4983230072969 + 3 ^ 40 * 7252327 * 2
def baseEnd_7252327 : Nat := 1241309871526583990319887

theorem tailTrace_7252327 : CollatzResearch.WordTrace tailWord_7252327 prefixEnd_7252327 1241309871526583990319887 := by
  unfold tailWord_7252327
  simp only [CollatzResearch.WordTrace]
  refine ⟨264514096397065352686819235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176342730931376901791212823 264514096397065352686819235)
  ·
    refine ⟨396771144595598029030228853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264514096397065352686819235 396771144595598029030228853)
    ·
      refine ⟨37197294805837315221583955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 396771144595598029030228853 37197294805837315221583955)
      ·
        refine ⟨55795942208755972832375933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37197294805837315221583955 55795942208755972832375933)
        ·
          refine ⟨20923478328283489812140975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55795942208755972832375933 20923478328283489812140975)
          ·
            refine ⟨31385217492425234718211463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20923478328283489812140975 31385217492425234718211463)
            ·
              refine ⟨47077826238637852077317195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31385217492425234718211463 47077826238637852077317195)
              ·
                refine ⟨70616739357956778115975793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47077826238637852077317195 70616739357956778115975793)
                ·
                  refine ⟨52962554518467583586981845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70616739357956778115975793 52962554518467583586981845)
                  ·
                    refine ⟨1241309871526583990319887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52962554518467583586981845 1241309871526583990319887)
                    ·
                      rfl

theorem cell23_7252327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_7252327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252327 prefixEnd_7252327 := by exact prefixLift 7252327
  have htrace : WordTrace (prefixWord ++ tailWord_7252327) baseStart_7252327 baseEnd_7252327 := by
    simpa [prefixWord, tailWord_7252327, baseEnd_7252327] using wordTrace_append hprefix tailTrace_7252327
  have hstable : (prefixWord ++ tailWord_7252327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252327).length < 2 ^ (prefixWord ++ tailWord_7252327).sum := by decide
  have hdescent : baseEnd_7252327 < baseStart_7252327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252341 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_7252341 : Nat := 118140960795 + 7252341 * 2 ^ 59
def prefixEnd_7252341 : Nat := 4983230072969 + 3 ^ 40 * 7252341 * 2
def baseEnd_7252341 : Nat := 3723936803308914916184597

theorem tailTrace_7252341 : CollatzResearch.WordTrace tailWord_7252341 prefixEnd_7252341 3723936803308914916184597 := by
  unfold tailWord_7252341
  simp only [CollatzResearch.WordTrace]
  refine ⟨264514607019014633077828877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176343071346009755385219251 264514607019014633077828877)
  ·
    refine ⟨99192977632130487404185829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264514607019014633077828877 99192977632130487404185829)
    ·
      refine ⟨18598683306024466388284843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99192977632130487404185829 18598683306024466388284843)
      ·
        refine ⟨27898024959036699582427265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18598683306024466388284843 27898024959036699582427265)
        ·
          refine ⟨20923518719277524686820449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27898024959036699582427265 20923518719277524686820449)
          ·
            refine ⟨15692639039458143515115337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20923518719277524686820449 15692639039458143515115337)
            ·
              refine ⟨11769479279593607636336503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15692639039458143515115337 11769479279593607636336503)
              ·
                refine ⟨17654218919390411454504755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11769479279593607636336503 17654218919390411454504755)
                ·
                  refine ⟨26481328379085617181757133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17654218919390411454504755 26481328379085617181757133)
                  ·
                    refine ⟨9930498142157106443158925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26481328379085617181757133 9930498142157106443158925)
                    ·
                      refine ⟨3723936803308914916184597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9930498142157106443158925 3723936803308914916184597)
                      ·
                        rfl

theorem cell23_7252341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_7252341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252341 prefixEnd_7252341 := by exact prefixLift 7252341
  have htrace : WordTrace (prefixWord ++ tailWord_7252341) baseStart_7252341 baseEnd_7252341 := by
    simpa [prefixWord, tailWord_7252341, baseEnd_7252341] using wordTrace_append hprefix tailTrace_7252341
  have hstable : (prefixWord ++ tailWord_7252341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252341).length < 2 ^ (prefixWord ++ tailWord_7252341).sum := by decide
  have hdescent : baseEnd_7252341 < baseStart_7252341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252362 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7252362 : Nat := 118140960795 + 7252362 * 2 ^ 59
def prefixEnd_7252362 : Nat := 4983230072969 + 3 ^ 40 * 7252362 * 2
def baseEnd_7252362 : Nat := 3723947586402659334022001

theorem tailTrace_7252362 : CollatzResearch.WordTrace tailWord_7252362 prefixEnd_7252362 3723947586402659334022001 := by
  unfold tailWord_7252362
  simp only [CollatzResearch.WordTrace]
  refine ⟨66128843237984638416085835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176343581967959035776228893 66128843237984638416085835)
  ·
    refine ⟨99193264856976957624128753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66128843237984638416085835 99193264856976957624128753)
    ·
      refine ⟨74394948642732718218096565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99193264856976957624128753 74394948642732718218096565)
      ·
        refine ⟨6974526435256192332946553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74394948642732718218096565 6974526435256192332946553)
        ·
          refine ⟨5230894826442144249709915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6974526435256192332946553 5230894826442144249709915)
          ·
            refine ⟨7846342239663216374564873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230894826442144249709915 7846342239663216374564873)
            ·
              refine ⟨5884756679747412280923655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7846342239663216374564873 5884756679747412280923655)
              ·
                refine ⟨8827135019621118421385483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5884756679747412280923655 8827135019621118421385483)
                ·
                  refine ⟨13240702529431677632078225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8827135019621118421385483 13240702529431677632078225)
                  ·
                    refine ⟨9930526897073758224058669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13240702529431677632078225 9930526897073758224058669)
                    ·
                      refine ⟨3723947586402659334022001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9930526897073758224058669 3723947586402659334022001)
                      ·
                        rfl

theorem cell23_7252362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7252362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252362 prefixEnd_7252362 := by exact prefixLift 7252362
  have htrace : WordTrace (prefixWord ++ tailWord_7252362) baseStart_7252362 baseEnd_7252362 := by
    simpa [prefixWord, tailWord_7252362, baseEnd_7252362] using wordTrace_append hprefix tailTrace_7252362
  have hstable : (prefixWord ++ tailWord_7252362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252362).length < 2 ^ (prefixWord ++ tailWord_7252362).sum := by decide
  have hdescent : baseEnd_7252362 < baseStart_7252362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252377 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 4]
def baseStart_7252377 : Nat := 118140960795 + 7252377 * 2 ^ 59
def prefixEnd_7252377 : Nat := 4983230072969 + 3 ^ 40 * 7252377 * 2
def baseEnd_7252377 : Nat := 3723955288612476775334431

theorem tailTrace_7252377 : CollatzResearch.WordTrace tailWord_7252377 prefixEnd_7252377 3723955288612476775334431 := by
  unfold tailWord_7252377
  simp only [CollatzResearch.WordTrace]
  refine ⟨264515920046884211226139385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176343946697922807484092923 264515920046884211226139385)
  ·
    refine ⟨198386940035163158419604539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264515920046884211226139385 198386940035163158419604539)
    ·
      refine ⟨297580410052744737629406809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198386940035163158419604539 297580410052744737629406809)
      ·
        refine ⟨223185307539558553222055107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297580410052744737629406809 223185307539558553222055107)
        ·
          refine ⟨334777961309337829833082661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223185307539558553222055107 334777961309337829833082661)
          ·
            refine ⟨62770867745500843093702999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334777961309337829833082661 62770867745500843093702999)
            ·
              refine ⟨94156301618251264640554499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62770867745500843093702999 94156301618251264640554499)
              ·
                refine ⟨141234452427376896960831749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94156301618251264640554499 141234452427376896960831749)
                ·
                  refine ⟨26481459830133168180155953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141234452427376896960831749 26481459830133168180155953)
                  ·
                    refine ⟨19861094872599876135116965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26481459830133168180155953 19861094872599876135116965)
                    ·
                      refine ⟨3723955288612476775334431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19861094872599876135116965 3723955288612476775334431)
                      ·
                        rfl

theorem cell23_7252377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_7252377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252377 prefixEnd_7252377 := by exact prefixLift 7252377
  have htrace : WordTrace (prefixWord ++ tailWord_7252377) baseStart_7252377 baseEnd_7252377 := by
    simpa [prefixWord, tailWord_7252377, baseEnd_7252377] using wordTrace_append hprefix tailTrace_7252377
  have hstable : (prefixWord ++ tailWord_7252377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252377).length < 2 ^ (prefixWord ++ tailWord_7252377).sum := by decide
  have hdescent : baseEnd_7252377 < baseStart_7252377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252387 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 7]
def baseStart_7252387 : Nat := 118140960795 + 7252387 * 2 ^ 59
def prefixEnd_7252387 : Nat := 4983230072969 + 3 ^ 40 * 7252387 * 2
def baseEnd_7252387 : Nat := 413773380379891304023265

theorem tailTrace_7252387 : CollatzResearch.WordTrace tailWord_7252387 prefixEnd_7252387 413773380379891304023265 := by
  unfold tailWord_7252387
  simp only [CollatzResearch.WordTrace]
  refine ⟨264516284776847982934003415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176344189851231988622668943 264516284776847982934003415)
  ·
    refine ⟨396774427165271974401005123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264516284776847982934003415 396774427165271974401005123)
    ·
      refine ⟨595161640747907961601507685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396774427165271974401005123 595161640747907961601507685)
      ·
        refine ⟨111592807640232742800282691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 595161640747907961601507685 111592807640232742800282691)
        ·
          refine ⟨167389211460349114200424037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111592807640232742800282691 167389211460349114200424037)
          ·
            refine ⟨31385477148815458912579507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167389211460349114200424037 31385477148815458912579507)
            ·
              refine ⟨47078215723223188368869261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31385477148815458912579507 47078215723223188368869261)
              ·
                refine ⟨17654330896208695638325973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47078215723223188368869261 17654330896208695638325973)
                ·
                  refine ⟨413773380379891304023265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17654330896208695638325973 413773380379891304023265)
                  ·
                    rfl

theorem cell23_7252387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 7].length) (baseStart_7252387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252387 prefixEnd_7252387 := by exact prefixLift 7252387
  have htrace : WordTrace (prefixWord ++ tailWord_7252387) baseStart_7252387 baseEnd_7252387 := by
    simpa [prefixWord, tailWord_7252387, baseEnd_7252387] using wordTrace_append hprefix tailTrace_7252387
  have hstable : (prefixWord ++ tailWord_7252387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252387).length < 2 ^ (prefixWord ++ tailWord_7252387).sum := by decide
  have hdescent : baseEnd_7252387 < baseStart_7252387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252414 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_7252414 : Nat := 118140960795 + 7252414 * 2 ^ 59
def prefixEnd_7252414 : Nat := 4983230072969 + 3 ^ 40 * 7252414 * 2
def baseEnd_7252414 : Nat := 3723974287396693130571761

theorem tailTrace_7252414 : CollatzResearch.WordTrace tailWord_7252414 prefixEnd_7252414 3723974287396693130571761 := by
  unfold tailWord_7252414
  simp only [CollatzResearch.WordTrace]
  refine ⟨33064658693468770818154537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176344846365166777696824197 33064658693468770818154537)
  ·
    refine ⟨24798494020101578113615903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33064658693468770818154537 24798494020101578113615903)
    ·
      refine ⟨37197741030152367170423855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24798494020101578113615903 37197741030152367170423855)
      ·
        refine ⟨55796611545228550755635783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37197741030152367170423855 55796611545228550755635783)
        ·
          refine ⟨83694917317842826133453675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55796611545228550755635783 83694917317842826133453675)
          ·
            refine ⟨125542375976764239200180513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83694917317842826133453675 125542375976764239200180513)
            ·
              refine ⟨94156781982573179400135385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125542375976764239200180513 94156781982573179400135385)
              ·
                refine ⟨70617586486929884550101539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94156781982573179400135385 70617586486929884550101539)
                ·
                  refine ⟨105926379730394826825152309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70617586486929884550101539 105926379730394826825152309)
                  ·
                    refine ⟨9930598099724515014858029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105926379730394826825152309 9930598099724515014858029)
                    ·
                      refine ⟨3723974287396693130571761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9930598099724515014858029 3723974287396693130571761)
                      ·
                        rfl

theorem cell23_7252414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_7252414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252414 prefixEnd_7252414 := by exact prefixLift 7252414
  have htrace : WordTrace (prefixWord ++ tailWord_7252414) baseStart_7252414 baseEnd_7252414 := by
    simpa [prefixWord, tailWord_7252414, baseEnd_7252414] using wordTrace_append hprefix tailTrace_7252414
  have hstable : (prefixWord ++ tailWord_7252414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252414).length < 2 ^ (prefixWord ++ tailWord_7252414).sum := by decide
  have hdescent : baseEnd_7252414 < baseStart_7252414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252427 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 5]
def baseStart_7252427 : Nat := 118140960795 + 7252427 * 2 ^ 59
def prefixEnd_7252427 : Nat := 4983230072969 + 3 ^ 40 * 7252427 * 2
def baseEnd_7252427 : Nat := 3723980962645201579709201

theorem tailTrace_7252427 : CollatzResearch.WordTrace tailWord_7252427 prefixEnd_7252427 3723980962645201579709201 := by
  unfold tailWord_7252427
  simp only [CollatzResearch.WordTrace]
  refine ⟨264517743696703069765459535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176345162464468713176973023 264517743696703069765459535)
  ·
    refine ⟨396776615545054604648189303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264517743696703069765459535 396776615545054604648189303)
    ·
      refine ⟨595164923317581906972283955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396776615545054604648189303 595164923317581906972283955)
      ·
        refine ⟨892747384976372860458425933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595164923317581906972283955 892747384976372860458425933)
        ·
          refine ⟨334780269366139822671909725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 892747384976372860458425933 334780269366139822671909725)
          ·
            refine ⟨125542601012302433501966147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334780269366139822671909725 125542601012302433501966147)
            ·
              refine ⟨188313901518453650252949221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125542601012302433501966147 188313901518453650252949221)
              ·
                refine ⟨35308856534710059422427979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188313901518453650252949221 35308856534710059422427979)
                ·
                  refine ⟨52963284802065089133641969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35308856534710059422427979 52963284802065089133641969)
                  ·
                    refine ⟨39722463601548816850231477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52963284802065089133641969 39722463601548816850231477)
                    ·
                      refine ⟨3723980962645201579709201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39722463601548816850231477 3723980962645201579709201)
                      ·
                        rfl

theorem cell23_7252427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 5].length) (baseStart_7252427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252427 prefixEnd_7252427 := by exact prefixLift 7252427
  have htrace : WordTrace (prefixWord ++ tailWord_7252427) baseStart_7252427 baseEnd_7252427 := by
    simpa [prefixWord, tailWord_7252427, baseEnd_7252427] using wordTrace_append hprefix tailTrace_7252427
  have hstable : (prefixWord ++ tailWord_7252427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252427).length < 2 ^ (prefixWord ++ tailWord_7252427).sum := by decide
  have hdescent : baseEnd_7252427 < baseStart_7252427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252464 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 5, 4]
def baseStart_7252464 : Nat := 118140960795 + 7252464 * 2 ^ 59
def prefixEnd_7252464 : Nat := 4983230072969 + 3 ^ 40 * 7252464 * 2
def baseEnd_7252464 : Nat := 1241333320476472644982177

theorem tailTrace_7252464 : CollatzResearch.WordTrace tailWord_7252464 prefixEnd_7252464 1241333320476472644982177 := by
  unfold tailWord_7252464
  simp only [CollatzResearch.WordTrace]
  refine ⟨132259546598784512542278223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176346062131712683389704297 132259546598784512542278223)
  ·
    refine ⟨198389319898176768813417335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132259546598784512542278223 198389319898176768813417335)
    ·
      refine ⟨297583979847265153220126003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198389319898176768813417335 297583979847265153220126003)
      ·
        refine ⟨446375969770897729830189005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297583979847265153220126003 446375969770897729830189005)
        ·
          refine ⟨167390988664086648686320877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446375969770897729830189005 167390988664086648686320877)
          ·
            refine ⟨62771620749032493257370329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167390988664086648686320877 62771620749032493257370329)
            ·
              refine ⟨47078715561774369943027747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62771620749032493257370329 47078715561774369943027747)
              ·
                refine ⟨70618073342661554914541621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47078715561774369943027747 70618073342661554914541621)
                ·
                  refine ⟨6620444375874520773238277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70618073342661554914541621 6620444375874520773238277)
                  ·
                    refine ⟨1241333320476472644982177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6620444375874520773238277 1241333320476472644982177)
                    ·
                      rfl

theorem cell23_7252464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5, 4].length) (baseStart_7252464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252464 prefixEnd_7252464 := by exact prefixLift 7252464
  have htrace : WordTrace (prefixWord ++ tailWord_7252464) baseStart_7252464 baseEnd_7252464 := by
    simpa [prefixWord, tailWord_7252464, baseEnd_7252464] using wordTrace_append hprefix tailTrace_7252464
  have hstable : (prefixWord ++ tailWord_7252464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252464).length < 2 ^ (prefixWord ++ tailWord_7252464).sum := by decide
  have hdescent : baseEnd_7252464 < baseStart_7252464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252491 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 3]
def baseStart_7252491 : Nat := 118140960795 + 7252491 * 2 ^ 59
def prefixEnd_7252491 : Nat := 4983230072969 + 3 ^ 40 * 7252491 * 2
def baseEnd_7252491 : Nat := 3724013825407089329308907

theorem tailTrace_7252491 : CollatzResearch.WordTrace tailWord_7252491 prefixEnd_7252491 3724013825407089329308907 := by
  unfold tailWord_7252491
  simp only [CollatzResearch.WordTrace]
  refine ⟨264520077968471208695789327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176346718645647472463859551 264520077968471208695789327)
  ·
    refine ⟨396780116952706813043683991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264520077968471208695789327 396780116952706813043683991)
    ·
      refine ⟨595170175429060219565525987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396780116952706813043683991 595170175429060219565525987)
      ·
        refine ⟨892755263143590329348288981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595170175429060219565525987 892755263143590329348288981)
        ·
          refine ⟨20923951479927898344100523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 892755263143590329348288981 20923951479927898344100523)
          ·
            refine ⟨31385927219891847516150785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20923951479927898344100523 31385927219891847516150785)
            ·
              refine ⟨23539445414918885637113089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31385927219891847516150785 23539445414918885637113089)
              ·
                refine ⟨17654584061189164227834817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23539445414918885637113089 17654584061189164227834817)
                ·
                  refine ⟨13240938045891873170876113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17654584061189164227834817 13240938045891873170876113)
                  ·
                    refine ⟨9930703534418904878157085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13240938045891873170876113 9930703534418904878157085)
                    ·
                      refine ⟨3724013825407089329308907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9930703534418904878157085 3724013825407089329308907)
                      ·
                        rfl

theorem cell23_7252491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 3].length) (baseStart_7252491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252491 prefixEnd_7252491 := by exact prefixLift 7252491
  have htrace : WordTrace (prefixWord ++ tailWord_7252491) baseStart_7252491 baseEnd_7252491 := by
    simpa [prefixWord, tailWord_7252491, baseEnd_7252491] using wordTrace_append hprefix tailTrace_7252491
  have hstable : (prefixWord ++ tailWord_7252491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252491).length < 2 ^ (prefixWord ++ tailWord_7252491).sum := by decide
  have hdescent : baseEnd_7252491 < baseStart_7252491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252531 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 1, 5, 2]
def baseStart_7252531 : Nat := 118140960795 + 7252531 * 2 ^ 59
def prefixEnd_7252531 : Nat := 4983230072969 + 3 ^ 40 * 7252531 * 2
def baseEnd_7252531 : Nat := 3724034364633269172808723

theorem tailTrace_7252531 : CollatzResearch.WordTrace tailWord_7252531 prefixEnd_7252531 3724034364633269172808723 := by
  unfold tailWord_7252531
  simp only [CollatzResearch.WordTrace]
  refine ⟨264521536888326295527245447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176347691258884197018163631 264521536888326295527245447)
  ·
    refine ⟨396782305332489443290868171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264521536888326295527245447 396782305332489443290868171)
    ·
      refine ⟨595173457998734164936302257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396782305332489443290868171 595173457998734164936302257)
      ·
        refine ⟨446380093499050623702226693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595173457998734164936302257 446380093499050623702226693)
        ·
          refine ⟨83696267531071991944167505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446380093499050623702226693 83696267531071991944167505)
          ·
            refine ⟨62772200648303993958125629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83696267531071991944167505 62772200648303993958125629)
            ·
              refine ⟨23539575243113997734297111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62772200648303993958125629 23539575243113997734297111)
              ·
                refine ⟨35309362864670996601445667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23539575243113997734297111 35309362864670996601445667)
                ·
                  refine ⟨52964044297006494902168501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35309362864670996601445667 52964044297006494902168501)
                  ·
                    refine ⟨4965379152844358897078297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52964044297006494902168501 4965379152844358897078297)
                    ·
                      refine ⟨3724034364633269172808723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965379152844358897078297 3724034364633269172808723)
                      ·
                        rfl

theorem cell23_7252531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 5, 2].length) (baseStart_7252531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252531 prefixEnd_7252531 := by exact prefixLift 7252531
  have htrace : WordTrace (prefixWord ++ tailWord_7252531) baseStart_7252531 baseEnd_7252531 := by
    simpa [prefixWord, tailWord_7252531, baseEnd_7252531] using wordTrace_append hprefix tailTrace_7252531
  have hstable : (prefixWord ++ tailWord_7252531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252531).length < 2 ^ (prefixWord ++ tailWord_7252531).sum := by decide
  have hdescent : baseEnd_7252531 < baseStart_7252531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252595 : List Nat := [1, 1, 1, 2, 2, 1, 1, 9, 1, 2, 2]
def baseStart_7252595 : Nat := 118140960795 + 7252595 * 2 ^ 59
def prefixEnd_7252595 : Nat := 4983230072969 + 3 ^ 40 * 7252595 * 2
def baseEnd_7252595 : Nat := 3724067227395156922408429

theorem tailTrace_7252595 : CollatzResearch.WordTrace tailWord_7252595 prefixEnd_7252595 3724067227395156922408429 := by
  unfold tailWord_7252595
  simp only [CollatzResearch.WordTrace]
  refine ⟨264523871160094434457575239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176349247440062956305050159 264523871160094434457575239)
  ·
    refine ⟨396785806740141651686362859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264523871160094434457575239 396785806740141651686362859)
    ·
      refine ⟨595178710110212477529544289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396785806740141651686362859 595178710110212477529544289)
      ·
        refine ⟨446384032582659358147158217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595178710110212477529544289 446384032582659358147158217)
        ·
          refine ⟨334788024436994518610368663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446384032582659358147158217 334788024436994518610368663)
          ·
            refine ⟨502182036655491777915552995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334788024436994518610368663 502182036655491777915552995)
            ·
              refine ⟨753273054983237666873329493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502182036655491777915552995 753273054983237666873329493)
              ·
                refine ⟨4413709306542408204335915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 753273054983237666873329493 4413709306542408204335915)
                ·
                  refine ⟨6620563959813612306503873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413709306542408204335915 6620563959813612306503873)
                  ·
                    refine ⟨4965422969860209229877905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6620563959813612306503873 4965422969860209229877905)
                    ·
                      refine ⟨3724067227395156922408429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965422969860209229877905 3724067227395156922408429)
                      ·
                        rfl

theorem cell23_7252595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 1, 2, 2].length) (baseStart_7252595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252595 prefixEnd_7252595 := by exact prefixLift 7252595
  have htrace : WordTrace (prefixWord ++ tailWord_7252595) baseStart_7252595 baseEnd_7252595 := by
    simpa [prefixWord, tailWord_7252595, baseEnd_7252595] using wordTrace_append hprefix tailTrace_7252595
  have hstable : (prefixWord ++ tailWord_7252595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252595).length < 2 ^ (prefixWord ++ tailWord_7252595).sum := by decide
  have hdescent : baseEnd_7252595 < baseStart_7252595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252612 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_7252612 : Nat := 118140960795 + 7252612 * 2 ^ 59
def prefixEnd_7252612 : Nat := 4983230072969 + 3 ^ 40 * 7252612 * 2
def baseEnd_7252612 : Nat := 3724075956566283355895851

theorem tailTrace_7252612 : CollatzResearch.WordTrace tailWord_7252612 prefixEnd_7252612 3724075956566283355895851 := by
  unfold tailWord_7252612
  simp only [CollatzResearch.WordTrace]
  refine ⟨132262245600516423180472045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176349660800688564240629393 132262245600516423180472045)
  ·
    refine ⟨49598342100193658692677017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132262245600516423180472045 49598342100193658692677017)
    ·
      refine ⟨37198756575145244019507763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49598342100193658692677017 37198756575145244019507763)
      ·
        refine ⟨55798134862717866029261645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37198756575145244019507763 55798134862717866029261645)
        ·
          refine ⟨20924300573519199760973117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55798134862717866029261645 20924300573519199760973117)
          ·
            refine ⟨7846612715069699910364919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20924300573519199760973117 7846612715069699910364919)
            ·
              refine ⟨11769919072604549865547379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7846612715069699910364919 11769919072604549865547379)
              ·
                refine ⟨17654878608906824798321069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11769919072604549865547379 17654878608906824798321069)
                ·
                  refine ⟨6620579478340059299370401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17654878608906824798321069 6620579478340059299370401)
                  ·
                    refine ⟨4965434608755044474527801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6620579478340059299370401 4965434608755044474527801)
                    ·
                      refine ⟨3724075956566283355895851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965434608755044474527801 3724075956566283355895851)
                      ·
                        rfl

theorem cell23_7252612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_7252612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252612 prefixEnd_7252612 := by exact prefixLift 7252612
  have htrace : WordTrace (prefixWord ++ tailWord_7252612) baseStart_7252612 baseEnd_7252612 := by
    simpa [prefixWord, tailWord_7252612, baseEnd_7252612] using wordTrace_append hprefix tailTrace_7252612
  have hstable : (prefixWord ++ tailWord_7252612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252612).length < 2 ^ (prefixWord ++ tailWord_7252612).sum := by decide
  have hdescent : baseEnd_7252612 < baseStart_7252612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252664 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_7252664 : Nat := 118140960795 + 7252664 * 2 ^ 59
def prefixEnd_7252664 : Nat := 4983230072969 + 3 ^ 40 * 7252664 * 2
def baseEnd_7252664 : Nat := 3724102657560317152445611

theorem tailTrace_7252664 : CollatzResearch.WordTrace tailWord_7252664 prefixEnd_7252664 3724102657560317152445611 := by
  unfold tailWord_7252664
  simp only [CollatzResearch.WordTrace]
  refine ⟨132263193898422229620918523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176350925197896306161224697 132263193898422229620918523)
  ·
    refine ⟨198394790847633344431377785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132263193898422229620918523 198394790847633344431377785)
    ·
      refine ⟨148796093135725008323533339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198394790847633344431377785 148796093135725008323533339)
      ·
        refine ⟨223194139703587512485300009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148796093135725008323533339 223194139703587512485300009)
        ·
          refine ⟨167395604777690634363975007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223194139703587512485300009 167395604777690634363975007)
          ·
            refine ⟨251093407166535951545962511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167395604777690634363975007 251093407166535951545962511)
            ·
              refine ⟨376640110749803927318943767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251093407166535951545962511 376640110749803927318943767)
              ·
                refine ⟨564960166124705890978415651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376640110749803927318943767 564960166124705890978415651)
                ·
                  refine ⟨847440249187058836467623477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564960166124705890978415651 847440249187058836467623477)
                  ·
                    refine ⟨79447523361286765918839701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 847440249187058836467623477 79447523361286765918839701)
                    ·
                      refine ⟨3724102657560317152445611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79447523361286765918839701 3724102657560317152445611)
                      ·
                        rfl

theorem cell23_7252664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_7252664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252664 prefixEnd_7252664 := by exact prefixLift 7252664
  have htrace : WordTrace (prefixWord ++ tailWord_7252664) baseStart_7252664 baseEnd_7252664 := by
    simpa [prefixWord, tailWord_7252664, baseEnd_7252664] using wordTrace_append hprefix tailTrace_7252664
  have hstable : (prefixWord ++ tailWord_7252664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252664).length < 2 ^ (prefixWord ++ tailWord_7252664).sum := by decide
  have hdescent : baseEnd_7252664 < baseStart_7252664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252668 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 3, 4, 2]
def baseStart_7252668 : Nat := 118140960795 + 7252668 * 2 ^ 59
def prefixEnd_7252668 : Nat := 4983230072969 + 3 ^ 40 * 7252668 * 2
def baseEnd_7252668 : Nat := 3724104711482935136795593

theorem tailTrace_7252668 : CollatzResearch.WordTrace tailWord_7252668 prefixEnd_7252668 3724104711482935136795593 := by
  unfold tailWord_7252668
  simp only [CollatzResearch.WordTrace]
  refine ⟨132263266844414983962491329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176351022459219978616655105 132263266844414983962491329)
  ·
    refine ⟨99197450133311237971868497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132263266844414983962491329 99197450133311237971868497)
    ·
      refine ⟨74398087599983428478901373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99197450133311237971868497 74398087599983428478901373)
      ·
        refine ⟨27899282849993785679588015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74398087599983428478901373 27899282849993785679588015)
        ·
          refine ⟨41848924274990678519382023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27899282849993785679588015 41848924274990678519382023)
          ·
            refine ⟨62773386412486017779073035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41848924274990678519382023 62773386412486017779073035)
            ·
              refine ⟨94160079618729026668609553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62773386412486017779073035 94160079618729026668609553)
              ·
                refine ⟨70620059714046770001457165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94160079618729026668609553 70620059714046770001457165)
                ·
                  refine ⟨26482522392767538750546437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70620059714046770001457165 26482522392767538750546437)
                  ·
                    refine ⟨4965472948643913515727457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26482522392767538750546437 4965472948643913515727457)
                    ·
                      refine ⟨3724104711482935136795593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965472948643913515727457 3724104711482935136795593)
                      ·
                        rfl

theorem cell23_7252668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_7252668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252668 prefixEnd_7252668 := by exact prefixLift 7252668
  have htrace : WordTrace (prefixWord ++ tailWord_7252668) baseStart_7252668 baseEnd_7252668 := by
    simpa [prefixWord, tailWord_7252668, baseEnd_7252668] using wordTrace_append hprefix tailTrace_7252668
  have hstable : (prefixWord ++ tailWord_7252668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252668).length < 2 ^ (prefixWord ++ tailWord_7252668).sum := by decide
  have hdescent : baseEnd_7252668 < baseStart_7252668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252671 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 3]
def baseStart_7252671 : Nat := 118140960795 + 7252671 * 2 ^ 59
def prefixEnd_7252671 : Nat := 4983230072969 + 3 ^ 40 * 7252671 * 2
def baseEnd_7252671 : Nat := 3724106251924898625058079

theorem tailTrace_7252671 : CollatzResearch.WordTrace tailWord_7252671 prefixEnd_7252671 3724106251924898625058079 := by
  unfold tailWord_7252671
  simp only [CollatzResearch.WordTrace]
  refine ⟨264526643107819099437341867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176351095405212732958227911 264526643107819099437341867)
  ·
    refine ⟨396789964661728649156012801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264526643107819099437341867 396789964661728649156012801)
    ·
      refine ⟨297592473496296486867009601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396789964661728649156012801 297592473496296486867009601)
      ·
        refine ⟨223194355122222365150257201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297592473496296486867009601 223194355122222365150257201)
        ·
          refine ⟨167395766341666773862692901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223194355122222365150257201 167395766341666773862692901)
          ·
            refine ⟨31386706189062520099254919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167395766341666773862692901 31386706189062520099254919)
            ·
              refine ⟨47080059283593780148882379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31386706189062520099254919 47080059283593780148882379)
              ·
                refine ⟨70620088925390670223323569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47080059283593780148882379 70620088925390670223323569)
                ·
                  refine ⟨52965066694043002667492677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70620088925390670223323569 52965066694043002667492677)
                  ·
                    refine ⟨9930950005133063000154877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52965066694043002667492677 9930950005133063000154877)
                    ·
                      refine ⟨3724106251924898625058079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9930950005133063000154877 3724106251924898625058079)
                      ·
                        rfl

theorem cell23_7252671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_7252671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252671 prefixEnd_7252671 := by exact prefixLift 7252671
  have htrace : WordTrace (prefixWord ++ tailWord_7252671) baseStart_7252671 baseEnd_7252671 := by
    simpa [prefixWord, tailWord_7252671, baseEnd_7252671] using wordTrace_append hprefix tailTrace_7252671
  have hstable : (prefixWord ++ tailWord_7252671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252671).length < 2 ^ (prefixWord ++ tailWord_7252671).sum := by decide
  have hdescent : baseEnd_7252671 < baseStart_7252671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252708 : List Nat := [2, 3, 1, 1, 1, 4, 1, 5, 5]
def baseStart_7252708 : Nat := 118140960795 + 7252708 * 2 ^ 59
def prefixEnd_7252708 : Nat := 4983230072969 + 3 ^ 40 * 7252708 * 2
def baseEnd_7252708 : Nat := 413791694523234997810601

theorem tailTrace_7252708 : CollatzResearch.WordTrace tailWord_7252708 prefixEnd_7252708 413791694523234997810601 := by
  unfold tailWord_7252708
  simp only [CollatzResearch.WordTrace]
  refine ⟨132263996304342527378219389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176351995072456703170959185 132263996304342527378219389)
  ·
    refine ⟨49598998614128447766832271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132263996304342527378219389 49598998614128447766832271)
    ·
      refine ⟨74398497921192671650248407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49598998614128447766832271 74398497921192671650248407)
      ·
        refine ⟨111597746881789007475372611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74398497921192671650248407 111597746881789007475372611)
        ·
          refine ⟨167396620322683511213058917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111597746881789007475372611 167396620322683511213058917)
          ·
            refine ⟨31386866310503158352448547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167396620322683511213058917 31386866310503158352448547)
            ·
              refine ⟨47080299465754737528672821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31386866310503158352448547 47080299465754737528672821)
              ·
                refine ⟨4413778074914506643313077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47080299465754737528672821 4413778074914506643313077)
                ·
                  refine ⟨413791694523234997810601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4413778074914506643313077 413791694523234997810601)
                  ·
                    rfl

theorem cell23_7252708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_7252708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252708 prefixEnd_7252708 := by exact prefixLift 7252708
  have htrace : WordTrace (prefixWord ++ tailWord_7252708) baseStart_7252708 baseEnd_7252708 := by
    simpa [prefixWord, tailWord_7252708, baseEnd_7252708] using wordTrace_append hprefix tailTrace_7252708
  have hstable : (prefixWord ++ tailWord_7252708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252708).length < 2 ^ (prefixWord ++ tailWord_7252708).sum := by decide
  have hdescent : baseEnd_7252708 < baseStart_7252708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252718 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_7252718 : Nat := 118140960795 + 7252718 * 2 ^ 59
def prefixEnd_7252718 : Nat := 4983230072969 + 3 ^ 40 * 7252718 * 2
def baseEnd_7252718 : Nat := 3724130385515659941170363

theorem tailTrace_7252718 : CollatzResearch.WordTrace tailWord_7252718 prefixEnd_7252718 3724130385515659941170363 := by
  unfold tailWord_7252718
  simp only [CollatzResearch.WordTrace]
  refine ⟨33066044667331103308037851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176352238225765884309535205 33066044667331103308037851)
  ·
    refine ⟨49599067000996654962056777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33066044667331103308037851 49599067000996654962056777)
    ·
      refine ⟨37199300250747491221542583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49599067000996654962056777 37199300250747491221542583)
      ·
        refine ⟨55798950376121236832313875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37199300250747491221542583 55798950376121236832313875)
        ·
          refine ⟨83698425564181855248470813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55798950376121236832313875 83698425564181855248470813)
          ·
            refine ⟨31386909586568195718176555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83698425564181855248470813 31386909586568195718176555)
            ·
              refine ⟨47080364379852293577264833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31386909586568195718176555 47080364379852293577264833)
              ·
                refine ⟨35310273284889220182948625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47080364379852293577264833 35310273284889220182948625)
                ·
                  refine ⟨26482704963666915137211469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35310273284889220182948625 26482704963666915137211469)
                  ·
                    refine ⟨9931014361375093176454301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26482704963666915137211469 9931014361375093176454301)
                    ·
                      refine ⟨3724130385515659941170363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9931014361375093176454301 3724130385515659941170363)
                      ·
                        rfl

theorem cell23_7252718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_7252718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252718 prefixEnd_7252718 := by exact prefixLift 7252718
  have htrace : WordTrace (prefixWord ++ tailWord_7252718) baseStart_7252718 baseEnd_7252718 := by
    simpa [prefixWord, tailWord_7252718, baseEnd_7252718] using wordTrace_append hprefix tailTrace_7252718
  have hstable : (prefixWord ++ tailWord_7252718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252718).length < 2 ^ (prefixWord ++ tailWord_7252718).sum := by decide
  have hdescent : baseEnd_7252718 < baseStart_7252718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252721 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 4, 5]
def baseStart_7252721 : Nat := 118140960795 + 7252721 * 2 ^ 59
def prefixEnd_7252721 : Nat := 4983230072969 + 3 ^ 40 * 7252721 * 2
def baseEnd_7252721 : Nat := 1241377308652541143144283

theorem tailTrace_7252721 : CollatzResearch.WordTrace tailWord_7252721 prefixEnd_7252721 1241377308652541143144283 := by
  unfold tailWord_7252721
  simp only [CollatzResearch.WordTrace]
  refine ⟨264528466757637957976662017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176352311171758638651108011 264528466757637957976662017)
  ·
    refine ⟨198396350068228468482496513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264528466757637957976662017 198396350068228468482496513)
    ·
      refine ⟨148797262551171351361872385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198396350068228468482496513 148797262551171351361872385)
      ·
        refine ⟨111597946913378513521404289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148797262551171351361872385 111597946913378513521404289)
        ·
          refine ⟨83698460185033885141053217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111597946913378513521404289 83698460185033885141053217)
          ·
            refine ⟨62773845138775413855789913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83698460185033885141053217 62773845138775413855789913)
            ·
              refine ⟨47080383854081560391842435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62773845138775413855789913 47080383854081560391842435)
              ·
                refine ⟨70620575781122340587763653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47080383854081560391842435 70620575781122340587763653)
                ·
                  refine ⟨13241357958960438860205685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70620575781122340587763653 13241357958960438860205685)
                  ·
                    refine ⟨1241377308652541143144283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13241357958960438860205685 1241377308652541143144283)
                    ·
                      rfl

theorem cell23_7252721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_7252721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252721 prefixEnd_7252721 := by exact prefixLift 7252721
  have htrace : WordTrace (prefixWord ++ tailWord_7252721) baseStart_7252721 baseEnd_7252721 := by
    simpa [prefixWord, tailWord_7252721, baseEnd_7252721] using wordTrace_append hprefix tailTrace_7252721
  have hstable : (prefixWord ++ tailWord_7252721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252721).length < 2 ^ (prefixWord ++ tailWord_7252721).sum := by decide
  have hdescent : baseEnd_7252721 < baseStart_7252721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252738 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_7252738 : Nat := 118140960795 + 7252738 * 2 ^ 59
def prefixEnd_7252738 : Nat := 4983230072969 + 3 ^ 40 * 7252738 * 2
def baseEnd_7252738 : Nat := 1241380218376249954306757

theorem tailTrace_7252738 : CollatzResearch.WordTrace tailWord_7252738 prefixEnd_7252738 1241380218376249954306757 := by
  unfold tailWord_7252738
  simp only [CollatzResearch.WordTrace]
  refine ⟨66132271699644092470007717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176352724532384246586687245 66132271699644092470007717)
  ·
    refine ⟨12399800943683267338126447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66132271699644092470007717 12399800943683267338126447)
    ·
      refine ⟨18599701415524901007189671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12399800943683267338126447 18599701415524901007189671)
      ·
        refine ⟨27899552123287351510784507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18599701415524901007189671 27899552123287351510784507)
        ·
          refine ⟨41849328184931027266176761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27899552123287351510784507 41849328184931027266176761)
          ·
            refine ⟨31386996138698270449632571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41849328184931027266176761 31386996138698270449632571)
            ·
              refine ⟨47080494208047405674448857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31386996138698270449632571 47080494208047405674448857)
              ·
                refine ⟨35310370656035554255836643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47080494208047405674448857 35310370656035554255836643)
                ·
                  refine ⟨52965555984053331383754965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35310370656035554255836643 52965555984053331383754965)
                  ·
                    refine ⟨1241380218376249954306757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52965555984053331383754965 1241380218376249954306757)
                    ·
                      rfl

theorem cell23_7252738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_7252738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252738 prefixEnd_7252738 := by exact prefixLift 7252738
  have htrace : WordTrace (prefixWord ++ tailWord_7252738) baseStart_7252738 baseEnd_7252738 := by
    simpa [prefixWord, tailWord_7252738, baseEnd_7252738] using wordTrace_append hprefix tailTrace_7252738
  have hstable : (prefixWord ++ tailWord_7252738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252738).length < 2 ^ (prefixWord ++ tailWord_7252738).sum := by decide
  have hdescent : baseEnd_7252738 < baseStart_7252738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252848 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 4]
def baseStart_7252848 : Nat := 118140960795 + 7252848 * 2 ^ 59
def prefixEnd_7252848 : Nat := 4983230072969 + 3 ^ 40 * 7252848 * 2
def baseEnd_7252848 : Nat := 3724197138000744432544765

theorem tailTrace_7252848 : CollatzResearch.WordTrace tailWord_7252848 prefixEnd_7252848 3724197138000744432544765 := by
  unfold tailWord_7252848
  simp only [CollatzResearch.WordTrace]
  refine ⟨132266549414088929333267599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176355399218785239111023465 132266549414088929333267599)
  ·
    refine ⟨198399824121133393999901399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132266549414088929333267599 198399824121133393999901399)
    ·
      refine ⟨297599736181700090999852099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198399824121133393999901399 297599736181700090999852099)
      ·
        refine ⟨446399604272550136499778149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297599736181700090999852099 446399604272550136499778149)
        ·
          refine ⟨83699925801103150593708403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446399604272550136499778149 83699925801103150593708403)
          ·
            refine ⟨125549888701654725890562605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83699925801103150593708403 125549888701654725890562605)
            ·
              refine ⟨47081208263120522208960977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125549888701654725890562605 47081208263120522208960977)
              ·
                refine ⟨35310906197340391656720733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47081208263120522208960977 35310906197340391656720733)
                ·
                  refine ⟨13241589824002646871270275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35310906197340391656720733 13241589824002646871270275)
                  ·
                    refine ⟨19862384736003970306905413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13241589824002646871270275 19862384736003970306905413)
                    ·
                      refine ⟨3724197138000744432544765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19862384736003970306905413 3724197138000744432544765)
                      ·
                        rfl

theorem cell23_7252848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_7252848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252848 prefixEnd_7252848 := by exact prefixLift 7252848
  have htrace : WordTrace (prefixWord ++ tailWord_7252848) baseStart_7252848 baseEnd_7252848 := by
    simpa [prefixWord, tailWord_7252848, baseEnd_7252848] using wordTrace_append hprefix tailTrace_7252848
  have hstable : (prefixWord ++ tailWord_7252848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252848).length < 2 ^ (prefixWord ++ tailWord_7252848).sum := by decide
  have hdescent : baseEnd_7252848 < baseStart_7252848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252858 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 6, 4]
def baseStart_7252858 : Nat := 118140960795 + 7252858 * 2 ^ 59
def prefixEnd_7252858 : Nat := 4983230072969 + 3 ^ 40 * 7252858 * 2
def baseEnd_7252858 : Nat := 1241400757602429797806573

theorem tailTrace_7252858 : CollatzResearch.WordTrace tailWord_7252858 prefixEnd_7252858 1241400757602429797806573 := by
  unfold tailWord_7252858
  simp only [CollatzResearch.WordTrace]
  refine ⟨66133365889535407593599807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176355642372094420249599485 66133365889535407593599807)
  ·
    refine ⟨99200048834303111390399711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66133365889535407593599807 99200048834303111390399711)
    ·
      refine ⟨148800073251454667085599567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99200048834303111390399711 148800073251454667085599567)
      ·
        refine ⟨223200109877182000628399351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148800073251454667085599567 223200109877182000628399351)
        ·
          refine ⟨334800164815773000942599027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223200109877182000628399351 334800164815773000942599027)
          ·
            refine ⟨502200247223659501413898541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334800164815773000942599027 502200247223659501413898541)
            ·
              refine ⟨188325092708872313030211953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502200247223659501413898541 188325092708872313030211953)
              ·
                refine ⟨141243819531654234772658965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188325092708872313030211953 141243819531654234772658965)
                ·
                  refine ⟨6620804040546292254968389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141243819531654234772658965 6620804040546292254968389)
                  ·
                    refine ⟨1241400757602429797806573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6620804040546292254968389 1241400757602429797806573)
                    ·
                      rfl

theorem cell23_7252858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_7252858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252858 prefixEnd_7252858 := by exact prefixLift 7252858
  have htrace : WordTrace (prefixWord ++ tailWord_7252858) baseStart_7252858 baseEnd_7252858 := by
    simpa [prefixWord, tailWord_7252858, baseEnd_7252858] using wordTrace_append hprefix tailTrace_7252858
  have hstable : (prefixWord ++ tailWord_7252858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252858).length < 2 ^ (prefixWord ++ tailWord_7252858).sum := by decide
  have hdescent : baseEnd_7252858 < baseStart_7252858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252891 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 8]
def baseStart_7252891 : Nat := 118140960795 + 7252891 * 2 ^ 59
def prefixEnd_7252891 : Nat := 4983230072969 + 3 ^ 40 * 7252891 * 2
def baseEnd_7252891 : Nat := 3724219217668887764307067

theorem tailTrace_7252891 : CollatzResearch.WordTrace tailWord_7252891 prefixEnd_7252891 3724219217668887764307067 := by
  unfold tailWord_7252891
  simp only [CollatzResearch.WordTrace]
  refine ⟨264534667167022077010350527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176356444778014718006900351 264534667167022077010350527)
  ·
    refine ⟨396802000750533115515525791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264534667167022077010350527 396802000750533115515525791)
    ·
      refine ⟨595203001125799673273288687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396802000750533115515525791 595203001125799673273288687)
      ·
        refine ⟨892804501688699509909933031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595203001125799673273288687 892804501688699509909933031)
        ·
          refine ⟨1339206752533049264864899547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892804501688699509909933031 1339206752533049264864899547)
          ·
            refine ⟨2008810128799573897297349321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339206752533049264864899547 2008810128799573897297349321)
            ·
              refine ⟨1506607596599680422973011991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2008810128799573897297349321 1506607596599680422973011991)
              ·
                refine ⟨2259911394899520634459517987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506607596599680422973011991 2259911394899520634459517987)
                ·
                  refine ⟨3389867092349280951689276981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259911394899520634459517987 3389867092349280951689276981)
                  ·
                    refine ⟨317800039907745089220869717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3389867092349280951689276981 317800039907745089220869717)
                    ·
                      refine ⟨3724219217668887764307067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 317800039907745089220869717 3724219217668887764307067)
                      ·
                        rfl

theorem cell23_7252891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_7252891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252891 prefixEnd_7252891 := by exact prefixLift 7252891
  have htrace : WordTrace (prefixWord ++ tailWord_7252891) baseStart_7252891 baseEnd_7252891 := by
    simpa [prefixWord, tailWord_7252891, baseEnd_7252891] using wordTrace_append hprefix tailTrace_7252891
  have hstable : (prefixWord ++ tailWord_7252891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252891).length < 2 ^ (prefixWord ++ tailWord_7252891).sum := by decide
  have hdescent : baseEnd_7252891 < baseStart_7252891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252892 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 4, 4]
def baseStart_7252892 : Nat := 118140960795 + 7252892 * 2 ^ 59
def prefixEnd_7252892 : Nat := 4983230072969 + 3 ^ 40 * 7252892 * 2
def baseEnd_7252892 : Nat := 1241406577049847420131521

theorem tailTrace_7252892 : CollatzResearch.WordTrace tailWord_7252892 prefixEnd_7252892 1241406577049847420131521 := by
  unfold tailWord_7252892
  simp only [CollatzResearch.WordTrace]
  refine ⟨132267351820009227090568465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176356469093345636120757953 132267351820009227090568465)
  ·
    refine ⟨99200513865006920317926349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132267351820009227090568465 99200513865006920317926349)
    ·
      refine ⟨37200192699377595119222381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99200513865006920317926349 37200192699377595119222381)
      ·
        refine ⟨13950072262266598169708393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37200192699377595119222381 13950072262266598169708393)
        ·
          refine ⟨10462554196699948627281295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13950072262266598169708393 10462554196699948627281295)
          ·
            refine ⟨15693831295049922940921943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10462554196699948627281295 15693831295049922940921943)
            ·
              refine ⟨23540746942574884411382915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15693831295049922940921943 23540746942574884411382915)
              ·
                refine ⟨35311120413862326617074373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23540746942574884411382915 35311120413862326617074373)
                ·
                  refine ⟨6620835077599186240701445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35311120413862326617074373 6620835077599186240701445)
                  ·
                    refine ⟨1241406577049847420131521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6620835077599186240701445 1241406577049847420131521)
                    ·
                      rfl

theorem cell23_7252892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_7252892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252892 prefixEnd_7252892 := by exact prefixLift 7252892
  have htrace : WordTrace (prefixWord ++ tailWord_7252892) baseStart_7252892 baseEnd_7252892 := by
    simpa [prefixWord, tailWord_7252892, baseEnd_7252892] using wordTrace_append hprefix tailTrace_7252892
  have hstable : (prefixWord ++ tailWord_7252892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252892).length < 2 ^ (prefixWord ++ tailWord_7252892).sum := by decide
  have hdescent : baseEnd_7252892 < baseStart_7252892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7252899 : List Nat := [1, 1, 1, 4, 1, 2, 4, 4, 1, 2, 2]
def baseStart_7252899 : Nat := 118140960795 + 7252899 * 2 ^ 59
def prefixEnd_7252899 : Nat := 4983230072969 + 3 ^ 40 * 7252899 * 2
def baseEnd_7252899 : Nat := 3724223325514123733007031

theorem tailTrace_7252899 : CollatzResearch.WordTrace tailWord_7252899 prefixEnd_7252899 3724223325514123733007031 := by
  unfold tailWord_7252899
  simp only [CollatzResearch.WordTrace]
  refine ⟨264534958950993094376641751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176356639300662062917761167 264534958950993094376641751)
  ·
    refine ⟨396802438426489641564962627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264534958950993094376641751 396802438426489641564962627)
    ·
      refine ⟨595203657639734462347443941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396802438426489641564962627 595203657639734462347443941)
      ·
        refine ⟨111600685807450211690145739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 595203657639734462347443941 111600685807450211690145739)
        ·
          refine ⟨167401028711175317535218609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111600685807450211690145739 167401028711175317535218609)
          ·
            refine ⟨125550771533381488151413957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167401028711175317535218609 125550771533381488151413957)
            ·
              refine ⟨23540769662509029028390117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125550771533381488151413957 23540769662509029028390117)
              ·
                refine ⟨4413894311720442942823147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23540769662509029028390117 4413894311720442942823147)
                ·
                  refine ⟨6620841467580664414234721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413894311720442942823147 6620841467580664414234721)
                  ·
                    refine ⟨4965631100685498310676041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6620841467580664414234721 4965631100685498310676041)
                    ·
                      refine ⟨3724223325514123733007031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4965631100685498310676041 3724223325514123733007031)
                      ·
                        rfl

theorem cell23_7252899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_7252899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7252899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7252899 prefixEnd_7252899 := by exact prefixLift 7252899
  have htrace : WordTrace (prefixWord ++ tailWord_7252899) baseStart_7252899 baseEnd_7252899 := by
    simpa [prefixWord, tailWord_7252899, baseEnd_7252899] using wordTrace_append hprefix tailTrace_7252899
  have hstable : (prefixWord ++ tailWord_7252899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7252899).length < 2 ^ (prefixWord ++ tailWord_7252899).sum := by decide
  have hdescent : baseEnd_7252899 < baseStart_7252899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7252899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
