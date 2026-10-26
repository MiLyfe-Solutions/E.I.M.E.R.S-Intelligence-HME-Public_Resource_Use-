import V185TrunkScan23Chunk0545

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3228320 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 2, 1, 3]
def baseStart_3228320 : Nat := 118140960795 + 3228320 * 2 ^ 59
def prefixEnd_3228320 : Nat := 4983230072969 + 3 ^ 40 * 3228320 * 2
def baseEnd_3228320 : Nat := 1657679866522914416853233

theorem tailTrace_3228320 : CollatzResearch.WordTrace tailWord_3228320 prefixEnd_3228320 1657679866522914416853233 := by
  unfold tailWord_3228320
  simp only [CollatzResearch.WordTrace]
  refine ⟨58873251832177734002821207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78497669109570312003761609 58873251832177734002821207)
  ·
    refine ⟨88309877748266601004231811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58873251832177734002821207 88309877748266601004231811)
    ·
      refine ⟨132464816622399901506347717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88309877748266601004231811 132464816622399901506347717)
      ·
        refine ⟨24837153116699981532440197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132464816622399901506347717 24837153116699981532440197)
        ·
          refine ⟨4656966209381246537332537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24837153116699981532440197 4656966209381246537332537)
          ·
            refine ⟨3492724657035934902999403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4656966209381246537332537 3492724657035934902999403)
            ·
              refine ⟨5239086985553902354499105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3492724657035934902999403 5239086985553902354499105)
              ·
                refine ⟨3929315239165426765874329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239086985553902354499105 3929315239165426765874329)
                ·
                  refine ⟨2946986429374070074405747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3929315239165426765874329 2946986429374070074405747)
                  ·
                    refine ⟨4420479644061105111608621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2946986429374070074405747 4420479644061105111608621)
                    ·
                      refine ⟨1657679866522914416853233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4420479644061105111608621 1657679866522914416853233)
                      ·
                        rfl

theorem cell23_3228320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_3228320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228320 prefixEnd_3228320 := by exact prefixLift 3228320
  have htrace : WordTrace (prefixWord ++ tailWord_3228320) baseStart_3228320 baseEnd_3228320 := by
    simpa [prefixWord, tailWord_3228320, baseEnd_3228320] using wordTrace_append hprefix tailTrace_3228320
  have hstable : (prefixWord ++ tailWord_3228320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228320).length < 2 ^ (prefixWord ++ tailWord_3228320).sum := by decide
  have hdescent : baseEnd_3228320 < baseStart_3228320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228337 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 2, 1, 3]
def baseStart_3228337 : Nat := 118140960795 + 3228337 * 2 ^ 59
def prefixEnd_3228337 : Nat := 4983230072969 + 3 ^ 40 * 3228337 * 2
def baseEnd_3228337 : Nat := 1657688595694040850340655

theorem tailTrace_3228337 : CollatzResearch.WordTrace tailWord_3228337 prefixEnd_3228337 1657688595694040850340655 := by
  unfold tailWord_3228337
  simp only [CollatzResearch.WordTrace]
  refine ⟨117747123705293879909011265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78498082470195919939340843 117747123705293879909011265)
  ·
    refine ⟨88310342778970409931758449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117747123705293879909011265 88310342778970409931758449)
    ·
      refine ⟨66232757084227807448818837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88310342778970409931758449 66232757084227807448818837)
      ·
        refine ⟨3104660488323178474163383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66232757084227807448818837 3104660488323178474163383)
        ·
          refine ⟨4656990732484767711245075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104660488323178474163383 4656990732484767711245075)
          ·
            refine ⟨6985486098727151566867613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4656990732484767711245075 6985486098727151566867613)
            ·
              refine ⟨2619557287022681837575355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6985486098727151566867613 2619557287022681837575355)
              ·
                refine ⟨3929335930534022756363033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619557287022681837575355 3929335930534022756363033)
                ·
                  refine ⟨2947001947900517067272275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3929335930534022756363033 2947001947900517067272275)
                  ·
                    refine ⟨4420502921850775600908413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2947001947900517067272275 4420502921850775600908413)
                    ·
                      refine ⟨1657688595694040850340655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4420502921850775600908413 1657688595694040850340655)
                      ·
                        rfl

theorem cell23_3228337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_3228337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228337 prefixEnd_3228337 := by exact prefixLift 3228337
  have htrace : WordTrace (prefixWord ++ tailWord_3228337) baseStart_3228337 baseEnd_3228337 := by
    simpa [prefixWord, tailWord_3228337, baseEnd_3228337] using wordTrace_append hprefix tailTrace_3228337
  have hstable : (prefixWord ++ tailWord_3228337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228337).length < 2 ^ (prefixWord ++ tailWord_3228337).sum := by decide
  have hdescent : baseEnd_3228337 < baseStart_3228337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228339 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 4]
def baseStart_3228339 : Nat := 118140960795 + 3228339 * 2 ^ 59
def prefixEnd_3228339 : Nat := 4983230072969 + 3 ^ 40 * 3228339 * 2
def baseEnd_3228339 : Nat := 1657689622655349842515645

theorem tailTrace_3228339 : CollatzResearch.WordTrace tailWord_3228339 prefixEnd_3228339 1657689622655349842515645 := by
  unfold tailWord_3228339
  simp only [CollatzResearch.WordTrace]
  refine ⟨117747196651286634250584071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78498131100857756167056047 117747196651286634250584071)
  ·
    refine ⟨176620794976929951375876107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117747196651286634250584071 176620794976929951375876107)
    ·
      refine ⟨264931192465394927063814161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176620794976929951375876107 264931192465394927063814161)
      ·
        refine ⟨198698394349046195297860621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264931192465394927063814161 198698394349046195297860621)
        ·
          refine ⟨74511897880892323236697733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198698394349046195297860621 74511897880892323236697733)
          ·
            refine ⟨13970980852667310606880825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74511897880892323236697733 13970980852667310606880825)
            ·
              refine ⟨10478235639500482955160619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13970980852667310606880825 10478235639500482955160619)
              ·
                refine ⟨15717353459250724432740929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10478235639500482955160619 15717353459250724432740929)
                ·
                  refine ⟨11788015094438043324555697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15717353459250724432740929 11788015094438043324555697)
                  ·
                    refine ⟨8841011320828532493416773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11788015094438043324555697 8841011320828532493416773)
                    ·
                      refine ⟨1657689622655349842515645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8841011320828532493416773 1657689622655349842515645)
                      ·
                        rfl

theorem cell23_3228339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_3228339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228339 prefixEnd_3228339 := by exact prefixLift 3228339
  have htrace : WordTrace (prefixWord ++ tailWord_3228339) baseStart_3228339 baseEnd_3228339 := by
    simpa [prefixWord, tailWord_3228339, baseEnd_3228339] using wordTrace_append hprefix tailTrace_3228339
  have hstable : (prefixWord ++ tailWord_3228339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228339).length < 2 ^ (prefixWord ++ tailWord_3228339).sum := by decide
  have hdescent : baseEnd_3228339 < baseStart_3228339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228349 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 7]
def baseStart_3228349 : Nat := 118140960795 + 3228349 * 2 ^ 59
def prefixEnd_3228349 : Nat := 4983230072969 + 3 ^ 40 * 3228349 * 2
def baseEnd_3228349 : Nat := 184188306384654978154511

theorem tailTrace_3228349 : CollatzResearch.WordTrace tailWord_3228349 prefixEnd_3228349 184188306384654978154511 := by
  unfold tailWord_3228349
  simp only [CollatzResearch.WordTrace]
  refine ⟨117747561381250405958448101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78498374254166937305632067 117747561381250405958448101)
  ·
    refine ⟨22077667758984451117209019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117747561381250405958448101 22077667758984451117209019)
    ·
      refine ⟨33116501638476676675813529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22077667758984451117209019 33116501638476676675813529)
      ·
        refine ⟨24837376228857507506860147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33116501638476676675813529 24837376228857507506860147)
        ·
          refine ⟨37256064343286261260290221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24837376228857507506860147 37256064343286261260290221)
          ·
            refine ⟨13971024128732347972608833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37256064343286261260290221 13971024128732347972608833)
            ·
              refine ⟨10478268096549260979456625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13971024128732347972608833 10478268096549260979456625)
              ·
                refine ⟨7858701072411945734592469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10478268096549260979456625 7858701072411945734592469)
                ·
                  refine ⟨184188306384654978154511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7858701072411945734592469 184188306384654978154511)
                  ·
                    rfl

theorem cell23_3228349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_3228349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228349 prefixEnd_3228349 := by exact prefixLift 3228349
  have htrace : WordTrace (prefixWord ++ tailWord_3228349) baseStart_3228349 baseEnd_3228349 := by
    simpa [prefixWord, tailWord_3228349, baseEnd_3228349] using wordTrace_append hprefix tailTrace_3228349
  have hstable : (prefixWord ++ tailWord_3228349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228349).length < 2 ^ (prefixWord ++ tailWord_3228349).sum := by decide
  have hdescent : baseEnd_3228349 < baseStart_3228349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228359 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_3228359 : Nat := 118140960795 + 3228359 * 2 ^ 59
def prefixEnd_3228359 : Nat := 4983230072969 + 3 ^ 40 * 3228359 * 2
def baseEnd_3228359 : Nat := 1657699892268439764265553

theorem tailTrace_3228359 : CollatzResearch.WordTrace tailWord_3228359 prefixEnd_3228359 1657699892268439764265553 := by
  unfold tailWord_3228359
  simp only [CollatzResearch.WordTrace]
  refine ⟨117747926111214177666312131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78498617407476118444208087 117747926111214177666312131)
  ·
    refine ⟨176621889166821266499468197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117747926111214177666312131 176621889166821266499468197)
    ·
      refine ⟨33116604218778987468650287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176621889166821266499468197 33116604218778987468650287)
      ·
        refine ⟨49674906328168481202975431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33116604218778987468650287 49674906328168481202975431)
        ·
          refine ⟨74512359492252721804463147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49674906328168481202975431 74512359492252721804463147)
          ·
            refine ⟨111768539238379082706694721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74512359492252721804463147 111768539238379082706694721)
            ·
              refine ⟨83826404428784312030021041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111768539238379082706694721 83826404428784312030021041)
              ·
                refine ⟨62869803321588234022515781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83826404428784312030021041 62869803321588234022515781)
                ·
                  refine ⟨11788088122797793879221709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62869803321588234022515781 11788088122797793879221709)
                  ·
                    refine ⟨4420533046049172704708141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11788088122797793879221709 4420533046049172704708141)
                    ·
                      refine ⟨1657699892268439764265553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4420533046049172704708141 1657699892268439764265553)
                      ·
                        rfl

theorem cell23_3228359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_3228359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228359 prefixEnd_3228359 := by exact prefixLift 3228359
  have htrace : WordTrace (prefixWord ++ tailWord_3228359) baseStart_3228359 baseEnd_3228359 := by
    simpa [prefixWord, tailWord_3228359, baseEnd_3228359] using wordTrace_append hprefix tailTrace_3228359
  have hstable : (prefixWord ++ tailWord_3228359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228359).length < 2 ^ (prefixWord ++ tailWord_3228359).sum := by decide
  have hdescent : baseEnd_3228359 < baseStart_3228359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228383 : List Nat := [1, 1, 2, 3, 2, 4, 3, 2, 5]
def baseStart_3228383 : Nat := 118140960795 + 3228383 * 2 ^ 59
def prefixEnd_3228383 : Nat := 4983230072969 + 3 ^ 40 * 3228383 * 2
def baseEnd_3228383 : Nat := 184190246200460852262827

theorem tailTrace_3228383 : CollatzResearch.WordTrace tailWord_3228383 prefixEnd_3228383 184190246200460852262827 := by
  unfold tailWord_3228383
  simp only [CollatzResearch.WordTrace]
  refine ⟨117748801463127229765185803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78499200975418153176790535 117748801463127229765185803)
  ·
    refine ⟨176623202194690844647778705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117748801463127229765185803 176623202194690844647778705)
    ·
      refine ⟨132467401646018133485834029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176623202194690844647778705 132467401646018133485834029)
      ·
        refine ⟨49675275617256800057187761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132467401646018133485834029 49675275617256800057187761)
        ·
          refine ⟨37256456712942600042890821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49675275617256800057187761 37256456712942600042890821)
          ·
            refine ⟨6985585633676737508042029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37256456712942600042890821 6985585633676737508042029)
            ·
              refine ⟨2619594612628776565515761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6985585633676737508042029 2619594612628776565515761)
              ·
                refine ⟨1964695959471582424136821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2619594612628776565515761 1964695959471582424136821)
                ·
                  refine ⟨184190246200460852262827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1964695959471582424136821 184190246200460852262827)
                  ·
                    rfl

theorem cell23_3228383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 5].length) (baseStart_3228383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228383 prefixEnd_3228383 := by exact prefixLift 3228383
  have htrace : WordTrace (prefixWord ++ tailWord_3228383) baseStart_3228383 baseEnd_3228383 := by
    simpa [prefixWord, tailWord_3228383, baseEnd_3228383] using wordTrace_append hprefix tailTrace_3228383
  have hstable : (prefixWord ++ tailWord_3228383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228383).length < 2 ^ (prefixWord ++ tailWord_3228383).sum := by decide
  have hdescent : baseEnd_3228383 < baseStart_3228383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228389 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3228389 : Nat := 118140960795 + 3228389 * 2 ^ 59
def prefixEnd_3228389 : Nat := 4983230072969 + 3 ^ 40 * 3228389 * 2
def baseEnd_3228389 : Nat := 1657715296688074646890415

theorem tailTrace_3228389 : CollatzResearch.WordTrace tailWord_3228389 prefixEnd_3228389 1657715296688074646890415 := by
  unfold tailWord_3228389
  simp only [CollatzResearch.WordTrace]
  refine ⟨117749020301105492789904221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78499346867403661859936147 117749020301105492789904221)
  ·
    refine ⟨44155882612914559796214083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117749020301105492789904221 44155882612914559796214083)
    ·
      refine ⟨66233823919371839694321125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44155882612914559796214083 66233823919371839694321125)
      ·
        refine ⟨12418841984882219942685211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66233823919371839694321125 12418841984882219942685211)
        ·
          refine ⟨18628262977323329914027817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12418841984882219942685211 18628262977323329914027817)
          ·
            refine ⟨13971197232992497435520863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18628262977323329914027817 13971197232992497435520863)
            ·
              refine ⟨20956795849488746153281295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13971197232992497435520863 20956795849488746153281295)
              ·
                refine ⟨31435193774233119229921943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20956795849488746153281295 31435193774233119229921943)
                ·
                  refine ⟨47152790661349678844882915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31435193774233119229921943 47152790661349678844882915)
                  ·
                    refine ⟨70729185992024518267324373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47152790661349678844882915 70729185992024518267324373)
                    ·
                      refine ⟨1657715296688074646890415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70729185992024518267324373 1657715296688074646890415)
                      ·
                        rfl

theorem cell23_3228389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3228389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228389 prefixEnd_3228389 := by exact prefixLift 3228389
  have htrace : WordTrace (prefixWord ++ tailWord_3228389) baseStart_3228389 baseEnd_3228389 := by
    simpa [prefixWord, tailWord_3228389, baseEnd_3228389] using wordTrace_append hprefix tailTrace_3228389
  have hstable : (prefixWord ++ tailWord_3228389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228389).length < 2 ^ (prefixWord ++ tailWord_3228389).sum := by decide
  have hdescent : baseEnd_3228389 < baseStart_3228389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228434 : List Nat := [3, 2, 4, 1, 3, 1, 2, 2, 5]
def baseStart_3228434 : Nat := 118140960795 + 3228434 * 2 ^ 59
def prefixEnd_3228434 : Nat := 4983230072969 + 3 ^ 40 * 3228434 * 2
def baseEnd_3228434 : Nat := 184193155924169663425301

theorem tailTrace_3228434 : CollatzResearch.WordTrace tailWord_3228434 prefixEnd_3228434 184193155924169663425301 := by
  unfold tailWord_3228434
  simp only [CollatzResearch.WordTrace]
  refine ⟨29437665396485616368823089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78500441057294976983528237 29437665396485616368823089)
  ·
    refine ⟨22078249047364212276617317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29437665396485616368823089 22078249047364212276617317)
    ·
      refine ⟨4139671696380789801865747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22078249047364212276617317 4139671696380789801865747)
      ·
        refine ⟨6209507544571184702798621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139671696380789801865747 6209507544571184702798621)
        ·
          refine ⟨2328565329214194263549483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6209507544571184702798621 2328565329214194263549483)
          ·
            refine ⟨3492847993821291395324225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328565329214194263549483 3492847993821291395324225)
            ·
              refine ⟨2619635995365968546493169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3492847993821291395324225 2619635995365968546493169)
              ·
                refine ⟨1964726996524476409869877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2619635995365968546493169 1964726996524476409869877)
                ·
                  refine ⟨184193155924169663425301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1964726996524476409869877 184193155924169663425301)
                  ·
                    rfl

theorem cell23_3228434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_3228434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228434 prefixEnd_3228434 := by exact prefixLift 3228434
  have htrace : WordTrace (prefixWord ++ tailWord_3228434) baseStart_3228434 baseEnd_3228434 := by
    simpa [prefixWord, tailWord_3228434, baseEnd_3228434] using wordTrace_append hprefix tailTrace_3228434
  have hstable : (prefixWord ++ tailWord_3228434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228434).length < 2 ^ (prefixWord ++ tailWord_3228434).sum := by decide
  have hdescent : baseEnd_3228434 < baseStart_3228434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228456 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 6]
def baseStart_3228456 : Nat := 118140960795 + 3228456 * 2 ^ 59
def prefixEnd_3228456 : Nat := 4983230072969 + 3 ^ 40 * 3228456 * 2
def baseEnd_3228456 : Nat := 184194411099102876083623

theorem tailTrace_3228456 : CollatzResearch.WordTrace tailWord_3228456 prefixEnd_3228456 184194411099102876083623 := by
  unfold tailWord_3228456
  simp only [CollatzResearch.WordTrace]
  refine ⟨58875731995931381616296611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78500975994575175488395481 58875731995931381616296611)
  ·
    refine ⟨88313597993897072424444917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58875731995931381616296611 88313597993897072424444917)
    ·
      refine ⟨8279399811927850539791711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88313597993897072424444917 8279399811927850539791711)
      ·
        refine ⟨12419099717891775809687567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8279399811927850539791711 12419099717891775809687567)
        ·
          refine ⟨18628649576837663714531351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12419099717891775809687567 18628649576837663714531351)
          ·
            refine ⟨27942974365256495571797027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18628649576837663714531351 27942974365256495571797027)
            ·
              refine ⟨41914461547884743357695541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27942974365256495571797027 41914461547884743357695541)
              ·
                refine ⟨3929480770114194689783957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41914461547884743357695541 3929480770114194689783957)
                ·
                  refine ⟨184194411099102876083623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3929480770114194689783957 184194411099102876083623)
                  ·
                    rfl

theorem cell23_3228456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 6].length) (baseStart_3228456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228456 prefixEnd_3228456 := by exact prefixLift 3228456
  have htrace : WordTrace (prefixWord ++ tailWord_3228456) baseStart_3228456 baseEnd_3228456 := by
    simpa [prefixWord, tailWord_3228456, baseEnd_3228456] using wordTrace_append hprefix tailTrace_3228456
  have hstable : (prefixWord ++ tailWord_3228456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228456).length < 2 ^ (prefixWord ++ tailWord_3228456).sum := by decide
  have hdescent : baseEnd_3228456 < baseStart_3228456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228470 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3228470 : Nat := 118140960795 + 3228470 * 2 ^ 59
def prefixEnd_3228470 : Nat := 4983230072969 + 3 ^ 40 * 3228470 * 2
def baseEnd_3228470 : Nat := 1657756888621088829977543

theorem tailTrace_3228470 : CollatzResearch.WordTrace tailWord_3228470 prefixEnd_3228470 1657756888621088829977543 := by
  unfold tailWord_3228470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7359498413363252726475179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78501316409208029082401909 7359498413363252726475179)
  ·
    refine ⟨11039247620044879089712769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7359498413363252726475179 11039247620044879089712769)
    ·
      refine ⟨8279435715033659317284577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11039247620044879089712769 8279435715033659317284577)
      ·
        refine ⟨6209576786275244487963433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8279435715033659317284577 6209576786275244487963433)
        ·
          refine ⟨4657182589706433365972575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6209576786275244487963433 4657182589706433365972575)
          ·
            refine ⟨6985773884559650048958863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657182589706433365972575 6985773884559650048958863)
            ·
              refine ⟨10478660826839475073438295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6985773884559650048958863 10478660826839475073438295)
              ·
                refine ⟨15717991240259212610157443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10478660826839475073438295 15717991240259212610157443)
                ·
                  refine ⟨23576986860388818915236165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15717991240259212610157443 23576986860388818915236165)
                  ·
                    refine ⟨4420685036322903546606781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23576986860388818915236165 4420685036322903546606781)
                    ·
                      refine ⟨1657756888621088829977543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4420685036322903546606781 1657756888621088829977543)
                      ·
                        rfl

theorem cell23_3228470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3228470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228470 prefixEnd_3228470 := by exact prefixLift 3228470
  have htrace : WordTrace (prefixWord ++ tailWord_3228470) baseStart_3228470 baseEnd_3228470 := by
    simpa [prefixWord, tailWord_3228470, baseEnd_3228470] using wordTrace_append hprefix tailTrace_3228470
  have hstable : (prefixWord ++ tailWord_3228470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228470).length < 2 ^ (prefixWord ++ tailWord_3228470).sum := by decide
  have hdescent : baseEnd_3228470 < baseStart_3228470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228477 : List Nat := [1, 4, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_3228477 : Nat := 118140960795 + 3228477 * 2 ^ 59
def prefixEnd_3228477 : Nat := 4983230072969 + 3 ^ 40 * 3228477 * 2
def baseEnd_3228477 : Nat := 552586827661890100863337

theorem tailTrace_3228477 : CollatzResearch.WordTrace tailWord_3228477 prefixEnd_3228477 552586827661890100863337 := by
  unfold tailWord_3228477
  simp only [CollatzResearch.WordTrace]
  refine ⟨117752229924786683819107685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78501486616524455879405123 117752229924786683819107685)
  ·
    refine ⟨22078543110897503216082691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117752229924786683819107685 22078543110897503216082691)
    ·
      refine ⟨33117814666346254824124037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22078543110897503216082691 33117814666346254824124037)
      ·
        refine ⟨6209590249939922779523257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33117814666346254824124037 6209590249939922779523257)
        ·
          refine ⟨4657192687454942084642443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6209590249939922779523257 4657192687454942084642443)
          ·
            refine ⟨6985789031182413126963665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657192687454942084642443 6985789031182413126963665)
            ·
              refine ⟨5239341773386809845222749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6985789031182413126963665 5239341773386809845222749)
              ·
                refine ⟨1964753165020053691958531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5239341773386809845222749 1964753165020053691958531)
                ·
                  refine ⟨2947129747530080537937797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964753165020053691958531 2947129747530080537937797)
                  ·
                    refine ⟨552586827661890100863337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2947129747530080537937797 552586827661890100863337)
                    ·
                      rfl

theorem cell23_3228477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_3228477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228477 prefixEnd_3228477 := by exact prefixLift 3228477
  have htrace : WordTrace (prefixWord ++ tailWord_3228477) baseStart_3228477 baseEnd_3228477 := by
    simpa [prefixWord, tailWord_3228477, baseEnd_3228477] using wordTrace_append hprefix tailTrace_3228477
  have hstable : (prefixWord ++ tailWord_3228477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228477).length < 2 ^ (prefixWord ++ tailWord_3228477).sum := by decide
  have hdescent : baseEnd_3228477 < baseStart_3228477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228499 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 3, 6]
def baseStart_3228499 : Nat := 118140960795 + 3228499 * 2 ^ 59
def prefixEnd_3228499 : Nat := 4983230072969 + 3 ^ 40 * 3228499 * 2
def baseEnd_3228499 : Nat := 552590593186689738838303

theorem tailTrace_3228499 : CollatzResearch.WordTrace tailWord_3228499 prefixEnd_3228499 552590593186689738838303 := by
  unfold tailWord_3228499
  simp only [CollatzResearch.WordTrace]
  refine ⟨117753032330706981576408551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78502021553804654384272367 117753032330706981576408551)
  ·
    refine ⟨176629548496060472364612827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117753032330706981576408551 176629548496060472364612827)
    ·
      refine ⟨264944322744090708546919241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176629548496060472364612827 264944322744090708546919241)
      ·
        refine ⟨198708242058068031410189431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264944322744090708546919241 198708242058068031410189431)
        ·
          refine ⟨298062363087102047115284147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198708242058068031410189431 298062363087102047115284147)
          ·
            refine ⟨447093544630653070672926221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298062363087102047115284147 447093544630653070672926221)
            ·
              refine ⟨167660079236494901502347333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 447093544630653070672926221 167660079236494901502347333)
              ·
                refine ⟨31436264856842794031690125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167660079236494901502347333 31436264856842794031690125)
                ·
                  refine ⟨11788599321316047761883797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31436264856842794031690125 11788599321316047761883797)
                  ·
                    refine ⟨552590593186689738838303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11788599321316047761883797 552590593186689738838303)
                    ·
                      rfl

theorem cell23_3228499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 6].length) (baseStart_3228499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228499 prefixEnd_3228499 := by exact prefixLift 3228499
  have htrace : WordTrace (prefixWord ++ tailWord_3228499) baseStart_3228499 baseEnd_3228499 := by
    simpa [prefixWord, tailWord_3228499, baseEnd_3228499] using wordTrace_append hprefix tailTrace_3228499
  have hstable : (prefixWord ++ tailWord_3228499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228499).length < 2 ^ (prefixWord ++ tailWord_3228499).sum := by decide
  have hdescent : baseEnd_3228499 < baseStart_3228499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228533 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 4, 4]
def baseStart_3228533 : Nat := 118140960795 + 3228533 * 2 ^ 59
def prefixEnd_3228533 : Nat := 4983230072969 + 3 ^ 40 * 3228533 * 2
def baseEnd_3228533 : Nat := 552596412634107361163251

theorem tailTrace_3228533 : CollatzResearch.WordTrace tailWord_3228533 prefixEnd_3228533 552596412634107361163251 := by
  unfold tailWord_3228533
  simp only [CollatzResearch.WordTrace]
  refine ⟨117754272412583805383146253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78502848275055870255430835 117754272412583805383146253)
  ·
    refine ⟨44157852154718927018679845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117754272412583805383146253 44157852154718927018679845)
    ·
      refine ⟨8279597279009798816002471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44157852154718927018679845 8279597279009798816002471)
      ·
        refine ⟨12419395918514698224003707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8279597279009798816002471 12419395918514698224003707)
        ·
          refine ⟨18629093877772047336005561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12419395918514698224003707 18629093877772047336005561)
          ·
            refine ⟨13971820408329035502004171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18629093877772047336005561 13971820408329035502004171)
            ·
              refine ⟨20957730612493553253006257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13971820408329035502004171 20957730612493553253006257)
              ·
                refine ⟨15718297959370164939754693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20957730612493553253006257 15718297959370164939754693)
                ·
                  refine ⟨2947180867381905926204005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15718297959370164939754693 2947180867381905926204005)
                  ·
                    refine ⟨552596412634107361163251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2947180867381905926204005 552596412634107361163251)
                    ·
                      rfl

theorem cell23_3228533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_3228533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228533 prefixEnd_3228533 := by exact prefixLift 3228533
  have htrace : WordTrace (prefixWord ++ tailWord_3228533) baseStart_3228533 baseEnd_3228533 := by
    simpa [prefixWord, tailWord_3228533, baseEnd_3228533] using wordTrace_append hprefix tailTrace_3228533
  have hstable : (prefixWord ++ tailWord_3228533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228533).length < 2 ^ (prefixWord ++ tailWord_3228533).sum := by decide
  have hdescent : baseEnd_3228533 < baseStart_3228533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228534 : List Nat := [5, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3228534 : Nat := 118140960795 + 3228534 * 2 ^ 59
def prefixEnd_3228534 : Nat := 4983230072969 + 3 ^ 40 * 3228534 * 2
def baseEnd_3228534 : Nat := 1657789751382976579577249

theorem tailTrace_3228534 : CollatzResearch.WordTrace tailWord_3228534 prefixEnd_3228534 1657789751382976579577249 := by
  unfold tailWord_3228534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7359644305348761409620791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78502872590386788369288437 7359644305348761409620791)
  ·
    refine ⟨11039466458023142114431187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7359644305348761409620791 11039466458023142114431187)
    ·
      refine ⟨16559199687034713171646781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11039466458023142114431187 16559199687034713171646781)
      ·
        refine ⟨6209699882638017439367543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16559199687034713171646781 6209699882638017439367543)
        ·
          refine ⟨9314549823957026159051315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6209699882638017439367543 9314549823957026159051315)
          ·
            refine ⟨13971824735935539238576973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9314549823957026159051315 13971824735935539238576973)
            ·
              refine ⟨5239434275975827214466365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13971824735935539238576973 5239434275975827214466365)
              ·
                refine ⟨1964787853490935205424887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5239434275975827214466365 1964787853490935205424887)
                ·
                  refine ⟨2947181780236402808137331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964787853490935205424887 2947181780236402808137331)
                  ·
                    refine ⟨4420772670354604212205997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2947181780236402808137331 4420772670354604212205997)
                    ·
                      refine ⟨1657789751382976579577249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4420772670354604212205997 1657789751382976579577249)
                      ·
                        rfl

theorem cell23_3228534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3228534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228534 prefixEnd_3228534 := by exact prefixLift 3228534
  have htrace : WordTrace (prefixWord ++ tailWord_3228534) baseStart_3228534 baseEnd_3228534 := by
    simpa [prefixWord, tailWord_3228534, baseEnd_3228534] using wordTrace_append hprefix tailTrace_3228534
  have hstable : (prefixWord ++ tailWord_3228534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228534).length < 2 ^ (prefixWord ++ tailWord_3228534).sum := by decide
  have hdescent : baseEnd_3228534 < baseStart_3228534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228543 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 1, 2, 3]
def baseStart_3228543 : Nat := 118140960795 + 3228543 * 2 ^ 59
def prefixEnd_3228543 : Nat := 4983230072969 + 3 ^ 40 * 3228543 * 2
def baseEnd_3228543 : Nat := 1657794372708867044364707

theorem tailTrace_3228543 : CollatzResearch.WordTrace tailWord_3228543 prefixEnd_3228543 1657794372708867044364707 := by
  unfold tailWord_3228543
  simp only [CollatzResearch.WordTrace]
  refine ⟨117754637142547577091010283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78503091428365051394006855 117754637142547577091010283)
  ·
    refine ⟨176631955713821365636515425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117754637142547577091010283 176631955713821365636515425)
    ·
      refine ⟨132473966785366024227386569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176631955713821365636515425 132473966785366024227386569)
      ·
        refine ⟨99355475089024518170539927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132473966785366024227386569 99355475089024518170539927)
        ·
          refine ⟨149033212633536777255809891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99355475089024518170539927 149033212633536777255809891)
          ·
            refine ⟨223549818950305165883714837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149033212633536777255809891 223549818950305165883714837)
            ·
              refine ⟨10478897763295554650799133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 223549818950305165883714837 10478897763295554650799133)
              ·
                refine ⟨3929586661235832994049675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10478897763295554650799133 3929586661235832994049675)
                ·
                  refine ⟨5894379991853749491074513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929586661235832994049675 5894379991853749491074513)
                  ·
                    refine ⟨4420784993890312118305885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5894379991853749491074513 4420784993890312118305885)
                    ·
                      refine ⟨1657794372708867044364707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4420784993890312118305885 1657794372708867044364707)
                      ·
                        rfl

theorem cell23_3228543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_3228543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228543 prefixEnd_3228543 := by exact prefixLift 3228543
  have htrace : WordTrace (prefixWord ++ tailWord_3228543) baseStart_3228543 baseEnd_3228543 := by
    simpa [prefixWord, tailWord_3228543, baseEnd_3228543] using wordTrace_append hprefix tailTrace_3228543
  have hstable : (prefixWord ++ tailWord_3228543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228543).length < 2 ^ (prefixWord ++ tailWord_3228543).sum := by decide
  have hdescent : baseEnd_3228543 < baseStart_3228543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228573 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_3228573 : Nat := 118140960795 + 3228573 * 2 ^ 59
def prefixEnd_3228573 : Nat := 4983230072969 + 3 ^ 40 * 3228573 * 2
def baseEnd_3228573 : Nat := 1657809777128501926989569

theorem tailTrace_3228573 : CollatzResearch.WordTrace tailWord_3228573 prefixEnd_3228573 1657809777128501926989569 := by
  unfold tailWord_3228573
  simp only [CollatzResearch.WordTrace]
  refine ⟨117755731332438892214602373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78503820888292594809734915 117755731332438892214602373)
  ·
    refine ⟨22079199624832292290237945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117755731332438892214602373 22079199624832292290237945)
    ·
      refine ⟨16559399718624219217678459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22079199624832292290237945 16559399718624219217678459)
      ·
        refine ⟨24839099577936328826517689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16559399718624219217678459 24839099577936328826517689)
        ·
          refine ⟨18629324683452246619888267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24839099577936328826517689 18629324683452246619888267)
          ·
            refine ⟨27943987025178369929832401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18629324683452246619888267 27943987025178369929832401)
            ·
              refine ⟨20957990268883777447374301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27943987025178369929832401 20957990268883777447374301)
              ·
                refine ⟨7859246350831416542765363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20957990268883777447374301 7859246350831416542765363)
                ·
                  refine ⟨11788869526247124814148045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7859246350831416542765363 11788869526247124814148045)
                  ·
                    refine ⟨4420826072342671805305517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11788869526247124814148045 4420826072342671805305517)
                    ·
                      refine ⟨1657809777128501926989569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4420826072342671805305517 1657809777128501926989569)
                      ·
                        rfl

theorem cell23_3228573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_3228573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228573 prefixEnd_3228573 := by exact prefixLift 3228573
  have htrace : WordTrace (prefixWord ++ tailWord_3228573) baseStart_3228573 baseEnd_3228573 := by
    simpa [prefixWord, tailWord_3228573, baseEnd_3228573] using wordTrace_append hprefix tailTrace_3228573
  have hstable : (prefixWord ++ tailWord_3228573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228573).length < 2 ^ (prefixWord ++ tailWord_3228573).sum := by decide
  have hdescent : baseEnd_3228573 < baseStart_3228573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228577 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3228577 : Nat := 118140960795 + 3228577 * 2 ^ 59
def prefixEnd_3228577 : Nat := 4983230072969 + 3 ^ 40 * 3228577 * 2
def baseEnd_3228577 : Nat := 1657811831051119911339551

theorem tailTrace_3228577 : CollatzResearch.WordTrace tailWord_3228577 prefixEnd_3228577 1657811831051119911339551 := by
  unfold tailWord_3228577
  simp only [CollatzResearch.WordTrace]
  refine ⟨117755877224424400897747985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78503918149616267265165323 117755877224424400897747985)
  ·
    refine ⟨88316907918318300673310989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117755877224424400897747985 88316907918318300673310989)
    ·
      refine ⟨33118840469369362752491621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88316907918318300673310989 33118840469369362752491621)
      ·
        refine ⟨6209782588006755516092179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33118840469369362752491621 6209782588006755516092179)
        ·
          refine ⟨9314673882010133274138269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6209782588006755516092179 9314673882010133274138269)
          ·
            refine ⟨3493002705753799977801851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9314673882010133274138269 3493002705753799977801851)
            ·
              refine ⟨5239504058630699966702777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493002705753799977801851 5239504058630699966702777)
              ·
                refine ⟨3929628043973024975027083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239504058630699966702777 3929628043973024975027083)
                ·
                  refine ⟨5894442065959537462540625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929628043973024975027083 5894442065959537462540625)
                  ·
                    refine ⟨4420831549469653096905469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5894442065959537462540625 4420831549469653096905469)
                    ·
                      refine ⟨1657811831051119911339551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4420831549469653096905469 1657811831051119911339551)
                      ·
                        rfl

theorem cell23_3228577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3228577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228577 prefixEnd_3228577 := by exact prefixLift 3228577
  have htrace : WordTrace (prefixWord ++ tailWord_3228577) baseStart_3228577 baseEnd_3228577 := by
    simpa [prefixWord, tailWord_3228577, baseEnd_3228577] using wordTrace_append hprefix tailTrace_3228577
  have hstable : (prefixWord ++ tailWord_3228577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228577).length < 2 ^ (prefixWord ++ tailWord_3228577).sum := by decide
  have hdescent : baseEnd_3228577 < baseStart_3228577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228703 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 4]
def baseStart_3228703 : Nat := 118140960795 + 3228703 * 2 ^ 59
def prefixEnd_3228703 : Nat := 4983230072969 + 3 ^ 40 * 3228703 * 2
def baseEnd_3228703 : Nat := 1657876529613586418363971

theorem tailTrace_3228703 : CollatzResearch.WordTrace tailWord_3228703 prefixEnd_3228703 1657876529613586418363971 := by
  unfold tailWord_3228703
  simp only [CollatzResearch.WordTrace]
  refine ⟨117760472821967924416834763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78506981881311949611223175 117760472821967924416834763)
  ·
    refine ⟨176640709232951886625252145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117760472821967924416834763 176640709232951886625252145)
    ·
      refine ⟨132480531924713914968939109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176640709232951886625252145 132480531924713914968939109)
      ·
        refine ⟨24840099735883859056676083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132480531924713914968939109 24840099735883859056676083)
        ·
          refine ⟨37260149603825788585014125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24840099735883859056676083 37260149603825788585014125)
          ·
            refine ⟨13972556101434670719380297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37260149603825788585014125 13972556101434670719380297)
            ·
              refine ⟨10479417076076003039535223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13972556101434670719380297 10479417076076003039535223)
              ·
                refine ⟨15719125614114004559302835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10479417076076003039535223 15719125614114004559302835)
                ·
                  refine ⟨23578688421171006838954253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15719125614114004559302835 23578688421171006838954253)
                  ·
                    refine ⟨8842008157939127564607845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23578688421171006838954253 8842008157939127564607845)
                    ·
                      refine ⟨1657876529613586418363971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8842008157939127564607845 1657876529613586418363971)
                      ·
                        rfl

theorem cell23_3228703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_3228703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228703 prefixEnd_3228703 := by exact prefixLift 3228703
  have htrace : WordTrace (prefixWord ++ tailWord_3228703) baseStart_3228703 baseEnd_3228703 := by
    simpa [prefixWord, tailWord_3228703, baseEnd_3228703] using wordTrace_append hprefix tailTrace_3228703
  have hstable : (prefixWord ++ tailWord_3228703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228703).length < 2 ^ (prefixWord ++ tailWord_3228703).sum := by decide
  have hdescent : baseEnd_3228703 < baseStart_3228703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228704 : List Nat := [2, 1, 1, 7, 1, 2, 1, 3, 5]
def baseStart_3228704 : Nat := 118140960795 + 3228704 * 2 ^ 59
def prefixEnd_3228704 : Nat := 4983230072969 + 3 ^ 40 * 3228704 * 2
def baseEnd_3228704 : Nat := 184208560343804546050163

theorem tailTrace_3228704 : CollatzResearch.WordTrace tailWord_3228704 prefixEnd_3228704 184208560343804546050163 := by
  unfold tailWord_3228704
  simp only [CollatzResearch.WordTrace]
  refine ⟨58880254647482150793810583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78507006196642867725080777 58880254647482150793810583)
  ·
    refine ⟨88320381971223226190715875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58880254647482150793810583 88320381971223226190715875)
    ·
      refine ⟨132480572956834839286073813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88320381971223226190715875 132480572956834839286073813)
      ·
        refine ⟨3105013428675816545767355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 132480572956834839286073813 3105013428675816545767355)
        ·
          refine ⟨4657520143013724818651033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105013428675816545767355 4657520143013724818651033)
          ·
            refine ⟨3493140107260293613988275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4657520143013724818651033 3493140107260293613988275)
            ·
              refine ⟨5239710160890440420982413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493140107260293613988275 5239710160890440420982413)
              ·
                refine ⟨1964891310333915157868405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5239710160890440420982413 1964891310333915157868405)
                ·
                  refine ⟨184208560343804546050163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1964891310333915157868405 184208560343804546050163)
                  ·
                    rfl

theorem cell23_3228704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 5].length) (baseStart_3228704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228704 prefixEnd_3228704 := by exact prefixLift 3228704
  have htrace : WordTrace (prefixWord ++ tailWord_3228704) baseStart_3228704 baseEnd_3228704 := by
    simpa [prefixWord, tailWord_3228704, baseEnd_3228704] using wordTrace_append hprefix tailTrace_3228704
  have hstable : (prefixWord ++ tailWord_3228704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228704).length < 2 ^ (prefixWord ++ tailWord_3228704).sum := by decide
  have hdescent : baseEnd_3228704 < baseStart_3228704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228730 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 3, 4]
def baseStart_3228730 : Nat := 118140960795 + 3228730 * 2 ^ 59
def prefixEnd_3228730 : Nat := 4983230072969 + 3 ^ 40 * 3228730 * 2
def baseEnd_3228730 : Nat := 552630131197085937575449

theorem tailTrace_3228730 : CollatzResearch.WordTrace tailWord_3228730 prefixEnd_3228730 552630131197085937575449 := by
  unfold tailWord_3228730
  simp only [CollatzResearch.WordTrace]
  refine ⟨29440364398217527007016911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78507638395246738685378429 29440364398217527007016911)
  ·
    refine ⟨44160546597326290510525367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29440364398217527007016911 44160546597326290510525367)
    ·
      refine ⟨66240819895989435765788051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44160546597326290510525367 66240819895989435765788051)
      ·
        refine ⟨99361229843984153648682077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66240819895989435765788051 99361229843984153648682077)
        ·
          refine ⟨37260461191494057618255779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99361229843984153648682077 37260461191494057618255779)
          ·
            refine ⟨55890691787241086427383669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37260461191494057618255779 55890691787241086427383669)
            ·
              refine ⟨5239752355053851852567219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55890691787241086427383669 5239752355053851852567219)
              ·
                refine ⟨7859628532580777778850829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5239752355053851852567219 7859628532580777778850829)
                ·
                  refine ⟨2947360699717791667069061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7859628532580777778850829 2947360699717791667069061)
                  ·
                    refine ⟨552630131197085937575449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2947360699717791667069061 552630131197085937575449)
                    ·
                      rfl

theorem cell23_3228730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_3228730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228730 prefixEnd_3228730 := by exact prefixLift 3228730
  have htrace : WordTrace (prefixWord ++ tailWord_3228730) baseStart_3228730 baseEnd_3228730 := by
    simpa [prefixWord, tailWord_3228730, baseEnd_3228730] using wordTrace_append hprefix tailTrace_3228730
  have hstable : (prefixWord ++ tailWord_3228730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228730).length < 2 ^ (prefixWord ++ tailWord_3228730).sum := by decide
  have hdescent : baseEnd_3228730 < baseStart_3228730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228753 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 2, 5, 3]
def baseStart_3228753 : Nat := 118140960795 + 3228753 * 2 ^ 59
def prefixEnd_3228753 : Nat := 4983230072969 + 3 ^ 40 * 3228753 * 2
def baseEnd_3228753 : Nat := 1657902203646311222738741

theorem tailTrace_3228753 : CollatzResearch.WordTrace tailWord_3228753 prefixEnd_3228753 1657902203646311222738741 := by
  unfold tailWord_3228753
  simp only [CollatzResearch.WordTrace]
  refine ⟨117762296471786782956154913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78508197647857855304103275 117762296471786782956154913)
  ·
    refine ⟨88321722353840087217116185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117762296471786782956154913 88321722353840087217116185)
    ·
      refine ⟨66241291765380065412837139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88321722353840087217116185 66241291765380065412837139)
      ·
        refine ⟨99361937648070098119255709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66241291765380065412837139 99361937648070098119255709)
        ·
          refine ⟨37260726618026286794720891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99361937648070098119255709 37260726618026286794720891)
          ·
            refine ⟨55891089927039430192081337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37260726618026286794720891 55891089927039430192081337)
            ·
              refine ⟨41918317445279572644061003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55891089927039430192081337 41918317445279572644061003)
              ·
                refine ⟨62877476167919358966091505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41918317445279572644061003 62877476167919358966091505)
                ·
                  refine ⟨47158107125939519224568629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62877476167919358966091505 47158107125939519224568629)
                  ·
                    refine ⟨4421072543056829927303309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47158107125939519224568629 4421072543056829927303309)
                    ·
                      refine ⟨1657902203646311222738741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4421072543056829927303309 1657902203646311222738741)
                      ·
                        rfl

theorem cell23_3228753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_3228753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228753 prefixEnd_3228753 := by exact prefixLift 3228753
  have htrace : WordTrace (prefixWord ++ tailWord_3228753) baseStart_3228753 baseEnd_3228753 := by
    simpa [prefixWord, tailWord_3228753, baseEnd_3228753] using wordTrace_append hprefix tailTrace_3228753
  have hstable : (prefixWord ++ tailWord_3228753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228753).length < 2 ^ (prefixWord ++ tailWord_3228753).sum := by decide
  have hdescent : baseEnd_3228753 < baseStart_3228753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228781 : List Nat := [1, 5, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_3228781 : Nat := 118140960795 + 3228781 * 2 ^ 59
def prefixEnd_3228781 : Nat := 4983230072969 + 3 ^ 40 * 3228781 * 2
def baseEnd_3228781 : Nat := 552638860368212371062871

theorem tailTrace_3228781 : CollatzResearch.WordTrace tailWord_3228781 prefixEnd_3228781 552638860368212371062871 := by
  unfold tailWord_3228781
  simp only [CollatzResearch.WordTrace]
  refine ⟨117763317715685343738174197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78508878477123562492116131 117763317715685343738174197)
  ·
    refine ⟨11040311035845500975453831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117763317715685343738174197 11040311035845500975453831)
    ·
      refine ⟨16560466553768251463180747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11040311035845500975453831 16560466553768251463180747)
      ·
        refine ⟨24840699830652377194771121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16560466553768251463180747 24840699830652377194771121)
        ·
          refine ⟨18630524872989282896078341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24840699830652377194771121 18630524872989282896078341)
          ·
            refine ⟨3493223413685490543014689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18630524872989282896078341 3493223413685490543014689)
            ·
              refine ⟨2619917560264117907261017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3493223413685490543014689 2619917560264117907261017)
              ·
                refine ⟨1964938170198088430445763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2619917560264117907261017 1964938170198088430445763)
                ·
                  refine ⟨2947407255297132645668645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964938170198088430445763 2947407255297132645668645)
                  ·
                    refine ⟨552638860368212371062871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2947407255297132645668645 552638860368212371062871)
                    ·
                      rfl

theorem cell23_3228781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_3228781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228781 prefixEnd_3228781 := by exact prefixLift 3228781
  have htrace : WordTrace (prefixWord ++ tailWord_3228781) baseStart_3228781 baseEnd_3228781 := by
    simpa [prefixWord, tailWord_3228781, baseEnd_3228781] using wordTrace_append hprefix tailTrace_3228781
  have hstable : (prefixWord ++ tailWord_3228781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228781).length < 2 ^ (prefixWord ++ tailWord_3228781).sum := by decide
  have hdescent : baseEnd_3228781 < baseStart_3228781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228790 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_3228790 : Nat := 118140960795 + 3228790 * 2 ^ 59
def prefixEnd_3228790 : Nat := 4983230072969 + 3 ^ 40 * 3228790 * 2
def baseEnd_3228790 : Nat := 552640400810175859325357

theorem tailTrace_3228790 : CollatzResearch.WordTrace tailWord_3228790 prefixEnd_3228790 552640400810175859325357 := by
  unfold tailWord_3228790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7360227873290796142203239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78509097315101825516834549 7360227873290796142203239)
  ·
    refine ⟨11040341809936194213304859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7360227873290796142203239 11040341809936194213304859)
    ·
      refine ⟨16560512714904291319957289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11040341809936194213304859 16560512714904291319957289)
      ·
        refine ⟨12420384536178218489967967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16560512714904291319957289 12420384536178218489967967)
        ·
          refine ⟨18630576804267327734951951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12420384536178218489967967 18630576804267327734951951)
          ·
            refine ⟨27945865206400991602427927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18630576804267327734951951 27945865206400991602427927)
            ·
              refine ⟨41918797809601487403641891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27945865206400991602427927 41918797809601487403641891)
              ·
                refine ⟨62878196714402231105462837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41918797809601487403641891 62878196714402231105462837)
                ·
                  refine ⟨5894830941975209166137141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62878196714402231105462837 5894830941975209166137141)
                  ·
                    refine ⟨552640400810175859325357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5894830941975209166137141 552640400810175859325357)
                    ·
                      rfl

theorem cell23_3228790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_3228790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228790 prefixEnd_3228790 := by exact prefixLift 3228790
  have htrace : WordTrace (prefixWord ++ tailWord_3228790) baseStart_3228790 baseEnd_3228790 := by
    simpa [prefixWord, tailWord_3228790, baseEnd_3228790] using wordTrace_append hprefix tailTrace_3228790
  have hstable : (prefixWord ++ tailWord_3228790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228790).length < 2 ^ (prefixWord ++ tailWord_3228790).sum := by decide
  have hdescent : baseEnd_3228790 < baseStart_3228790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228810 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3228810 : Nat := 118140960795 + 3228810 * 2 ^ 59
def prefixEnd_3228810 : Nat := 4983230072969 + 3 ^ 40 * 3228810 * 2
def baseEnd_3228810 : Nat := 1657931472043617499725979

theorem tailTrace_3228810 : CollatzResearch.WordTrace tailWord_3228810 prefixEnd_3228810 1657931472043617499725979 := by
  unfold tailWord_3228810
  simp only [CollatzResearch.WordTrace]
  refine ⟨29441093858145070422744971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78509583621720187793986589 29441093858145070422744971)
  ·
    refine ⟨44161640787217605634117457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29441093858145070422744971 44161640787217605634117457)
    ·
      refine ⟨33121230590413204225588093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44161640787217605634117457 33121230590413204225588093)
      ·
        refine ⟨12420461471404951584595535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33121230590413204225588093 12420461471404951584595535)
        ·
          refine ⟨18630692207107427376893303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12420461471404951584595535 18630692207107427376893303)
          ·
            refine ⟨27946038310661141065339955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18630692207107427376893303 27946038310661141065339955)
            ·
              refine ⟨41919057465991711598009933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27946038310661141065339955 41919057465991711598009933)
              ·
                refine ⟨15719646549746891849253725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41919057465991711598009933 15719646549746891849253725)
                ·
                  refine ⟨5894867456155084443470147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15719646549746891849253725 5894867456155084443470147)
                  ·
                    refine ⟨8842301184232626665205221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5894867456155084443470147 8842301184232626665205221)
                    ·
                      refine ⟨1657931472043617499725979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8842301184232626665205221 1657931472043617499725979)
                      ·
                        rfl

theorem cell23_3228810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3228810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228810 prefixEnd_3228810 := by exact prefixLift 3228810
  have htrace : WordTrace (prefixWord ++ tailWord_3228810) baseStart_3228810 baseEnd_3228810 := by
    simpa [prefixWord, tailWord_3228810, baseEnd_3228810] using wordTrace_append hprefix tailTrace_3228810
  have hstable : (prefixWord ++ tailWord_3228810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228810).length < 2 ^ (prefixWord ++ tailWord_3228810).sum := by decide
  have hdescent : baseEnd_3228810 < baseStart_3228810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228814 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2]
def baseStart_3228814 : Nat := 118140960795 + 3228814 * 2 ^ 59
def prefixEnd_3228814 : Nat := 4983230072969 + 3 ^ 40 * 3228814 * 2
def baseEnd_3228814 : Nat := 1657933525966235484075961

theorem tailTrace_3228814 : CollatzResearch.WordTrace tailWord_3228814 prefixEnd_3228814 1657933525966235484075961 := by
  unfold tailWord_3228814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14720565165570723796765687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78509680883043860249416997 14720565165570723796765687)
  ·
    refine ⟨22080847748356085695148531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14720565165570723796765687 22080847748356085695148531)
    ·
      refine ⟨33121271622534128542722797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22080847748356085695148531 33121271622534128542722797)
      ·
        refine ⟨12420476858450298203521049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33121271622534128542722797 12420476858450298203521049)
        ·
          refine ⟨9315357643837723652640787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12420476858450298203521049 9315357643837723652640787)
          ·
            refine ⟨13973036465756585478961181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9315357643837723652640787 13973036465756585478961181)
            ·
              refine ⟨5239888674658719554610443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13973036465756585478961181 5239888674658719554610443)
              ·
                refine ⟨7859833011988079331915665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5239888674658719554610443 7859833011988079331915665)
                ·
                  refine ⟨5894874758991059498936749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7859833011988079331915665 5894874758991059498936749)
                  ·
                    refine ⟨2210578034621647312101281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5894874758991059498936749 2210578034621647312101281)
                    ·
                      refine ⟨1657933525966235484075961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2210578034621647312101281 1657933525966235484075961)
                      ·
                        rfl

theorem cell23_3228814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_3228814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228814 prefixEnd_3228814 := by exact prefixLift 3228814
  have htrace : WordTrace (prefixWord ++ tailWord_3228814) baseStart_3228814 baseEnd_3228814 := by
    simpa [prefixWord, tailWord_3228814, baseEnd_3228814] using wordTrace_append hprefix tailTrace_3228814
  have hstable : (prefixWord ++ tailWord_3228814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228814).length < 2 ^ (prefixWord ++ tailWord_3228814).sum := by decide
  have hdescent : baseEnd_3228814 < baseStart_3228814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228824 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 1, 5]
def baseStart_3228824 : Nat := 118140960795 + 3228824 * 2 ^ 59
def prefixEnd_3228824 : Nat := 4983230072969 + 3 ^ 40 * 3228824 * 2
def baseEnd_3228824 : Nat := 552646220257593481650305

theorem tailTrace_3228824 : CollatzResearch.WordTrace tailWord_3228824 prefixEnd_3228824 552646220257593481650305 := by
  unfold tailWord_3228824
  simp only [CollatzResearch.WordTrace]
  refine ⟨58882443027264781040994763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78509924036353041387993017 58882443027264781040994763)
  ·
    refine ⟨88323664540897171561492145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58882443027264781040994763 88323664540897171561492145)
    ·
      refine ⟨66242748405672878671119109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88323664540897171561492145 66242748405672878671119109)
      ·
        refine ⟨12420515326063664750834833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66242748405672878671119109 12420515326063664750834833)
        ·
          refine ⟨9315386494547748563126125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12420515326063664750834833 9315386494547748563126125)
          ·
            refine ⟨3493269935455405711172297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9315386494547748563126125 3493269935455405711172297)
            ·
              refine ⟨2619952451591554283379223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3493269935455405711172297 2619952451591554283379223)
              ·
                refine ⟨3929928677387331425068835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619952451591554283379223 3929928677387331425068835)
                ·
                  refine ⟨5894893016080997137603253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929928677387331425068835 5894893016080997137603253)
                  ·
                    refine ⟨552646220257593481650305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5894893016080997137603253 552646220257593481650305)
                    ·
                      rfl

theorem cell23_3228824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_3228824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228824 prefixEnd_3228824 := by exact prefixLift 3228824
  have htrace : WordTrace (prefixWord ++ tailWord_3228824) baseStart_3228824 baseEnd_3228824 := by
    simpa [prefixWord, tailWord_3228824, baseEnd_3228824] using wordTrace_append hprefix tailTrace_3228824
  have hstable : (prefixWord ++ tailWord_3228824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228824).length < 2 ^ (prefixWord ++ tailWord_3228824).sum := by decide
  have hdescent : baseEnd_3228824 < baseStart_3228824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228833 : List Nat := [1, 2, 3, 3, 1, 1, 12]
def baseStart_3228833 : Nat := 118140960795 + 3228833 * 2 ^ 59
def prefixEnd_3228833 : Nat := 4983230072969 + 3 ^ 40 * 3228833 * 2
def baseEnd_3228833 : Nat := 20468435581465072959733

theorem tailTrace_3228833 : CollatzResearch.WordTrace tailWord_3228833 prefixEnd_3228833 20468435581465072959733 := by
  unfold tailWord_3228833
  simp only [CollatzResearch.WordTrace]
  refine ⟨117765214311496956619067153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78510142874331304412711435 117765214311496956619067153)
  ·
    refine ⟨88323910733622717464300365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117765214311496956619067153 88323910733622717464300365)
    ·
      refine ⟨33121466525108519049112637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88323910733622717464300365 33121466525108519049112637)
      ·
        refine ⟨12420549946915694643417239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33121466525108519049112637 12420549946915694643417239)
        ·
          refine ⟨18630824920373541965125859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12420549946915694643417239 18630824920373541965125859)
          ·
            refine ⟨27946237380560312947688789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18630824920373541965125859 27946237380560312947688789)
            ·
              refine ⟨20468435581465072959733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 27946237380560312947688789 20468435581465072959733)
              ·
                rfl

theorem cell23_3228833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 12].length) (baseStart_3228833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228833 prefixEnd_3228833 := by exact prefixLift 3228833
  have htrace : WordTrace (prefixWord ++ tailWord_3228833) baseStart_3228833 baseEnd_3228833 := by
    simpa [prefixWord, tailWord_3228833, baseEnd_3228833] using wordTrace_append hprefix tailTrace_3228833
  have hstable : (prefixWord ++ tailWord_3228833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228833).length < 2 ^ (prefixWord ++ tailWord_3228833).sum := by decide
  have hdescent : baseEnd_3228833 < baseStart_3228833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228837 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 2, 4]
def baseStart_3228837 : Nat := 118140960795 + 3228837 * 2 ^ 59
def prefixEnd_3228837 : Nat := 4983230072969 + 3 ^ 40 * 3228837 * 2
def baseEnd_3228837 : Nat := 552648445340429631362785

theorem tailTrace_3228837 : CollatzResearch.WordTrace tailWord_3228837 prefixEnd_3228837 552648445340429631362785 := by
  unfold tailWord_3228837
  simp only [CollatzResearch.WordTrace]
  refine ⟨117765360203482465302212765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78510240135654976868141843 117765360203482465302212765)
  ·
    refine ⟨44162010076305924488329787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117765360203482465302212765 44162010076305924488329787)
    ·
      refine ⟨66243015114458886732494681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44162010076305924488329787 66243015114458886732494681)
      ·
        refine ⟨49682261335844165049371011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66243015114458886732494681 49682261335844165049371011)
        ·
          refine ⟨74523392003766247574056517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49682261335844165049371011 74523392003766247574056517)
          ·
            refine ⟨13973136000706171420135597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74523392003766247574056517 13973136000706171420135597)
            ·
              refine ⟨5239926000264814282550849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13973136000706171420135597 5239926000264814282550849)
              ·
                refine ⟨3929944500198610711913137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239926000264814282550849 3929944500198610711913137)
                ·
                  refine ⟨2947458375148958033934853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3929944500198610711913137 2947458375148958033934853)
                  ·
                    refine ⟨552648445340429631362785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2947458375148958033934853 552648445340429631362785)
                    ·
                      rfl

theorem cell23_3228837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_3228837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228837 prefixEnd_3228837 := by exact prefixLift 3228837
  have htrace : WordTrace (prefixWord ++ tailWord_3228837) baseStart_3228837 baseEnd_3228837 := by
    simpa [prefixWord, tailWord_3228837, baseEnd_3228837] using wordTrace_append hprefix tailTrace_3228837
  have hstable : (prefixWord ++ tailWord_3228837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228837).length < 2 ^ (prefixWord ++ tailWord_3228837).sum := by decide
  have hdescent : baseEnd_3228837 < baseStart_3228837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228857 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3228857 : Nat := 118140960795 + 3228857 * 2 ^ 59
def prefixEnd_3228857 : Nat := 4983230072969 + 3 ^ 40 * 3228857 * 2
def baseEnd_3228857 : Nat := 1657955605634378815838263

theorem tailTrace_3228857 : CollatzResearch.WordTrace tailWord_3228857 prefixEnd_3228857 1657955605634378815838263 := by
  unfold tailWord_3228857
  simp only [CollatzResearch.WordTrace]
  refine ⟨117766089663410008717940825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78510726442273339145293883 117766089663410008717940825)
  ·
    refine ⟨88324567247557506538455619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117766089663410008717940825 88324567247557506538455619)
    ·
      refine ⟨132486850871336259807683429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88324567247557506538455619 132486850871336259807683429)
      ·
        refine ⟨24841284538375548713940643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132486850871336259807683429 24841284538375548713940643)
        ·
          refine ⟨37261926807563323070910965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24841284538375548713940643 37261926807563323070910965)
          ·
            refine ⟨3493305638209061537897903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37261926807563323070910965 3493305638209061537897903)
            ·
              refine ⟨5239958457313592306846855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493305638209061537897903 5239958457313592306846855)
              ·
                refine ⟨7859937685970388460270283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5239958457313592306846855 7859937685970388460270283)
                ·
                  refine ⟨11789906528955582690405425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7859937685970388460270283 11789906528955582690405425)
                  ·
                    refine ⟨8842429896716687017804069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11789906528955582690405425 8842429896716687017804069)
                    ·
                      refine ⟨1657955605634378815838263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8842429896716687017804069 1657955605634378815838263)
                      ·
                        rfl

theorem cell23_3228857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3228857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228857 prefixEnd_3228857 := by exact prefixLift 3228857
  have htrace : WordTrace (prefixWord ++ tailWord_3228857) baseStart_3228857 baseEnd_3228857 := by
    simpa [prefixWord, tailWord_3228857, baseEnd_3228857] using wordTrace_append hprefix tailTrace_3228857
  have hstable : (prefixWord ++ tailWord_3228857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228857).length < 2 ^ (prefixWord ++ tailWord_3228857).sum := by decide
  have hdescent : baseEnd_3228857 < baseStart_3228857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228863 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 2, 7]
def baseStart_3228863 : Nat := 118140960795 + 3228863 * 2 ^ 59
def prefixEnd_3228863 : Nat := 4983230072969 + 3 ^ 40 * 3228863 * 2
def baseEnd_3228863 : Nat := 552652895506101930787745

theorem tailTrace_3228863 : CollatzResearch.WordTrace tailWord_3228863 prefixEnd_3228863 552652895506101930787745 := by
  unfold tailWord_3228863
  simp only [CollatzResearch.WordTrace]
  refine ⟨117766308501388271742659243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78510872334258847828439495 117766308501388271742659243)
  ·
    refine ⟨176649462752082407613988865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117766308501388271742659243 176649462752082407613988865)
    ·
      refine ⟨132487097064061805710491649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176649462752082407613988865 132487097064061805710491649)
      ·
        refine ⟨99365322798046354282868737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132487097064061805710491649 99365322798046354282868737)
        ·
          refine ⟨74523992098534765712151553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99365322798046354282868737 74523992098534765712151553)
          ·
            refine ⟨55892994073901074284113665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74523992098534765712151553 55892994073901074284113665)
            ·
              refine ⟨41919745555425805713085249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55892994073901074284113665 41919745555425805713085249)
              ·
                refine ⟨31439809166569354284813937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41919745555425805713085249 31439809166569354284813937)
                ·
                  refine ⟨23579856874927015713610453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31439809166569354284813937 23579856874927015713610453)
                  ·
                    refine ⟨552652895506101930787745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23579856874927015713610453 552652895506101930787745)
                    ·
                      rfl

theorem cell23_3228863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_3228863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228863 prefixEnd_3228863 := by exact prefixLift 3228863
  have htrace : WordTrace (prefixWord ++ tailWord_3228863) baseStart_3228863 baseEnd_3228863 := by
    simpa [prefixWord, tailWord_3228863, baseEnd_3228863] using wordTrace_append hprefix tailTrace_3228863
  have hstable : (prefixWord ++ tailWord_3228863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228863).length < 2 ^ (prefixWord ++ tailWord_3228863).sum := by decide
  have hdescent : baseEnd_3228863 < baseStart_3228863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228864 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 3]
def baseStart_3228864 : Nat := 118140960795 + 3228864 * 2 ^ 59
def prefixEnd_3228864 : Nat := 4983230072969 + 3 ^ 40 * 3228864 * 2
def baseEnd_3228864 : Nat := 1657959199998960288450731

theorem tailTrace_3228864 : CollatzResearch.WordTrace tailWord_3228864 prefixEnd_3228864 1657959199998960288450731 := by
  unfold tailWord_3228864
  simp only [CollatzResearch.WordTrace]
  refine ⟨58883172487192324456722823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78510896649589765942297097 58883172487192324456722823)
  ·
    refine ⟨88324758730788486685084235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58883172487192324456722823 88324758730788486685084235)
    ·
      refine ⟨132487138096182730027626353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88324758730788486685084235 132487138096182730027626353)
      ·
        refine ⟨99365353572137047520719765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132487138096182730027626353 99365353572137047520719765)
        ·
          refine ⟨4657750948693924102533739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99365353572137047520719765 4657750948693924102533739)
          ·
            refine ⟨6986626423040886153800609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657750948693924102533739 6986626423040886153800609)
            ·
              refine ⟨5239969817280664615350457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6986626423040886153800609 5239969817280664615350457)
              ·
                refine ⟨3929977362960498461512843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239969817280664615350457 3929977362960498461512843)
                ·
                  refine ⟨5894966044440747692269265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929977362960498461512843 5894966044440747692269265)
                  ·
                    refine ⟨4421224533330560769201949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5894966044440747692269265 4421224533330560769201949)
                    ·
                      refine ⟨1657959199998960288450731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4421224533330560769201949 1657959199998960288450731)
                      ·
                        rfl

theorem cell23_3228864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_3228864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228864 prefixEnd_3228864 := by exact prefixLift 3228864
  have htrace : WordTrace (prefixWord ++ tailWord_3228864) baseStart_3228864 baseEnd_3228864 := by
    simpa [prefixWord, tailWord_3228864, baseEnd_3228864] using wordTrace_append hprefix tailTrace_3228864
  have hstable : (prefixWord ++ tailWord_3228864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228864).length < 2 ^ (prefixWord ++ tailWord_3228864).sum := by decide
  have hdescent : baseEnd_3228864 < baseStart_3228864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228884 : List Nat := [2, 4, 1, 4, 2, 1, 9]
def baseStart_3228884 : Nat := 118140960795 + 3228884 * 2 ^ 59
def prefixEnd_3228884 : Nat := 4983230072969 + 3 ^ 40 * 3228884 * 2
def baseEnd_3228884 : Nat := 20468758884099385311119

theorem tailTrace_3228884 : CollatzResearch.WordTrace tailWord_3228884 prefixEnd_3228884 20468758884099385311119 := by
  unfold tailWord_3228884
  simp only [CollatzResearch.WordTrace]
  refine ⟨58883537217156096164586853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78511382956208128219449137 58883537217156096164586853)
  ·
    refine ⟨11040663228216768030860035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58883537217156096164586853 11040663228216768030860035)
    ·
      refine ⟨16560994842325152046290053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11040663228216768030860035 16560994842325152046290053)
      ·
        refine ⟨3105186532935966008679385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16560994842325152046290053 3105186532935966008679385)
        ·
          refine ⟨2328889899701974506509539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3105186532935966008679385 2328889899701974506509539)
          ·
            refine ⟨3493334849552961759764309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328889899701974506509539 3493334849552961759764309)
            ·
              refine ⟨20468758884099385311119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3493334849552961759764309 20468758884099385311119)
              ·
                rfl

theorem cell23_3228884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 9].length) (baseStart_3228884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228884 prefixEnd_3228884 := by exact prefixLift 3228884
  have htrace : WordTrace (prefixWord ++ tailWord_3228884) baseStart_3228884 baseEnd_3228884 := by
    simpa [prefixWord, tailWord_3228884, baseEnd_3228884] using wordTrace_append hprefix tailTrace_3228884
  have hstable : (prefixWord ++ tailWord_3228884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228884).length < 2 ^ (prefixWord ++ tailWord_3228884).sum := by decide
  have hdescent : baseEnd_3228884 < baseStart_3228884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228910 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3228910 : Nat := 118140960795 + 3228910 * 2 ^ 59
def prefixEnd_3228910 : Nat := 4983230072969 + 3 ^ 40 * 3228910 * 2
def baseEnd_3228910 : Nat := 552660940036355702825173

theorem tailTrace_3228910 : CollatzResearch.WordTrace tailWord_3228910 prefixEnd_3228910 552660940036355702825173 := by
  unfold tailWord_3228910
  simp only [CollatzResearch.WordTrace]
  refine ⟨14721002841527249846202523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78512015154811999179746789 14721002841527249846202523)
  ·
    refine ⟨22081504262290874769303785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14721002841527249846202523 22081504262290874769303785)
    ·
      refine ⟨16561128196718156076977839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22081504262290874769303785 16561128196718156076977839)
      ·
        refine ⟨24841692295077234115466759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16561128196718156076977839 24841692295077234115466759)
        ·
          refine ⟨37262538442615851173200139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24841692295077234115466759 37262538442615851173200139)
          ·
            refine ⟨55893807663923776759800209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37262538442615851173200139 55893807663923776759800209)
            ·
              refine ⟨41920355747942832569850157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55893807663923776759800209 41920355747942832569850157)
              ·
                refine ⟨15720133405478562213693809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41920355747942832569850157 15720133405478562213693809)
                ·
                  refine ⟨11790100054108921660270357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15720133405478562213693809 11790100054108921660270357)
                  ·
                    refine ⟨552660940036355702825173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11790100054108921660270357 552660940036355702825173)
                    ·
                      rfl

theorem cell23_3228910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3228910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228910 prefixEnd_3228910 := by exact prefixLift 3228910
  have htrace : WordTrace (prefixWord ++ tailWord_3228910) baseStart_3228910 baseEnd_3228910 := by
    simpa [prefixWord, tailWord_3228910, baseEnd_3228910] using wordTrace_append hprefix tailTrace_3228910
  have hstable : (prefixWord ++ tailWord_3228910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228910).length < 2 ^ (prefixWord ++ tailWord_3228910).sum := by decide
  have hdescent : baseEnd_3228910 < baseStart_3228910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3228951 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 2, 2, 2]
def baseStart_3228951 : Nat := 118140960795 + 3228951 * 2 ^ 59
def prefixEnd_3228951 : Nat := 4983230072969 + 3 ^ 40 * 3228951 * 2
def baseEnd_3228951 : Nat := 1658003872815901448062831

theorem tailTrace_3228951 : CollatzResearch.WordTrace tailWord_3228951 prefixEnd_3228951 1658003872815901448062831 := by
  unfold tailWord_3228951
  simp only [CollatzResearch.WordTrace]
  refine ⟨117769518125069462771862707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78513012083379641847908471 117769518125069462771862707)
  ·
    refine ⟨176654277187604194157794061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117769518125069462771862707 176654277187604194157794061)
    ·
      refine ⟨66245353945351572809172773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176654277187604194157794061 66245353945351572809172773)
      ·
        refine ⟨12421003864753419901719895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66245353945351572809172773 12421003864753419901719895)
        ·
          refine ⟨18631505797130129852579843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12421003864753419901719895 18631505797130129852579843)
          ·
            refine ⟨27947258695695194778869765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18631505797130129852579843 27947258695695194778869765)
            ·
              refine ⟨5240111005442849021038081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27947258695695194778869765 5240111005442849021038081)
              ·
                refine ⟨3930083254082136765778561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5240111005442849021038081 3930083254082136765778561)
                ·
                  refine ⟨2947562440561602574333921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3930083254082136765778561 2947562440561602574333921)
                  ·
                    refine ⟨2210671830421201930750441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2947562440561602574333921 2210671830421201930750441)
                    ·
                      refine ⟨1658003872815901448062831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2210671830421201930750441 1658003872815901448062831)
                      ·
                        rfl

theorem cell23_3228951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_3228951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3228951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3228951 prefixEnd_3228951 := by exact prefixLift 3228951
  have htrace : WordTrace (prefixWord ++ tailWord_3228951) baseStart_3228951 baseEnd_3228951 := by
    simpa [prefixWord, tailWord_3228951, baseEnd_3228951] using wordTrace_append hprefix tailTrace_3228951
  have hstable : (prefixWord ++ tailWord_3228951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3228951).length < 2 ^ (prefixWord ++ tailWord_3228951).sum := by decide
  have hdescent : baseEnd_3228951 < baseStart_3228951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3228951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229017 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 3, 4]
def baseStart_3229017 : Nat := 118140960795 + 3229017 * 2 ^ 59
def prefixEnd_3229017 : Nat := 4983230072969 + 3 ^ 40 * 3229017 * 2
def baseEnd_3229017 : Nat := 552679254179699396612509

theorem tailTrace_3229017 : CollatzResearch.WordTrace tailWord_3229017 prefixEnd_3229017 552679254179699396612509 := by
  unfold tailWord_3229017
  simp only [CollatzResearch.WordTrace]
  refine ⟨117771925342830356043765305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78514616895220237362510203 117771925342830356043765305)
  ·
    refine ⟨88328944007122767032823979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117771925342830356043765305 88328944007122767032823979)
    ·
      refine ⟨132493416010684150549235969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88328944007122767032823979 132493416010684150549235969)
      ·
        refine ⟨99370062008013112911926977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132493416010684150549235969 99370062008013112911926977)
        ·
          refine ⟨74527546506009834683945233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99370062008013112911926977 74527546506009834683945233)
          ·
            refine ⟨55895659879507376012958925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74527546506009834683945233 55895659879507376012958925)
            ·
              refine ⟨20960872454815266004859597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55895659879507376012958925 20960872454815266004859597)
              ·
                refine ⟨7860327170555724751822349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20960872454815266004859597 7860327170555724751822349)
                ·
                  refine ⟨2947622688958396781933381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7860327170555724751822349 2947622688958396781933381)
                  ·
                    refine ⟨552679254179699396612509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2947622688958396781933381 552679254179699396612509)
                    ·
                      rfl

theorem cell23_3229017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 4].length) (baseStart_3229017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229017 prefixEnd_3229017 := by exact prefixLift 3229017
  have htrace : WordTrace (prefixWord ++ tailWord_3229017) baseStart_3229017 baseEnd_3229017 := by
    simpa [prefixWord, tailWord_3229017, baseEnd_3229017] using wordTrace_append hprefix tailTrace_3229017
  have hstable : (prefixWord ++ tailWord_3229017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229017).length < 2 ^ (prefixWord ++ tailWord_3229017).sum := by decide
  have hdescent : baseEnd_3229017 < baseStart_3229017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229024 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 2, 4, 2]
def baseStart_3229024 : Nat := 118140960795 + 3229024 * 2 ^ 59
def prefixEnd_3229024 : Nat := 4983230072969 + 3 ^ 40 * 3229024 * 2
def baseEnd_3229024 : Nat := 1658041356903679662449995

theorem tailTrace_3229024 : CollatzResearch.WordTrace tailWord_3229024 prefixEnd_3229024 1658041356903679662449995 := by
  unfold tailWord_3229024
  simp only [CollatzResearch.WordTrace]
  refine ⟨58886090326902498119635063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78514787102536664159513417 58886090326902498119635063)
  ·
    refine ⟨88329135490353747179452595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58886090326902498119635063 88329135490353747179452595)
    ·
      refine ⟨132493703235530620769178893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88329135490353747179452595 132493703235530620769178893)
      ·
        refine ⟨49685138713323982788442085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132493703235530620769178893 49685138713323982788442085)
        ·
          refine ⟨9315963508748246772832891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49685138713323982788442085 9315963508748246772832891)
          ·
            refine ⟨13973945263122370159249337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9315963508748246772832891 13973945263122370159249337)
            ·
              refine ⟨10480458947341777619437003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13973945263122370159249337 10480458947341777619437003)
              ·
                refine ⟨15720688421012666429155505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10480458947341777619437003 15720688421012666429155505)
                ·
                  refine ⟨11790516315759499821866629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15720688421012666429155505 11790516315759499821866629)
                  ·
                    refine ⟨2210721809204906216599993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11790516315759499821866629 2210721809204906216599993)
                    ·
                      refine ⟨1658041356903679662449995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2210721809204906216599993 1658041356903679662449995)
                      ·
                        rfl

theorem cell23_3229024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_3229024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229024 prefixEnd_3229024 := by exact prefixLift 3229024
  have htrace : WordTrace (prefixWord ++ tailWord_3229024) baseStart_3229024 baseEnd_3229024 := by
    simpa [prefixWord, tailWord_3229024, baseEnd_3229024] using wordTrace_append hprefix tailTrace_3229024
  have hstable : (prefixWord ++ tailWord_3229024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229024).length < 2 ^ (prefixWord ++ tailWord_3229024).sum := by decide
  have hdescent : baseEnd_3229024 < baseStart_3229024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229027 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 3]
def baseStart_3229027 : Nat := 118140960795 + 3229027 * 2 ^ 59
def prefixEnd_3229027 : Nat := 4983230072969 + 3 ^ 40 * 3229027 * 2
def baseEnd_3229027 : Nat := 1658042897345643150712481

theorem tailTrace_3229027 : CollatzResearch.WordTrace tailWord_3229027 prefixEnd_3229027 1658042897345643150712481 := by
  unfold tailWord_3229027
  simp only [CollatzResearch.WordTrace]
  refine ⟨117772290072794127751629335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78514860048529418501086223 117772290072794127751629335)
  ·
    refine ⟨176658435109191191627444003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117772290072794127751629335 176658435109191191627444003)
    ·
      refine ⟨264987652663786787441166005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176658435109191191627444003 264987652663786787441166005)
      ·
        refine ⟨24842592437230011322609313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 264987652663786787441166005 24842592437230011322609313)
        ·
          refine ⟨18631944327922508491956985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24842592437230011322609313 18631944327922508491956985)
          ·
            refine ⟨13973958245941881368967739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18631944327922508491956985 13973958245941881368967739)
            ·
              refine ⟨20960937368912822053451609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13973958245941881368967739 20960937368912822053451609)
              ·
                refine ⟨15720703026684616540088707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20960937368912822053451609 15720703026684616540088707)
                ·
                  refine ⟨23581054540026924810133061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15720703026684616540088707 23581054540026924810133061)
                  ·
                    refine ⟨4421447726255048401899949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23581054540026924810133061 4421447726255048401899949)
                    ·
                      refine ⟨1658042897345643150712481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4421447726255048401899949 1658042897345643150712481)
                      ·
                        rfl

theorem cell23_3229027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_3229027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229027 prefixEnd_3229027 := by exact prefixLift 3229027
  have htrace : WordTrace (prefixWord ++ tailWord_3229027) baseStart_3229027 baseEnd_3229027 := by
    simpa [prefixWord, tailWord_3229027, baseEnd_3229027] using wordTrace_append hprefix tailTrace_3229027
  have hstable : (prefixWord ++ tailWord_3229027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229027).length < 2 ^ (prefixWord ++ tailWord_3229027).sum := by decide
  have hdescent : baseEnd_3229027 < baseStart_3229027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229050 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_3229050 : Nat := 118140960795 + 3229050 * 2 ^ 59
def prefixEnd_3229050 : Nat := 4983230072969 + 3 ^ 40 * 3229050 * 2
def baseEnd_3229050 : Nat := 1658054707400696560724875

theorem tailTrace_3229050 : CollatzResearch.WordTrace tailWord_3229050 prefixEnd_3229050 1658054707400696560724875 := by
  unfold tailWord_3229050
  simp only [CollatzResearch.WordTrace]
  refine ⟨29443282237927700669929151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78515419301140535119811069 29443282237927700669929151)
  ·
    refine ⟨44164923356891551004893727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29443282237927700669929151 44164923356891551004893727)
    ·
      refine ⟨66247385035337326507340591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44164923356891551004893727 66247385035337326507340591)
      ·
        refine ⟨99371077553005989761010887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66247385035337326507340591 99371077553005989761010887)
        ·
          refine ⟨149056616329508984641516331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99371077553005989761010887 149056616329508984641516331)
          ·
            refine ⟨223584924494263476962274497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149056616329508984641516331 223584924494263476962274497)
            ·
              refine ⟨167688693370697607721705873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223584924494263476962274497 167688693370697607721705873)
              ·
                refine ⟨125766520028023205791279405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167688693370697607721705873 125766520028023205791279405)
                ·
                  refine ⟨47162445010508702171729777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125766520028023205791279405 47162445010508702171729777)
                  ·
                    refine ⟨35371833757881526628797333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47162445010508702171729777 35371833757881526628797333)
                    ·
                      refine ⟨1658054707400696560724875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35371833757881526628797333 1658054707400696560724875)
                      ·
                        rfl

theorem cell23_3229050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_3229050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229050 prefixEnd_3229050 := by exact prefixLift 3229050
  have htrace : WordTrace (prefixWord ++ tailWord_3229050) baseStart_3229050 baseEnd_3229050 := by
    simpa [prefixWord, tailWord_3229050, baseEnd_3229050] using wordTrace_append hprefix tailTrace_3229050
  have hstable : (prefixWord ++ tailWord_3229050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229050).length < 2 ^ (prefixWord ++ tailWord_3229050).sum := by decide
  have hdescent : baseEnd_3229050 < baseStart_3229050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229107 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 6, 4]
def baseStart_3229107 : Nat := 118140960795 + 3229107 * 2 ^ 59
def prefixEnd_3229107 : Nat := 4983230072969 + 3 ^ 40 * 3229107 * 2
def baseEnd_3229107 : Nat := 552694658599334279237371

theorem tailTrace_3229107 : CollatzResearch.WordTrace tailWord_3229107 prefixEnd_3229107 552694658599334279237371 := by
  unfold tailWord_3229107
  simp only [CollatzResearch.WordTrace]
  refine ⟨117775207912504301414541575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78516805275002867609694383 117775207912504301414541575)
  ·
    refine ⟨176662811868756452121812363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117775207912504301414541575 176662811868756452121812363)
    ·
      refine ⟨264994217803134678182718545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176662811868756452121812363 264994217803134678182718545)
      ·
        refine ⟨198745663352351008637038909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264994217803134678182718545 198745663352351008637038909)
        ·
          refine ⟨74529623757131628238889591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198745663352351008637038909 74529623757131628238889591)
          ·
            refine ⟨111794435635697442358334387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74529623757131628238889591 111794435635697442358334387)
            ·
              refine ⟨167691653453546163537501581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111794435635697442358334387 167691653453546163537501581)
              ·
                refine ⟨62884370045079811326563093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167691653453546163537501581 62884370045079811326563093)
                ·
                  refine ⟨2947704845863116155932645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62884370045079811326563093 2947704845863116155932645)
                  ·
                    refine ⟨552694658599334279237371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2947704845863116155932645 552694658599334279237371)
                    ·
                      rfl

theorem cell23_3229107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 4].length) (baseStart_3229107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229107 prefixEnd_3229107 := by exact prefixLift 3229107
  have htrace : WordTrace (prefixWord ++ tailWord_3229107) baseStart_3229107 baseEnd_3229107 := by
    simpa [prefixWord, tailWord_3229107, baseEnd_3229107] using wordTrace_append hprefix tailTrace_3229107
  have hstable : (prefixWord ++ tailWord_3229107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229107).length < 2 ^ (prefixWord ++ tailWord_3229107).sum := by decide
  have hdescent : baseEnd_3229107 < baseStart_3229107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229127 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_3229127 : Nat := 118140960795 + 3229127 * 2 ^ 59
def prefixEnd_3229127 : Nat := 4983230072969 + 3 ^ 40 * 3229127 * 2
def baseEnd_3229127 : Nat := 1658094245411092759462021

theorem tailTrace_3229127 : CollatzResearch.WordTrace tailWord_3229127 prefixEnd_3229127 1658094245411092759462021 := by
  unfold tailWord_3229127
  simp only [CollatzResearch.WordTrace]
  refine ⟨117775937372431844830269635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78517291581621229886846423 117775937372431844830269635)
  ·
    refine ⟨176663906058647767245404453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117775937372431844830269635 176663906058647767245404453)
    ·
      refine ⟨33124482385996456358513335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176663906058647767245404453 33124482385996456358513335)
      ·
        refine ⟨49686723578994684537770003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33124482385996456358513335 49686723578994684537770003)
        ·
          refine ⟨74530085368492026806655005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49686723578994684537770003 74530085368492026806655005)
          ·
            refine ⟨27948782013184510052495627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74530085368492026806655005 27948782013184510052495627)
            ·
              refine ⟨41923173019776765078743441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27948782013184510052495627 41923173019776765078743441)
              ·
                refine ⟨31442379764832573809057581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41923173019776765078743441 31442379764832573809057581)
                ·
                  refine ⟨11790892411812215178396593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31442379764832573809057581 11790892411812215178396593)
                  ·
                    refine ⟨8843169308859161383797445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11790892411812215178396593 8843169308859161383797445)
                    ·
                      refine ⟨1658094245411092759462021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8843169308859161383797445 1658094245411092759462021)
                      ·
                        rfl

theorem cell23_3229127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_3229127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229127 prefixEnd_3229127 := by exact prefixLift 3229127
  have htrace : WordTrace (prefixWord ++ tailWord_3229127) baseStart_3229127 baseEnd_3229127 := by
    simpa [prefixWord, tailWord_3229127, baseEnd_3229127] using wordTrace_append hprefix tailTrace_3229127
  have hstable : (prefixWord ++ tailWord_3229127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229127).length < 2 ^ (prefixWord ++ tailWord_3229127).sum := by decide
  have hdescent : baseEnd_3229127 < baseStart_3229127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229134 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_3229134 : Nat := 118140960795 + 3229134 * 2 ^ 59
def prefixEnd_3229134 : Nat := 4983230072969 + 3 ^ 40 * 3229134 * 2
def baseEnd_3229134 : Nat := 1658097839775674232074489

theorem tailTrace_3229134 : CollatzResearch.WordTrace tailWord_3229134 prefixEnd_3229134 1658097839775674232074489 := by
  unfold tailWord_3229134
  simp only [CollatzResearch.WordTrace]
  refine ⟨14722024085425810628221807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78517461788937656683849637 14722024085425810628221807)
  ·
    refine ⟨22083036128138715942332711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14722024085425810628221807 22083036128138715942332711)
    ·
      refine ⟨33124554192208073913499067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22083036128138715942332711 33124554192208073913499067)
      ·
        refine ⟨49686831288312110870248601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33124554192208073913499067 49686831288312110870248601)
        ·
          refine ⟨37265123466234083152686451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49686831288312110870248601 37265123466234083152686451)
          ·
            refine ⟨55897685199351124729029677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37265123466234083152686451 55897685199351124729029677)
            ·
              refine ⟨20961631949756671773386129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55897685199351124729029677 20961631949756671773386129)
              ·
                refine ⟨15721223962317503830039597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20961631949756671773386129 15721223962317503830039597)
                ·
                  refine ⟨5895458985869063936264849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15721223962317503830039597 5895458985869063936264849)
                  ·
                    refine ⟨4421594239401797952198637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5895458985869063936264849 4421594239401797952198637)
                    ·
                      refine ⟨1658097839775674232074489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4421594239401797952198637 1658097839775674232074489)
                      ·
                        rfl

theorem cell23_3229134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_3229134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229134 prefixEnd_3229134 := by exact prefixLift 3229134
  have htrace : WordTrace (prefixWord ++ tailWord_3229134) baseStart_3229134 baseEnd_3229134 := by
    simpa [prefixWord, tailWord_3229134, baseEnd_3229134] using wordTrace_append hprefix tailTrace_3229134
  have hstable : (prefixWord ++ tailWord_3229134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229134).length < 2 ^ (prefixWord ++ tailWord_3229134).sum := by decide
  have hdescent : baseEnd_3229134 < baseStart_3229134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229165 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3229165 : Nat := 118140960795 + 3229165 * 2 ^ 59
def prefixEnd_3229165 : Nat := 4983230072969 + 3 ^ 40 * 3229165 * 2
def baseEnd_3229165 : Nat := 1658113757675963610786847

theorem tailTrace_3229165 : CollatzResearch.WordTrace tailWord_3229165 prefixEnd_3229165 1658113757675963610786847 := by
  unfold tailWord_3229165
  simp only [CollatzResearch.WordTrace]
  refine ⟨117777323346294177320152949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78518215564196118213435299 117777323346294177320152949)
  ·
    refine ⟨11041624063715079123764339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117777323346294177320152949 11041624063715079123764339)
    ·
      refine ⟨16562436095572618685646509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11041624063715079123764339 16562436095572618685646509)
      ·
        refine ⟨6210913535839732007117441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16562436095572618685646509 6210913535839732007117441)
        ·
          refine ⟨4658185151879799005338081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6210913535839732007117441 4658185151879799005338081)
          ·
            refine ⟨3493638863909849254003561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4658185151879799005338081 3493638863909849254003561)
            ·
              refine ⟨2620229147932386940502671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3493638863909849254003561 2620229147932386940502671)
              ·
                refine ⟨3930343721898580410754007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620229147932386940502671 3930343721898580410754007)
                ·
                  refine ⟨5895515582847870616131011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930343721898580410754007 5895515582847870616131011)
                  ·
                    refine ⟨8843273374271805924196517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5895515582847870616131011 8843273374271805924196517)
                    ·
                      refine ⟨1658113757675963610786847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8843273374271805924196517 1658113757675963610786847)
                      ·
                        rfl

theorem cell23_3229165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3229165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229165 prefixEnd_3229165 := by exact prefixLift 3229165
  have htrace : WordTrace (prefixWord ++ tailWord_3229165) baseStart_3229165 baseEnd_3229165 := by
    simpa [prefixWord, tailWord_3229165, baseEnd_3229165] using wordTrace_append hprefix tailTrace_3229165
  have hstable : (prefixWord ++ tailWord_3229165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229165).length < 2 ^ (prefixWord ++ tailWord_3229165).sum := by decide
  have hdescent : baseEnd_3229165 < baseStart_3229165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229168 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 1, 2, 3]
def baseStart_3229168 : Nat := 118140960795 + 3229168 * 2 ^ 59
def prefixEnd_3229168 : Nat := 4983230072969 + 3 ^ 40 * 3229168 * 2
def baseEnd_3229168 : Nat := 1658115298117927099049333

theorem tailTrace_3229168 : CollatzResearch.WordTrace tailWord_3229168 prefixEnd_3229168 1658115298117927099049333 := by
  unfold tailWord_3229168
  simp only [CollatzResearch.WordTrace]
  refine ⟨58888716382641654416256079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78518288510188872555008105 58888716382641654416256079)
  ·
    refine ⟨88333074573962481624384119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58888716382641654416256079 88333074573962481624384119)
    ·
      refine ⟨132499611860943722436576179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88333074573962481624384119 132499611860943722436576179)
      ·
        refine ⟨198749417791415583654864269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132499611860943722436576179 198749417791415583654864269)
        ·
          refine ⟨74531031671780843870574101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198749417791415583654864269 74531031671780843870574101)
          ·
            refine ⟨3493642109614727056433161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74531031671780843870574101 3493642109614727056433161)
            ·
              refine ⟨2620231582211045292324871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3493642109614727056433161 2620231582211045292324871)
              ·
                refine ⟨3930347373316567938487307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620231582211045292324871 3930347373316567938487307)
                ·
                  refine ⟨5895521059974851907730961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930347373316567938487307 5895521059974851907730961)
                  ·
                    refine ⟨4421640794981138930798221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5895521059974851907730961 4421640794981138930798221)
                    ·
                      refine ⟨1658115298117927099049333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4421640794981138930798221 1658115298117927099049333)
                      ·
                        rfl

theorem cell23_3229168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 2, 3].length) (baseStart_3229168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229168 prefixEnd_3229168 := by exact prefixLift 3229168
  have htrace : WordTrace (prefixWord ++ tailWord_3229168) baseStart_3229168 baseEnd_3229168 := by
    simpa [prefixWord, tailWord_3229168, baseEnd_3229168] using wordTrace_append hprefix tailTrace_3229168
  have hstable : (prefixWord ++ tailWord_3229168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229168).length < 2 ^ (prefixWord ++ tailWord_3229168).sum := by decide
  have hdescent : baseEnd_3229168 < baseStart_3229168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229181 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_3229181 : Nat := 118140960795 + 3229181 * 2 ^ 59
def prefixEnd_3229181 : Nat := 4983230072969 + 3 ^ 40 * 3229181 * 2
def baseEnd_3229181 : Nat := 1658121973366435548186773

theorem tailTrace_3229181 : CollatzResearch.WordTrace tailWord_3229181 prefixEnd_3229181 1658121973366435548186773 := by
  unfold tailWord_3229181
  simp only [CollatzResearch.WordTrace]
  refine ⟨117777906914236212052735397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78518604609490808035156931 117777906914236212052735397)
  ·
    refine ⟨22083357546419289759887887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117777906914236212052735397 22083357546419289759887887)
    ·
      refine ⟨33125036319628934639831831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22083357546419289759887887 33125036319628934639831831)
      ·
        refine ⟨49687554479443401959747747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33125036319628934639831831 49687554479443401959747747)
        ·
          refine ⟨74531331719165102939621621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49687554479443401959747747 74531331719165102939621621)
          ·
            refine ⟨6987312348671728400589527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74531331719165102939621621 6987312348671728400589527)
            ·
              refine ⟨10480968523007592600884291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6987312348671728400589527 10480968523007592600884291)
              ·
                refine ⟨15721452784511388901326437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10480968523007592600884291 15721452784511388901326437)
                ·
                  refine ⟨2947772397095885418998707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15721452784511388901326437 2947772397095885418998707)
                  ·
                    refine ⟨4421658595643828128498061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2947772397095885418998707 4421658595643828128498061)
                    ·
                      refine ⟨1658121973366435548186773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4421658595643828128498061 1658121973366435548186773)
                      ·
                        rfl

theorem cell23_3229181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_3229181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229181 prefixEnd_3229181 := by exact prefixLift 3229181
  have htrace : WordTrace (prefixWord ++ tailWord_3229181) baseStart_3229181 baseEnd_3229181 := by
    simpa [prefixWord, tailWord_3229181, baseEnd_3229181] using wordTrace_append hprefix tailTrace_3229181
  have hstable : (prefixWord ++ tailWord_3229181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229181).length < 2 ^ (prefixWord ++ tailWord_3229181).sum := by decide
  have hdescent : baseEnd_3229181 < baseStart_3229181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229182 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_3229182 : Nat := 118140960795 + 3229182 * 2 ^ 59
def prefixEnd_3229182 : Nat := 4983230072969 + 3 ^ 40 * 3229182 * 2
def baseEnd_3229182 : Nat := 1658122486847090044274269

theorem tailTrace_3229182 : CollatzResearch.WordTrace tailWord_3229182 prefixEnd_3229182 1658122486847090044274269 := by
  unfold tailWord_3229182
  simp only [CollatzResearch.WordTrace]
  refine ⟨14722242923404073652940225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78518628924821726149014533 14722242923404073652940225)
  ·
    refine ⟨11041682192553055239705169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14722242923404073652940225 11041682192553055239705169)
    ·
      refine ⟨8281261644414791429778877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11041682192553055239705169 8281261644414791429778877)
      ·
        refine ⟨3105473116655546786167079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8281261644414791429778877 3105473116655546786167079)
        ·
          refine ⟨4658209674983320179250619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105473116655546786167079 4658209674983320179250619)
          ·
            refine ⟨6987314512474980268875929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658209674983320179250619 6987314512474980268875929)
            ·
              refine ⟨5240485884356235201656947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6987314512474980268875929 5240485884356235201656947)
              ·
                refine ⟨7860728826534352802485421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5240485884356235201656947 7860728826534352802485421)
                ·
                  refine ⟨2947773309950382300932033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7860728826534352802485421 2947773309950382300932033)
                  ·
                    refine ⟨2210829982462786725699025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2947773309950382300932033 2210829982462786725699025)
                    ·
                      refine ⟨1658122486847090044274269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2210829982462786725699025 1658122486847090044274269)
                      ·
                        rfl

theorem cell23_3229182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_3229182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229182 prefixEnd_3229182 := by exact prefixLift 3229182
  have htrace : WordTrace (prefixWord ++ tailWord_3229182) baseStart_3229182 baseEnd_3229182 := by
    simpa [prefixWord, tailWord_3229182, baseEnd_3229182] using wordTrace_append hprefix tailTrace_3229182
  have hstable : (prefixWord ++ tailWord_3229182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229182).length < 2 ^ (prefixWord ++ tailWord_3229182).sum := by decide
  have hdescent : baseEnd_3229182 < baseStart_3229182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229187 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 4]
def baseStart_3229187 : Nat := 118140960795 + 3229187 * 2 ^ 59
def prefixEnd_3229187 : Nat := 4983230072969 + 3 ^ 40 * 3229187 * 2
def baseEnd_3229187 : Nat := 1658125054250362524711745

theorem tailTrace_3229187 : CollatzResearch.WordTrace tailWord_3229187 prefixEnd_3229187 1658125054250362524711745 := by
  unfold tailWord_3229187
  simp only [CollatzResearch.WordTrace]
  refine ⟨117778125752214475077453815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78518750501476316718302543 117778125752214475077453815)
  ·
    refine ⟨176667188628321712616180723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117778125752214475077453815 176667188628321712616180723)
    ·
      refine ⟨265000782942482568924271085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176667188628321712616180723 265000782942482568924271085)
      ·
        refine ⟨99375293603430963346601657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265000782942482568924271085 99375293603430963346601657)
        ·
          refine ⟨74531470202573222509951243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99375293603430963346601657 74531470202573222509951243)
          ·
            refine ⟨111797205303859833764926865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74531470202573222509951243 111797205303859833764926865)
            ·
              refine ⟨83847903977894875323695149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111797205303859833764926865 83847903977894875323695149)
              ·
                refine ⟨31442963991710578246385681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83847903977894875323695149 31442963991710578246385681)
                ·
                  refine ⟨23582222993782933684789261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31442963991710578246385681 23582222993782933684789261)
                  ·
                    refine ⟨8843333622668600131795973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23582222993782933684789261 8843333622668600131795973)
                    ·
                      refine ⟨1658125054250362524711745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8843333622668600131795973 1658125054250362524711745)
                      ·
                        rfl

theorem cell23_3229187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_3229187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229187 prefixEnd_3229187 := by exact prefixLift 3229187
  have htrace : WordTrace (prefixWord ++ tailWord_3229187) baseStart_3229187 baseEnd_3229187 := by
    simpa [prefixWord, tailWord_3229187, baseEnd_3229187] using wordTrace_append hprefix tailTrace_3229187
  have hstable : (prefixWord ++ tailWord_3229187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229187).length < 2 ^ (prefixWord ++ tailWord_3229187).sum := by decide
  have hdescent : baseEnd_3229187 < baseStart_3229187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229198 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_3229198 : Nat := 118140960795 + 3229198 * 2 ^ 59
def prefixEnd_3229198 : Nat := 4983230072969 + 3 ^ 40 * 3229198 * 2
def baseEnd_3229198 : Nat := 1658130702537561981674195

theorem tailTrace_3229198 : CollatzResearch.WordTrace tailWord_3229198 prefixEnd_3229198 1658130702537561981674195 := by
  unfold tailWord_3229198
  simp only [CollatzResearch.WordTrace]
  refine ⟨14722315869396827994513031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78519017970116415970736165 14722315869396827994513031)
  ·
    refine ⟨22083473804095241991769547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14722315869396827994513031 22083473804095241991769547)
    ·
      refine ⟨33125210706142862987654321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22083473804095241991769547 33125210706142862987654321)
      ·
        refine ⟨24843908029607147240740741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33125210706142862987654321 24843908029607147240740741)
        ·
          refine ⟨4658232755551340107638889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24843908029607147240740741 4658232755551340107638889)
          ·
            refine ⟨3493674566663505080729167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4658232755551340107638889 3493674566663505080729167)
            ·
              refine ⟨5240511849995257621093751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493674566663505080729167 5240511849995257621093751)
              ·
                refine ⟨7860767774992886431640627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5240511849995257621093751 7860767774992886431640627)
                ·
                  refine ⟨11791151662489329647460941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7860767774992886431640627 11791151662489329647460941)
                  ·
                    refine ⟨4421681873433498617797853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11791151662489329647460941 4421681873433498617797853)
                    ·
                      refine ⟨1658130702537561981674195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4421681873433498617797853 1658130702537561981674195)
                      ·
                        rfl

theorem cell23_3229198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_3229198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229198 prefixEnd_3229198 := by exact prefixLift 3229198
  have htrace : WordTrace (prefixWord ++ tailWord_3229198) baseStart_3229198 baseEnd_3229198 := by
    simpa [prefixWord, tailWord_3229198, baseEnd_3229198] using wordTrace_append hprefix tailTrace_3229198
  have hstable : (prefixWord ++ tailWord_3229198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229198).length < 2 ^ (prefixWord ++ tailWord_3229198).sum := by decide
  have hdescent : baseEnd_3229198 < baseStart_3229198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229255 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 2, 2, 2]
def baseStart_3229255 : Nat := 118140960795 + 3229255 * 2 ^ 59
def prefixEnd_3229255 : Nat := 4983230072969 + 3 ^ 40 * 3229255 * 2
def baseEnd_3229255 : Nat := 1658159970934868258661433

theorem tailTrace_3229255 : CollatzResearch.WordTrace tailWord_3229255 prefixEnd_3229255 1658159970934868258661433 := by
  unfold tailWord_3229255
  simp only [CollatzResearch.WordTrace]
  refine ⟨117780605915968122690929219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78520403943978748460619479 117780605915968122690929219)
  ·
    refine ⟨176670908873952184036393829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117780605915968122690929219 176670908873952184036393829)
    ·
      refine ⟨33125795413866034506823843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176670908873952184036393829 33125795413866034506823843)
      ·
        refine ⟨49688693120799051760235765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33125795413866034506823843 49688693120799051760235765)
        ·
          refine ⟨4658314980074911102522103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49688693120799051760235765 4658314980074911102522103)
          ·
            refine ⟨6987472470112366653783155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658314980074911102522103 6987472470112366653783155)
            ·
              refine ⟨10481208705168549980674733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6987472470112366653783155 10481208705168549980674733)
              ·
                refine ⟨3930453264438206242753025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10481208705168549980674733 3930453264438206242753025)
                ·
                  refine ⟨2947839948328654682064769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3930453264438206242753025 2947839948328654682064769)
                  ·
                    refine ⟨2210879961246491011548577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2947839948328654682064769 2210879961246491011548577)
                    ·
                      refine ⟨1658159970934868258661433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2210879961246491011548577 1658159970934868258661433)
                      ·
                        rfl

theorem cell23_3229255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_3229255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229255 prefixEnd_3229255 := by exact prefixLift 3229255
  have htrace : WordTrace (prefixWord ++ tailWord_3229255) baseStart_3229255 baseEnd_3229255 := by
    simpa [prefixWord, tailWord_3229255, baseEnd_3229255] using wordTrace_append hprefix tailTrace_3229255
  have hstable : (prefixWord ++ tailWord_3229255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229255).length < 2 ^ (prefixWord ++ tailWord_3229255).sum := by decide
  have hdescent : baseEnd_3229255 < baseStart_3229255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229257 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 3, 7]
def baseStart_3229257 : Nat := 118140960795 + 3229257 * 2 ^ 59
def prefixEnd_3229257 : Nat := 4983230072969 + 3 ^ 40 * 3229257 * 2
def baseEnd_3229257 : Nat := 552720332632059083612141

theorem tailTrace_3229257 : CollatzResearch.WordTrace tailWord_3229257 prefixEnd_3229257 552720332632059083612141 := by
  unfold tailWord_3229257
  simp only [CollatzResearch.WordTrace]
  refine ⟨117780678861960877032502025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78520452574640584688334683 117780678861960877032502025)
  ·
    refine ⟨88335509146470657774376519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117780678861960877032502025 88335509146470657774376519)
    ·
      refine ⟨132503263719705986661564779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88335509146470657774376519 132503263719705986661564779)
      ·
        refine ⟨198754895579558979992347169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132503263719705986661564779 198754895579558979992347169)
        ·
          refine ⟨149066171684669234994260377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198754895579558979992347169 149066171684669234994260377)
          ·
            refine ⟨111799628763501926245695283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149066171684669234994260377 111799628763501926245695283)
            ·
              refine ⟨167699443145252889368542925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111799628763501926245695283 167699443145252889368542925)
              ·
                refine ⟨62887291179469833513203597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167699443145252889368542925 62887291179469833513203597)
                ·
                  refine ⟨23582734192301187567451349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62887291179469833513203597 23582734192301187567451349)
                  ·
                    refine ⟨552720332632059083612141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23582734192301187567451349 552720332632059083612141)
                    ·
                      rfl

theorem cell23_3229257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_3229257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229257 prefixEnd_3229257 := by exact prefixLift 3229257
  have htrace : WordTrace (prefixWord ++ tailWord_3229257) baseStart_3229257 baseEnd_3229257 := by
    simpa [prefixWord, tailWord_3229257, baseEnd_3229257] using wordTrace_append hprefix tailTrace_3229257
  have hstable : (prefixWord ++ tailWord_3229257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229257).length < 2 ^ (prefixWord ++ tailWord_3229257).sum := by decide
  have hdescent : baseEnd_3229257 < baseStart_3229257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229267 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 5]
def baseStart_3229267 : Nat := 118140960795 + 3229267 * 2 ^ 59
def prefixEnd_3229267 : Nat := 4983230072969 + 3 ^ 40 * 3229267 * 2
def baseEnd_3229267 : Nat := 1658166132702722211711377

theorem tailTrace_3229267 : CollatzResearch.WordTrace tailWord_3229267 prefixEnd_3229267 1658166132702722211711377 := by
  unfold tailWord_3229267
  simp only [CollatzResearch.WordTrace]
  refine ⟨117781043591924648740366055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78520695727949765826910703 117781043591924648740366055)
  ·
    refine ⟨176671565387886973110549083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117781043591924648740366055 176671565387886973110549083)
    ·
      refine ⟨265007348081830459665823625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176671565387886973110549083 265007348081830459665823625)
      ·
        refine ⟨198755511061372844749367719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265007348081830459665823625 198755511061372844749367719)
        ·
          refine ⟨298133266592059267124051579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198755511061372844749367719 298133266592059267124051579)
          ·
            refine ⟨447199899888088900686077369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298133266592059267124051579 447199899888088900686077369)
            ·
              refine ⟨335399924916066675514558027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447199899888088900686077369 335399924916066675514558027)
              ·
                refine ⟨503099887374100013271837041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335399924916066675514558027 503099887374100013271837041)
                ·
                  refine ⟨377324915530575009953877781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503099887374100013271837041 377324915530575009953877781)
                  ·
                    refine ⟨17687105415495703591588021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 377324915530575009953877781 17687105415495703591588021)
                    ·
                      refine ⟨1658166132702722211711377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17687105415495703591588021 1658166132702722211711377)
                      ·
                        rfl

theorem cell23_3229267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_3229267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229267 prefixEnd_3229267 := by exact prefixLift 3229267
  have htrace : WordTrace (prefixWord ++ tailWord_3229267) baseStart_3229267 baseEnd_3229267 := by
    simpa [prefixWord, tailWord_3229267, baseEnd_3229267] using wordTrace_append hprefix tailTrace_3229267
  have hstable : (prefixWord ++ tailWord_3229267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229267).length < 2 ^ (prefixWord ++ tailWord_3229267).sum := by decide
  have hdescent : baseEnd_3229267 < baseStart_3229267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229284 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_3229284 : Nat := 118140960795 + 3229284 * 2 ^ 59
def prefixEnd_3229284 : Nat := 4983230072969 + 3 ^ 40 * 3229284 * 2
def baseEnd_3229284 : Nat := 1658174861873848645198799

theorem tailTrace_3229284 : CollatzResearch.WordTrace tailWord_3229284 prefixEnd_3229284 1658174861873848645198799 := by
  unfold tailWord_3229284
  simp only [CollatzResearch.WordTrace]
  refine ⟨58890831816431530321867453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78521109088575373762489937 58890831816431530321867453)
  ·
    refine ⟨22084061931161823870700295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58890831816431530321867453 22084061931161823870700295)
    ·
      refine ⟨33126092896742735806050443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22084061931161823870700295 33126092896742735806050443)
      ·
        refine ⟨49689139345114103709075665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33126092896742735806050443 49689139345114103709075665)
        ·
          refine ⟨37266854508835577781806749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49689139345114103709075665 37266854508835577781806749)
          ·
            refine ⟨13975070440813341668177531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37266854508835577781806749 13975070440813341668177531)
            ·
              refine ⟨20962605661220012502266297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13975070440813341668177531 20962605661220012502266297)
              ·
                refine ⟨15721954245915009376699723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20962605661220012502266297 15721954245915009376699723)
                ·
                  refine ⟨23582931368872514065049585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15721954245915009376699723 23582931368872514065049585)
                  ·
                    refine ⟨17687198526654385548787189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23582931368872514065049585 17687198526654385548787189)
                    ·
                      refine ⟨1658174861873848645198799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17687198526654385548787189 1658174861873848645198799)
                      ·
                        rfl

theorem cell23_3229284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_3229284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229284 prefixEnd_3229284 := by exact prefixLift 3229284
  have htrace : WordTrace (prefixWord ++ tailWord_3229284) baseStart_3229284 baseEnd_3229284 := by
    simpa [prefixWord, tailWord_3229284, baseEnd_3229284] using wordTrace_append hprefix tailTrace_3229284
  have hstable : (prefixWord ++ tailWord_3229284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229284).length < 2 ^ (prefixWord ++ tailWord_3229284).sum := by decide
  have hdescent : baseEnd_3229284 < baseStart_3229284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229301 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3229301 : Nat := 118140960795 + 3229301 * 2 ^ 59
def prefixEnd_3229301 : Nat := 4983230072969 + 3 ^ 40 * 3229301 * 2
def baseEnd_3229301 : Nat := 1658183591044975078686221

theorem tailTrace_3229301 : CollatzResearch.WordTrace tailWord_3229301 prefixEnd_3229301 1658183591044975078686221 := by
  unfold tailWord_3229301
  simp only [CollatzResearch.WordTrace]
  refine ⟨117782283673801472547103757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78521522449200981698069171 117782283673801472547103757)
  ·
    refine ⟨44168356377675552205163909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117782283673801472547103757 44168356377675552205163909)
    ·
      refine ⟨8281566820814166038468233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44168356377675552205163909 8281566820814166038468233)
      ·
        refine ⟨6211175115610624528851175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8281566820814166038468233 6211175115610624528851175)
        ·
          refine ⟨9316762673415936793276763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6211175115610624528851175 9316762673415936793276763)
          ·
            refine ⟨13975144010123905189915145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9316762673415936793276763 13975144010123905189915145)
            ·
              refine ⟨10481358007592928892436359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13975144010123905189915145 10481358007592928892436359)
              ·
                refine ⟨15722037011389393338654539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10481358007592928892436359 15722037011389393338654539)
                ·
                  refine ⟨23583055517084090007981809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15722037011389393338654539 23583055517084090007981809)
                  ·
                    refine ⟨17687291637813067505986357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23583055517084090007981809 17687291637813067505986357)
                    ·
                      refine ⟨1658183591044975078686221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17687291637813067505986357 1658183591044975078686221)
                      ·
                        rfl

theorem cell23_3229301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3229301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229301 prefixEnd_3229301 := by exact prefixLift 3229301
  have htrace : WordTrace (prefixWord ++ tailWord_3229301) baseStart_3229301 baseEnd_3229301 := by
    simpa [prefixWord, tailWord_3229301, baseEnd_3229301] using wordTrace_append hprefix tailTrace_3229301
  have hstable : (prefixWord ++ tailWord_3229301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229301).length < 2 ^ (prefixWord ++ tailWord_3229301).sum := by decide
  have hdescent : baseEnd_3229301 < baseStart_3229301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229389 : List Nat := [1, 6, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3229389 : Nat := 118140960795 + 3229389 * 2 ^ 59
def prefixEnd_3229389 : Nat := 4983230072969 + 3 ^ 40 * 3229389 * 2
def baseEnd_3229389 : Nat := 552742925780856911461939

theorem tailTrace_3229389 : CollatzResearch.WordTrace tailWord_3229389 prefixEnd_3229389 552742925780856911461939 := by
  unfold tailWord_3229389
  simp only [CollatzResearch.WordTrace]
  refine ⟨117785493297482663576307221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78523662198321775717538147 117785493297482663576307221)
  ·
    refine ⟨5521194998319499855139401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117785493297482663576307221 5521194998319499855139401)
    ·
      refine ⟨4140896248739624891354551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5521194998319499855139401 4140896248739624891354551)
      ·
        refine ⟨6211344373109437337031827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140896248739624891354551 6211344373109437337031827)
        ·
          refine ⟨9317016559664156005547741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6211344373109437337031827 9317016559664156005547741)
          ·
            refine ⟨3493881209874058502080403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9317016559664156005547741 3493881209874058502080403)
            ·
              refine ⟨5240821814811087753120605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493881209874058502080403 5240821814811087753120605)
              ·
                refine ⟨1965308180554157907420227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5240821814811087753120605 1965308180554157907420227)
                ·
                  refine ⟨2947962270831236861130341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1965308180554157907420227 2947962270831236861130341)
                  ·
                    refine ⟨552742925780856911461939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2947962270831236861130341 552742925780856911461939)
                    ·
                      rfl

theorem cell23_3229389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3229389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229389 prefixEnd_3229389 := by exact prefixLift 3229389
  have htrace : WordTrace (prefixWord ++ tailWord_3229389) baseStart_3229389 baseEnd_3229389 := by
    simpa [prefixWord, tailWord_3229389, baseEnd_3229389] using wordTrace_append hprefix tailTrace_3229389
  have hstable : (prefixWord ++ tailWord_3229389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229389).length < 2 ^ (prefixWord ++ tailWord_3229389).sum := by decide
  have hdescent : baseEnd_3229389 < baseStart_3229389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229412 : List Nat := [2, 3, 1, 1, 1, 3, 5, 2, 1, 1, 3]
def baseStart_3229412 : Nat := 118140960795 + 3229412 * 2 ^ 59
def prefixEnd_3229412 : Nat := 4983230072969 + 3 ^ 40 * 3229412 * 2
def baseEnd_3229412 : Nat := 1658240587397624144398211

theorem tailTrace_3229412 : CollatzResearch.WordTrace tailWord_3229412 prefixEnd_3229412 1658240587397624144398211 := by
  unfold tailWord_3229412
  simp only [CollatzResearch.WordTrace]
  refine ⟨58893166088199669252197245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78524221450932892336262993 58893166088199669252197245)
  ·
    refine ⟨22084937283074875969573967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58893166088199669252197245 22084937283074875969573967)
    ·
      refine ⟨33127405924612313954360951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22084937283074875969573967 33127405924612313954360951)
      ·
        refine ⟨49691108886918470931541427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33127405924612313954360951 49691108886918470931541427)
        ·
          refine ⟨74536663330377706397312141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49691108886918470931541427 74536663330377706397312141)
          ·
            refine ⟨27951248748891639898992053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74536663330377706397312141 27951248748891639898992053)
            ·
              refine ⟨2620429570208591240530505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27951248748891639898992053 2620429570208591240530505)
              ·
                refine ⟨1965322177656443430397879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2620429570208591240530505 1965322177656443430397879)
                ·
                  refine ⟨2947983266484665145596819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1965322177656443430397879 2947983266484665145596819)
                  ·
                    refine ⟨4421974899726997718395229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2947983266484665145596819 4421974899726997718395229)
                    ·
                      refine ⟨1658240587397624144398211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4421974899726997718395229 1658240587397624144398211)
                      ·
                        rfl

theorem cell23_3229412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_3229412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229412 prefixEnd_3229412 := by exact prefixLift 3229412
  have htrace : WordTrace (prefixWord ++ tailWord_3229412) baseStart_3229412 baseEnd_3229412 := by
    simpa [prefixWord, tailWord_3229412, baseEnd_3229412] using wordTrace_append hprefix tailTrace_3229412
  have hstable : (prefixWord ++ tailWord_3229412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229412).length < 2 ^ (prefixWord ++ tailWord_3229412).sum := by decide
  have hdescent : baseEnd_3229412 < baseStart_3229412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229451 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 3]
def baseStart_3229451 : Nat := 118140960795 + 3229451 * 2 ^ 59
def prefixEnd_3229451 : Nat := 4983230072969 + 3 ^ 40 * 3229451 * 2
def baseEnd_3229451 : Nat := 1658260613143149491810531

theorem tailTrace_3229451 : CollatzResearch.WordTrace tailWord_3229451 prefixEnd_3229451 1658260613143149491810531 := by
  unfold tailWord_3229451
  simp only [CollatzResearch.WordTrace]
  refine ⟨117787754623258048165064207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78525169748838698776709471 117787754623258048165064207)
  ·
    refine ⟨176681631934887072247596311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117787754623258048165064207 176681631934887072247596311)
    ·
      refine ⟨265022447902330608371394467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176681631934887072247596311 265022447902330608371394467)
      ·
        refine ⟨397533671853495912557091701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265022447902330608371394467 397533671853495912557091701)
        ·
          refine ⟨37268781736265241802227347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 397533671853495912557091701 37268781736265241802227347)
          ·
            refine ⟨55903172604397862703341021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37268781736265241802227347 55903172604397862703341021)
            ·
              refine ⟨20963689726649198513752883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55903172604397862703341021 20963689726649198513752883)
              ·
                refine ⟨31445534589973797770629325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20963689726649198513752883 31445534589973797770629325)
                ·
                  refine ⟨11792075471240174163985997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31445534589973797770629325 11792075471240174163985997)
                  ·
                    refine ⟨4422028301715065311494749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11792075471240174163985997 4422028301715065311494749)
                    ·
                      refine ⟨1658260613143149491810531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4422028301715065311494749 1658260613143149491810531)
                      ·
                        rfl

theorem cell23_3229451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 3].length) (baseStart_3229451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229451 prefixEnd_3229451 := by exact prefixLift 3229451
  have htrace : WordTrace (prefixWord ++ tailWord_3229451) baseStart_3229451 baseEnd_3229451 := by
    simpa [prefixWord, tailWord_3229451, baseEnd_3229451] using wordTrace_append hprefix tailTrace_3229451
  have hstable : (prefixWord ++ tailWord_3229451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229451).length < 2 ^ (prefixWord ++ tailWord_3229451).sum := by decide
  have hdescent : baseEnd_3229451 < baseStart_3229451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229511 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_3229511 : Nat := 118140960795 + 3229511 * 2 ^ 59
def prefixEnd_3229511 : Nat := 4983230072969 + 3 ^ 40 * 3229511 * 2
def baseEnd_3229511 : Nat := 1658291421982419257060255

theorem tailTrace_3229511 : CollatzResearch.WordTrace tailWord_3229511 prefixEnd_3229511 1658291421982419257060255 := by
  unfold tailWord_3229511
  simp only [CollatzResearch.WordTrace]
  refine ⟨117789943003040678412248387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78526628668693785608165591 117789943003040678412248387)
  ·
    refine ⟨176684914504561017618372581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117789943003040678412248387 176684914504561017618372581)
    ·
      refine ⟨33128421469605190803444859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176684914504561017618372581 33128421469605190803444859)
      ·
        refine ⟨49692632204407786205167289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33128421469605190803444859 49692632204407786205167289)
        ·
          refine ⟨37269474153305839653875467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49692632204407786205167289 37269474153305839653875467)
          ·
            refine ⟨55904211229958759480813201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37269474153305839653875467 55904211229958759480813201)
            ·
              refine ⟨41928158422469069610609901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55904211229958759480813201 41928158422469069610609901)
              ·
                refine ⟨15723059408425901103978713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41928158422469069610609901 15723059408425901103978713)
                ·
                  refine ⟨11792294556319425827984035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15723059408425901103978713 11792294556319425827984035)
                  ·
                    refine ⟨17688441834479138741976053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11792294556319425827984035 17688441834479138741976053)
                    ·
                      refine ⟨1658291421982419257060255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17688441834479138741976053 1658291421982419257060255)
                      ·
                        rfl

theorem cell23_3229511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_3229511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229511 prefixEnd_3229511 := by exact prefixLift 3229511
  have htrace : WordTrace (prefixWord ++ tailWord_3229511) baseStart_3229511 baseEnd_3229511 := by
    simpa [prefixWord, tailWord_3229511, baseEnd_3229511] using wordTrace_append hprefix tailTrace_3229511
  have hstable : (prefixWord ++ tailWord_3229511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229511).length < 2 ^ (prefixWord ++ tailWord_3229511).sum := by decide
  have hdescent : baseEnd_3229511 < baseStart_3229511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229512 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 1, 3, 2]
def baseStart_3229512 : Nat := 118140960795 + 3229512 * 2 ^ 59
def prefixEnd_3229512 : Nat := 4983230072969 + 3 ^ 40 * 3229512 * 2
def baseEnd_3229512 : Nat := 1658291935463073753147751

theorem tailTrace_3229512 : CollatzResearch.WordTrace tailWord_3229512 prefixEnd_3229512 1658291935463073753147751 := by
  unfold tailWord_3229512
  simp only [CollatzResearch.WordTrace]
  refine ⟨58894989738018527791517395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78526652984024703722023193 58894989738018527791517395)
  ·
    refine ⟨88342484607027791687276093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58894989738018527791517395 88342484607027791687276093)
    ·
      refine ⟨33128431727635421882728535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88342484607027791687276093 33128431727635421882728535)
      ·
        refine ⟨49692647591453132824092803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33128431727635421882728535 49692647591453132824092803)
        ·
          refine ⟨74538971387179699236139205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49692647591453132824092803 74538971387179699236139205)
          ·
            refine ⟨13976057135096193606776101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74538971387179699236139205 13976057135096193606776101)
            ·
              refine ⟨2620510712830536301270519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13976057135096193606776101 2620510712830536301270519)
              ·
                refine ⟨3930766069245804451905779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620510712830536301270519 3930766069245804451905779)
                ·
                  refine ⟨5896149103868706677858669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930766069245804451905779 5896149103868706677858669)
                  ·
                    refine ⟨2211055913950765004197001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5896149103868706677858669 2211055913950765004197001)
                    ·
                      refine ⟨1658291935463073753147751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2211055913950765004197001 1658291935463073753147751)
                      ·
                        rfl

theorem cell23_3229512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_3229512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229512 prefixEnd_3229512 := by exact prefixLift 3229512
  have htrace : WordTrace (prefixWord ++ tailWord_3229512) baseStart_3229512 baseEnd_3229512 := by
    simpa [prefixWord, tailWord_3229512, baseEnd_3229512] using wordTrace_append hprefix tailTrace_3229512
  have hstable : (prefixWord ++ tailWord_3229512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229512).length < 2 ^ (prefixWord ++ tailWord_3229512).sum := by decide
  have hdescent : baseEnd_3229512 < baseStart_3229512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229561 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 1, 7]
def baseStart_3229561 : Nat := 118140960795 + 3229561 * 2 ^ 59
def prefixEnd_3229561 : Nat := 4983230072969 + 3 ^ 40 * 3229561 * 2
def baseEnd_3229561 : Nat := 552772365338381353811675

theorem tailTrace_3229561 : CollatzResearch.WordTrace tailWord_3229561 prefixEnd_3229561 552772365338381353811675 := by
  unfold tailWord_3229561
  simp only [CollatzResearch.WordTrace]
  refine ⟨117791766652859536951568537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78527844435239691301045691 117791766652859536951568537)
  ·
    refine ⟨88343824989644652713676403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117791766652859536951568537 88343824989644652713676403)
    ·
      refine ⟨132515737484466979070514605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88343824989644652713676403 132515737484466979070514605)
      ·
        refine ⟨49693401556675117151442977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132515737484466979070514605 49693401556675117151442977)
        ·
          refine ⟨37270051167506337863582233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49693401556675117151442977 37270051167506337863582233)
          ·
            refine ⟨27952538375629753397686675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37270051167506337863582233 27952538375629753397686675)
            ·
              refine ⟨41928807563444630096530013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27952538375629753397686675 41928807563444630096530013)
              ·
                refine ⟨15723302836291736286198755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41928807563444630096530013 15723302836291736286198755)
                ·
                  refine ⟨23584954254437604429298133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15723302836291736286198755 23584954254437604429298133)
                  ·
                    refine ⟨552772365338381353811675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23584954254437604429298133 552772365338381353811675)
                    ·
                      rfl

theorem cell23_3229561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_3229561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229561 prefixEnd_3229561 := by exact prefixLift 3229561
  have htrace : WordTrace (prefixWord ++ tailWord_3229561) baseStart_3229561 baseEnd_3229561 := by
    simpa [prefixWord, tailWord_3229561, baseEnd_3229561] using wordTrace_append hprefix tailTrace_3229561
  have hstable : (prefixWord ++ tailWord_3229561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229561).length < 2 ^ (prefixWord ++ tailWord_3229561).sum := by decide
  have hdescent : baseEnd_3229561 < baseStart_3229561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229582 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_3229582 : Nat := 118140960795 + 3229582 * 2 ^ 59
def prefixEnd_3229582 : Nat := 4983230072969 + 3 ^ 40 * 3229582 * 2
def baseEnd_3229582 : Nat := 184258653234320942141381

theorem tailTrace_3229582 : CollatzResearch.WordTrace tailWord_3229582 prefixEnd_3229582 184258653234320942141381 := by
  unfold tailWord_3229582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14724066573222932192260375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78528355057188971692055333 14724066573222932192260375)
  ·
    refine ⟨22086099859834398288390563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14724066573222932192260375 22086099859834398288390563)
    ·
      refine ⟨33129149789751597432585845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22086099859834398288390563 33129149789751597432585845)
      ·
        refine ⟨3105857792789212259304923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33129149789751597432585845 3105857792789212259304923)
        ·
          refine ⟨4658786689183818388957385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105857792789212259304923 4658786689183818388957385)
          ·
            refine ⟨3494090016887863791718039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4658786689183818388957385 3494090016887863791718039)
            ·
              refine ⟨5241135025331795687577059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494090016887863791718039 5241135025331795687577059)
              ·
                refine ⟨7861702537997693531365589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241135025331795687577059 7861702537997693531365589)
                ·
                  refine ⟨184258653234320942141381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7861702537997693531365589 184258653234320942141381)
                  ·
                    rfl

theorem cell23_3229582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_3229582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229582 prefixEnd_3229582 := by exact prefixLift 3229582
  have htrace : WordTrace (prefixWord ++ tailWord_3229582) baseStart_3229582 baseEnd_3229582 := by
    simpa [prefixWord, tailWord_3229582, baseEnd_3229582] using wordTrace_append hprefix tailTrace_3229582
  have hstable : (prefixWord ++ tailWord_3229582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229582).length < 2 ^ (prefixWord ++ tailWord_3229582).sum := by decide
  have hdescent : baseEnd_3229582 < baseStart_3229582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229588 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3229588 : Nat := 118140960795 + 3229588 * 2 ^ 59
def prefixEnd_3229588 : Nat := 4983230072969 + 3 ^ 40 * 3229588 * 2
def baseEnd_3229588 : Nat := 1658330959992815455797401

theorem tailTrace_3229588 : CollatzResearch.WordTrace tailWord_3229588 prefixEnd_3229588 1658330959992815455797401 := by
  unfold tailWord_3229588
  simp only [CollatzResearch.WordTrace]
  refine ⟨58896375711880860281400709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78528500949174480375200945 58896375711880860281400709)
  ·
    refine ⟨11043070445977661302762633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58896375711880860281400709 11043070445977661302762633)
    ·
      refine ⟨8282302834483245977071975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11043070445977661302762633 8282302834483245977071975)
      ·
        refine ⟨12423454251724868965607963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8282302834483245977071975 12423454251724868965607963)
        ·
          refine ⟨18635181377587303448411945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12423454251724868965607963 18635181377587303448411945)
          ·
            refine ⟨13976386033190477586308959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18635181377587303448411945 13976386033190477586308959)
            ·
              refine ⟨20964579049785716379463439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13976386033190477586308959 20964579049785716379463439)
              ·
                refine ⟨31446868574678574569195159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20964579049785716379463439 31446868574678574569195159)
                ·
                  refine ⟨47170302862017861853792739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31446868574678574569195159 47170302862017861853792739)
                  ·
                    refine ⟨70755454293026792780689109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47170302862017861853792739 70755454293026792780689109)
                    ·
                      refine ⟨1658330959992815455797401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70755454293026792780689109 1658330959992815455797401)
                      ·
                        rfl

theorem cell23_3229588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3229588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229588 prefixEnd_3229588 := by exact prefixLift 3229588
  have htrace : WordTrace (prefixWord ++ tailWord_3229588) baseStart_3229588 baseEnd_3229588 := by
    simpa [prefixWord, tailWord_3229588, baseEnd_3229588] using wordTrace_append hprefix tailTrace_3229588
  have hstable : (prefixWord ++ tailWord_3229588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229588).length < 2 ^ (prefixWord ++ tailWord_3229588).sum := by decide
  have hdescent : baseEnd_3229588 < baseStart_3229588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229618 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_3229618 : Nat := 118140960795 + 3229618 * 2 ^ 59
def prefixEnd_3229618 : Nat := 4983230072969 + 3 ^ 40 * 3229618 * 2
def baseEnd_3229618 : Nat := 1658346364412450338422263

theorem tailTrace_3229618 : CollatzResearch.WordTrace tailWord_3229618 prefixEnd_3229618 1658346364412450338422263 := by
  unfold tailWord_3229618
  simp only [CollatzResearch.WordTrace]
  refine ⟨29448461403413258921598377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78529230409102023790929005 29448461403413258921598377)
  ·
    refine ⟨22086346052559944191198783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29448461403413258921598377 22086346052559944191198783)
    ·
      refine ⟨33129519078839916286798175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22086346052559944191198783 33129519078839916286798175)
      ·
        refine ⟨49694278618259874430197263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33129519078839916286798175 49694278618259874430197263)
        ·
          refine ⟨74541417927389811645295895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49694278618259874430197263 74541417927389811645295895)
          ·
            refine ⟨111812126891084717467943843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74541417927389811645295895 111812126891084717467943843)
            ·
              refine ⟨167718190336627076201915765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111812126891084717467943843 167718190336627076201915765)
              ·
                refine ⟨15723580344058788393929603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167718190336627076201915765 15723580344058788393929603)
                ·
                  refine ⟨23585370516088182590894405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15723580344058788393929603 23585370516088182590894405)
                  ·
                    refine ⟨4422256971766534235792701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23585370516088182590894405 4422256971766534235792701)
                    ·
                      refine ⟨1658346364412450338422263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4422256971766534235792701 1658346364412450338422263)
                      ·
                        rfl

theorem cell23_3229618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_3229618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229618 prefixEnd_3229618 := by exact prefixLift 3229618
  have htrace : WordTrace (prefixWord ++ tailWord_3229618) baseStart_3229618 baseEnd_3229618 := by
    simpa [prefixWord, tailWord_3229618, baseEnd_3229618] using wordTrace_append hprefix tailTrace_3229618
  have hstable : (prefixWord ++ tailWord_3229618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229618).length < 2 ^ (prefixWord ++ tailWord_3229618).sum := by decide
  have hdescent : baseEnd_3229618 < baseStart_3229618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229641 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_3229641 : Nat := 118140960795 + 3229641 * 2 ^ 59
def prefixEnd_3229641 : Nat := 4983230072969 + 3 ^ 40 * 3229641 * 2
def baseEnd_3229641 : Nat := 1658358174467503748434657

theorem tailTrace_3229641 : CollatzResearch.WordTrace tailWord_3229641 prefixEnd_3229641 1658358174467503748434657 := by
  unfold tailWord_3229641
  simp only [CollatzResearch.WordTrace]
  refine ⟨117794684492569710614480777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78529789661713140409653851 117794684492569710614480777)
  ·
    refine ⟨88346013369427282960860583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117794684492569710614480777 88346013369427282960860583)
    ·
      refine ⟨132519020054140924441290875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88346013369427282960860583 132519020054140924441290875)
      ·
        refine ⟨198778530081211386661936313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132519020054140924441290875 198778530081211386661936313)
        ·
          refine ⟨149083897560908539996452235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198778530081211386661936313 149083897560908539996452235)
          ·
            refine ⟨223625846341362809994678353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149083897560908539996452235 223625846341362809994678353)
            ·
              refine ⟨167719384756022107496008765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223625846341362809994678353 167719384756022107496008765)
              ·
                refine ⟨62894769283508290311003287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167719384756022107496008765 62894769283508290311003287)
                ·
                  refine ⟨94342153925262435466504931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62894769283508290311003287 94342153925262435466504931)
                  ·
                    refine ⟨141513230887893653199757397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94342153925262435466504931 141513230887893653199757397)
                    ·
                      refine ⟨1658358174467503748434657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 141513230887893653199757397 1658358174467503748434657)
                      ·
                        rfl

theorem cell23_3229641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_3229641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229641 prefixEnd_3229641 := by exact prefixLift 3229641
  have htrace : WordTrace (prefixWord ++ tailWord_3229641) baseStart_3229641 baseEnd_3229641 := by
    simpa [prefixWord, tailWord_3229641, baseEnd_3229641] using wordTrace_append hprefix tailTrace_3229641
  have hstable : (prefixWord ++ tailWord_3229641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229641).length < 2 ^ (prefixWord ++ tailWord_3229641).sum := by decide
  have hdescent : baseEnd_3229641 < baseStart_3229641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229665 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_3229665 : Nat := 118140960795 + 3229665 * 2 ^ 59
def prefixEnd_3229665 : Nat := 4983230072969 + 3 ^ 40 * 3229665 * 2
def baseEnd_3229665 : Nat := 1658370498003211654534547

theorem tailTrace_3229665 : CollatzResearch.WordTrace tailWord_3229665 prefixEnd_3229665 1658370498003211654534547 := by
  unfold tailWord_3229665
  simp only [CollatzResearch.WordTrace]
  refine ⟨117795559844482762713354449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78530373229655175142236299 117795559844482762713354449)
  ·
    refine ⟨88346669883362072035015837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117795559844482762713354449 88346669883362072035015837)
    ·
      refine ⟨33130001206260777013130939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88346669883362072035015837 33130001206260777013130939)
      ·
        refine ⟨49695001809391165519696409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33130001206260777013130939 49695001809391165519696409)
        ·
          refine ⟨37271251357043374139772307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49695001809391165519696409 37271251357043374139772307)
          ·
            refine ⟨55906877035565061209658461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37271251357043374139772307 55906877035565061209658461)
            ·
              refine ⟨20965078888336897953621923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55906877035565061209658461 20965078888336897953621923)
              ·
                refine ⟨31447618332505346930432885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20965078888336897953621923 31447618332505346930432885)
                ·
                  refine ⟨2948214218672376274728083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31447618332505346930432885 2948214218672376274728083)
                  ·
                    refine ⟨4422321328008564412092125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2948214218672376274728083 4422321328008564412092125)
                    ·
                      refine ⟨1658370498003211654534547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4422321328008564412092125 1658370498003211654534547)
                      ·
                        rfl

theorem cell23_3229665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_3229665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229665 prefixEnd_3229665 := by exact prefixLift 3229665
  have htrace : WordTrace (prefixWord ++ tailWord_3229665) baseStart_3229665 baseEnd_3229665 := by
    simpa [prefixWord, tailWord_3229665, baseEnd_3229665] using wordTrace_append hprefix tailTrace_3229665
  have hstable : (prefixWord ++ tailWord_3229665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229665).length < 2 ^ (prefixWord ++ tailWord_3229665).sum := by decide
  have hdescent : baseEnd_3229665 < baseStart_3229665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229666 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3229666 : Nat := 118140960795 + 3229666 * 2 ^ 59
def prefixEnd_3229666 : Nat := 4983230072969 + 3 ^ 40 * 3229666 * 2
def baseEnd_3229666 : Nat := 1658371011483866150622043

theorem tailTrace_3229666 : CollatzResearch.WordTrace tailWord_3229666 prefixEnd_3229666 1658371011483866150622043 := by
  unfold tailWord_3229666
  simp only [CollatzResearch.WordTrace]
  refine ⟨29448899079369784971035213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78530397544986093256093901 29448899079369784971035213)
  ·
    refine ⟨11043337154763669364138205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29448899079369784971035213 11043337154763669364138205)
    ·
      refine ⟨4141251433036376011551827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11043337154763669364138205 4141251433036376011551827)
      ·
        refine ⟨6211877149554564017327741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4141251433036376011551827 6211877149554564017327741)
        ·
          refine ⟨2329453931082961506497903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6211877149554564017327741 2329453931082961506497903)
          ·
            refine ⟨3494180896624442259746855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329453931082961506497903 3494180896624442259746855)
            ·
              refine ⟨5241271344936663389620283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494180896624442259746855 5241271344936663389620283)
              ·
                refine ⟨7861907017404995084430425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241271344936663389620283 7861907017404995084430425)
                ·
                  refine ⟨5896430263053746313322819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7861907017404995084430425 5896430263053746313322819)
                  ·
                    refine ⟨8844645394580619469984229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5896430263053746313322819 8844645394580619469984229)
                    ·
                      refine ⟨1658371011483866150622043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8844645394580619469984229 1658371011483866150622043)
                      ·
                        rfl

theorem cell23_3229666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3229666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229666 prefixEnd_3229666 := by exact prefixLift 3229666
  have htrace : WordTrace (prefixWord ++ tailWord_3229666) baseStart_3229666 baseEnd_3229666 := by
    simpa [prefixWord, tailWord_3229666, baseEnd_3229666] using wordTrace_append hprefix tailTrace_3229666
  have hstable : (prefixWord ++ tailWord_3229666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229666).length < 2 ^ (prefixWord ++ tailWord_3229666).sum := by decide
  have hdescent : baseEnd_3229666 < baseStart_3229666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229668 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_3229668 : Nat := 118140960795 + 3229668 * 2 ^ 59
def prefixEnd_3229668 : Nat := 4983230072969 + 3 ^ 40 * 3229668 * 2
def baseEnd_3229668 : Nat := 552790679481725047599011

theorem tailTrace_3229668 : CollatzResearch.WordTrace tailWord_3229668 prefixEnd_3229668 552790679481725047599011 := by
  unfold tailWord_3229668
  simp only [CollatzResearch.WordTrace]
  refine ⟨58897834631735947112856829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78530446175647929483809105 58897834631735947112856829)
  ·
    refine ⟨22086687986900980167321311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58897834631735947112856829 22086687986900980167321311)
    ·
      refine ⟨33130031980351470250981967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22086687986900980167321311 33130031980351470250981967)
      ·
        refine ⟨49695047970527205376472951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33130031980351470250981967 49695047970527205376472951)
        ·
          refine ⟨74542571955790808064709427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49695047970527205376472951 74542571955790808064709427)
          ·
            refine ⟨111813857933686212097064141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74542571955790808064709427 111813857933686212097064141)
            ·
              refine ⟨41930196725132329536399053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111813857933686212097064141 41930196725132329536399053)
              ·
                refine ⟨15723823771924623576149645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41930196725132329536399053 15723823771924623576149645)
                ·
                  refine ⟨5896433914471733841056117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15723823771924623576149645 5896433914471733841056117)
                  ·
                    refine ⟨552790679481725047599011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5896433914471733841056117 552790679481725047599011)
                    ·
                      rfl

theorem cell23_3229668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_3229668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229668 prefixEnd_3229668 := by exact prefixLift 3229668
  have htrace : WordTrace (prefixWord ++ tailWord_3229668) baseStart_3229668 baseEnd_3229668 := by
    simpa [prefixWord, tailWord_3229668, baseEnd_3229668] using wordTrace_append hprefix tailTrace_3229668
  have hstable : (prefixWord ++ tailWord_3229668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229668).length < 2 ^ (prefixWord ++ tailWord_3229668).sum := by decide
  have hdescent : baseEnd_3229668 < baseStart_3229668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229715 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 2, 4]
def baseStart_3229715 : Nat := 118140960795 + 3229715 * 2 ^ 59
def prefixEnd_3229715 : Nat := 4983230072969 + 3 ^ 40 * 3229715 * 2
def baseEnd_3229715 : Nat := 552798724011978819636439

theorem tailTrace_3229715 : CollatzResearch.WordTrace tailWord_3229715 prefixEnd_3229715 552798724011978819636439 := by
  unfold tailWord_3229715
  simp only [CollatzResearch.WordTrace]
  refine ⟨117797383494301621252674599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78531588996201080835116399 117797383494301621252674599)
  ·
    refine ⟨176696075241452431879011899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117797383494301621252674599 176696075241452431879011899)
    ·
      refine ⟨265044112862178647818517849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176696075241452431879011899 265044112862178647818517849)
      ·
        refine ⟨198783084646633985863888387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265044112862178647818517849 198783084646633985863888387)
        ·
          refine ⟨298174626969950978795832581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198783084646633985863888387 298174626969950978795832581)
          ·
            refine ⟨55907742556865808524218609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298174626969950978795832581 55907742556865808524218609)
            ·
              refine ⟨41930806917649356393163957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55907742556865808524218609 41930806917649356393163957)
              ·
                refine ⟨3931013148529627161859121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41930806917649356393163957 3931013148529627161859121)
                ·
                  refine ⟨2948259861397220371394341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3931013148529627161859121 2948259861397220371394341)
                  ·
                    refine ⟨552798724011978819636439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2948259861397220371394341 552798724011978819636439)
                    ·
                      rfl

theorem cell23_3229715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 4].length) (baseStart_3229715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229715 prefixEnd_3229715 := by exact prefixLift 3229715
  have htrace : WordTrace (prefixWord ++ tailWord_3229715) baseStart_3229715 baseEnd_3229715 := by
    simpa [prefixWord, tailWord_3229715, baseEnd_3229715] using wordTrace_append hprefix tailTrace_3229715
  have hstable : (prefixWord ++ tailWord_3229715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229715).length < 2 ^ (prefixWord ++ tailWord_3229715).sum := by decide
  have hdescent : baseEnd_3229715 < baseStart_3229715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229722 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4]
def baseStart_3229722 : Nat := 118140960795 + 3229722 * 2 ^ 59
def prefixEnd_3229722 : Nat := 4983230072969 + 3 ^ 40 * 3229722 * 2
def baseEnd_3229722 : Nat := 1658399766400517931521785

theorem tailTrace_3229722 : CollatzResearch.WordTrace tailWord_3229722 prefixEnd_3229722 1658399766400517931521785 := by
  unfold tailWord_3229722
  simp only [CollatzResearch.WordTrace]
  refine ⟨29449409701319065362044855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78531759203517507632119613 29449409701319065362044855)
  ·
    refine ⟨44174114551978598043067283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29449409701319065362044855 44174114551978598043067283)
    ·
      refine ⟨66261171827967897064600925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44174114551978598043067283 66261171827967897064600925)
      ·
        refine ⟨24847939435487961399225347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66261171827967897064600925 24847939435487961399225347)
        ·
          refine ⟨37271909153231942098838021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24847939435487961399225347 37271909153231942098838021)
          ·
            refine ⟨6988482966230989143532129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37271909153231942098838021 6988482966230989143532129)
            ·
              refine ⟨5241362224673241857649097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6988482966230989143532129 5241362224673241857649097)
              ·
                refine ⟨3931021668504931393236823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5241362224673241857649097 3931021668504931393236823)
                ·
                  refine ⟨5896532502757397089855235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931021668504931393236823 5896532502757397089855235)
                  ·
                    refine ⟨8844798754136095634782853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5896532502757397089855235 8844798754136095634782853)
                    ·
                      refine ⟨1658399766400517931521785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8844798754136095634782853 1658399766400517931521785)
                      ·
                        rfl

theorem cell23_3229722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_3229722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229722 prefixEnd_3229722 := by exact prefixLift 3229722
  have htrace : WordTrace (prefixWord ++ tailWord_3229722) baseStart_3229722 baseEnd_3229722 := by
    simpa [prefixWord, tailWord_3229722, baseEnd_3229722] using wordTrace_append hprefix tailTrace_3229722
  have hstable : (prefixWord ++ tailWord_3229722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229722).length < 2 ^ (prefixWord ++ tailWord_3229722).sum := by decide
  have hdescent : baseEnd_3229722 < baseStart_3229722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229739 : List Nat := [1, 1, 1, 1, 2, 1, 4, 7, 1, 2, 2]
def baseStart_3229739 : Nat := 118140960795 + 3229739 * 2 ^ 59
def prefixEnd_3229739 : Nat := 4983230072969 + 3 ^ 40 * 3229739 * 2
def baseEnd_3229739 : Nat := 1658408495571644365009207

theorem tailTrace_3229739 : CollatzResearch.WordTrace tailWord_3229739 prefixEnd_3229739 1658408495571644365009207 := by
  unfold tailWord_3229739
  simp only [CollatzResearch.WordTrace]
  refine ⟨117798258846214673351548271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78532172564143115567698847 117798258846214673351548271)
  ·
    refine ⟨176697388269322010027322407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117798258846214673351548271 176697388269322010027322407)
    ·
      refine ⟨265046082403983015040983611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176697388269322010027322407 265046082403983015040983611)
      ·
        refine ⟨397569123605974522561475417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265046082403983015040983611 397569123605974522561475417)
        ·
          refine ⟨298176842704480891921106563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397569123605974522561475417 298176842704480891921106563)
          ·
            refine ⟨447265264056721337881659845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298176842704480891921106563 447265264056721337881659845)
            ·
              refine ⟨83862237010635250852811221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 447265264056721337881659845 83862237010635250852811221)
              ·
                refine ⟨1965521179936763691862763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83862237010635250852811221 1965521179936763691862763)
                ·
                  refine ⟨2948281769905145537794145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1965521179936763691862763 2948281769905145537794145)
                  ·
                    refine ⟨2211211327428859153345609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2948281769905145537794145 2211211327428859153345609)
                    ·
                      refine ⟨1658408495571644365009207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2211211327428859153345609 1658408495571644365009207)
                      ·
                        rfl

theorem cell23_3229739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 1, 2, 2].length) (baseStart_3229739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229739 prefixEnd_3229739 := by exact prefixLift 3229739
  have htrace : WordTrace (prefixWord ++ tailWord_3229739) baseStart_3229739 baseEnd_3229739 := by
    simpa [prefixWord, tailWord_3229739, baseEnd_3229739] using wordTrace_append hprefix tailTrace_3229739
  have hstable : (prefixWord ++ tailWord_3229739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229739).length < 2 ^ (prefixWord ++ tailWord_3229739).sum := by decide
  have hdescent : baseEnd_3229739 < baseStart_3229739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229742 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_3229742 : Nat := 118140960795 + 3229742 * 2 ^ 59
def prefixEnd_3229742 : Nat := 4983230072969 + 3 ^ 40 * 3229742 * 2
def baseEnd_3229742 : Nat := 1658410036013607853271693

theorem tailTrace_3229742 : CollatzResearch.WordTrace tailWord_3229742 prefixEnd_3229742 1658410036013607853271693 := by
  unfold tailWord_3229742
  simp only [CollatzResearch.WordTrace]
  refine ⟨14724796033150475607988435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78532245510135869909271653 14724796033150475607988435)
  ·
    refine ⟨22087194049725713411982653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14724796033150475607988435 22087194049725713411982653)
    ·
      refine ⟨8282697768647142529493495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22087194049725713411982653 8282697768647142529493495)
      ·
        refine ⟨12424046652970713794240243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8282697768647142529493495 12424046652970713794240243)
        ·
          refine ⟨18636069979456070691360365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12424046652970713794240243 18636069979456070691360365)
          ·
            refine ⟨6988526242296026509260137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18636069979456070691360365 6988526242296026509260137)
            ·
              refine ⟨5241394681722019881945103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6988526242296026509260137 5241394681722019881945103)
              ·
                refine ⟨7862092022583029822917655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241394681722019881945103 7862092022583029822917655)
                ·
                  refine ⟨11793138033874544734376483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7862092022583029822917655 11793138033874544734376483)
                  ·
                    refine ⟨17689707050811817101564725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11793138033874544734376483 17689707050811817101564725)
                    ·
                      refine ⟨1658410036013607853271693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17689707050811817101564725 1658410036013607853271693)
                      ·
                        rfl

theorem cell23_3229742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_3229742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229742 prefixEnd_3229742 := by exact prefixLift 3229742
  have htrace : WordTrace (prefixWord ++ tailWord_3229742) baseStart_3229742 baseEnd_3229742 := by
    simpa [prefixWord, tailWord_3229742, baseEnd_3229742] using wordTrace_append hprefix tailTrace_3229742
  have hstable : (prefixWord ++ tailWord_3229742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229742).length < 2 ^ (prefixWord ++ tailWord_3229742).sum := by decide
  have hdescent : baseEnd_3229742 < baseStart_3229742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229765 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 2, 7, 2]
def baseStart_3229765 : Nat := 118140960795 + 3229765 * 2 ^ 59
def prefixEnd_3229765 : Nat := 4983230072969 + 3 ^ 40 * 3229765 * 2
def baseEnd_3229765 : Nat := 1658421846068661263284087

theorem tailTrace_3229765 : CollatzResearch.WordTrace tailWord_3229765 prefixEnd_3229765 1658421846068661263284087 := by
  unfold tailWord_3229765
  simp only [CollatzResearch.WordTrace]
  refine ⟨117799207144120479791994749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78532804762746986527996499 117799207144120479791994749)
  ·
    refine ⟨44174702679045179921998031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117799207144120479791994749 44174702679045179921998031)
    ·
      refine ⟨66262054018567769882997047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44174702679045179921998031 66262054018567769882997047)
      ·
        refine ⟨99393081027851654824495571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66262054018567769882997047 99393081027851654824495571)
        ·
          refine ⟨149089621541777482236743357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99393081027851654824495571 149089621541777482236743357)
          ·
            refine ⟨55908608078166555838778759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149089621541777482236743357 55908608078166555838778759)
            ·
              refine ⟨83862912117249833758168139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55908608078166555838778759 83862912117249833758168139)
              ·
                refine ⟨125794368175874750637252209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83862912117249833758168139 125794368175874750637252209)
                ·
                  refine ⟨94345776131906062977939157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125794368175874750637252209 94345776131906062977939157)
                  ·
                    refine ⟨2211229128091548351045449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 94345776131906062977939157 2211229128091548351045449)
                    ·
                      refine ⟨1658421846068661263284087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2211229128091548351045449 1658421846068661263284087)
                      ·
                        rfl

theorem cell23_3229765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 7, 2].length) (baseStart_3229765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229765 prefixEnd_3229765 := by exact prefixLift 3229765
  have htrace : WordTrace (prefixWord ++ tailWord_3229765) baseStart_3229765 baseEnd_3229765 := by
    simpa [prefixWord, tailWord_3229765, baseEnd_3229765] using wordTrace_append hprefix tailTrace_3229765
  have hstable : (prefixWord ++ tailWord_3229765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229765).length < 2 ^ (prefixWord ++ tailWord_3229765).sum := by decide
  have hdescent : baseEnd_3229765 < baseStart_3229765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229768 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_3229768 : Nat := 118140960795 + 3229768 * 2 ^ 59
def prefixEnd_3229768 : Nat := 4983230072969 + 3 ^ 40 * 3229768 * 2
def baseEnd_3229768 : Nat := 1658423386510624751546573

theorem tailTrace_3229768 : CollatzResearch.WordTrace tailWord_3229768 prefixEnd_3229768 1658423386510624751546573 := by
  unfold tailWord_3229768
  simp only [CollatzResearch.WordTrace]
  refine ⟨58899658281554805652176979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78532877708739740869569305 58899658281554805652176979)
  ·
    refine ⟨88349487422332208478265469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58899658281554805652176979 88349487422332208478265469)
    ·
      refine ⟨33131057783374578179349551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88349487422332208478265469 33131057783374578179349551)
      ·
        refine ⟨49696586675061867269024327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33131057783374578179349551 49696586675061867269024327)
        ·
          refine ⟨74544880012592800903536491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49696586675061867269024327 74544880012592800903536491)
          ·
            refine ⟨111817320018889201355304737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74544880012592800903536491 111817320018889201355304737)
            ·
              refine ⟨83862990014166901016478553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111817320018889201355304737 83862990014166901016478553)
              ·
                refine ⟨62897242510625175762358915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83862990014166901016478553 62897242510625175762358915)
                ·
                  refine ⟨94345863765937763643538373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62897242510625175762358915 94345863765937763643538373)
                  ·
                    refine ⟨17689849456113330683163445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94345863765937763643538373 17689849456113330683163445)
                    ·
                      refine ⟨1658423386510624751546573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17689849456113330683163445 1658423386510624751546573)
                      ·
                        rfl

theorem cell23_3229768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_3229768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229768 prefixEnd_3229768 := by exact prefixLift 3229768
  have htrace : WordTrace (prefixWord ++ tailWord_3229768) baseStart_3229768 baseEnd_3229768 := by
    simpa [prefixWord, tailWord_3229768, baseEnd_3229768] using wordTrace_append hprefix tailTrace_3229768
  have hstable : (prefixWord ++ tailWord_3229768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229768).length < 2 ^ (prefixWord ++ tailWord_3229768).sum := by decide
  have hdescent : baseEnd_3229768 < baseStart_3229768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229789 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3229789 : Nat := 118140960795 + 3229789 * 2 ^ 59
def prefixEnd_3229789 : Nat := 4983230072969 + 3 ^ 40 * 3229789 * 2
def baseEnd_3229789 : Nat := 1658434169604369169383977

theorem tailTrace_3229789 : CollatzResearch.WordTrace tailWord_3229789 prefixEnd_3229789 1658434169604369169383977 := by
  unfold tailWord_3229789
  simp only [CollatzResearch.WordTrace]
  refine ⟨117800082496033531890868421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78533388330689021260578947 117800082496033531890868421)
  ·
    refine ⟨22087515468006287229537829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117800082496033531890868421 22087515468006287229537829)
    ·
      refine ⟨4141409150251178855538343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22087515468006287229537829 4141409150251178855538343)
      ·
        refine ⟨6212113725376768283307515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4141409150251178855538343 6212113725376768283307515)
        ·
          refine ⟨9318170588065152424961273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6212113725376768283307515 9318170588065152424961273)
          ·
            refine ⟨6988627941048864318720955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9318170588065152424961273 6988627941048864318720955)
            ·
              refine ⟨10482941911573296478081433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6988627941048864318720955 10482941911573296478081433)
              ·
                refine ⟨7862206433679972358561075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10482941911573296478081433 7862206433679972358561075)
                ·
                  refine ⟨11793309650519958537841613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7862206433679972358561075 11793309650519958537841613)
                  ·
                    refine ⟨4422491118944984451690605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11793309650519958537841613 4422491118944984451690605)
                    ·
                      refine ⟨1658434169604369169383977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4422491118944984451690605 1658434169604369169383977)
                      ·
                        rfl

theorem cell23_3229789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3229789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229789 prefixEnd_3229789 := by exact prefixLift 3229789
  have htrace : WordTrace (prefixWord ++ tailWord_3229789) baseStart_3229789 baseEnd_3229789 := by
    simpa [prefixWord, tailWord_3229789, baseEnd_3229789] using wordTrace_append hprefix tailTrace_3229789
  have hstable : (prefixWord ++ tailWord_3229789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229789).length < 2 ^ (prefixWord ++ tailWord_3229789).sum := by decide
  have hdescent : baseEnd_3229789 < baseStart_3229789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229805 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_3229805 : Nat := 118140960795 + 3229805 * 2 ^ 59
def prefixEnd_3229805 : Nat := 4983230072969 + 3 ^ 40 * 3229805 * 2
def baseEnd_3229805 : Nat := 552814128431613702261301

theorem tailTrace_3229805 : CollatzResearch.WordTrace tailWord_3229805 prefixEnd_3229805 552814128431613702261301 := by
  unfold tailWord_3229805
  simp only [CollatzResearch.WordTrace]
  refine ⟨117800666063975566623450869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78533777375983711082300579 117800666063975566623450869)
  ·
    refine ⟨11043812443497709370948519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117800666063975566623450869 11043812443497709370948519)
    ·
      refine ⟨16565718665246564056422779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11043812443497709370948519 16565718665246564056422779)
      ·
        refine ⟨24848577997869846084634169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16565718665246564056422779 24848577997869846084634169)
        ·
          refine ⟨18636433498402384563475627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24848577997869846084634169 18636433498402384563475627)
          ·
            refine ⟨27954650247603576845213441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18636433498402384563475627 27954650247603576845213441)
            ·
              refine ⟨20965987685702682633910081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27954650247603576845213441 20965987685702682633910081)
              ·
                refine ⟨15724490764277011975432561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20965987685702682633910081 15724490764277011975432561)
                ·
                  refine ⟨11793368073207758981574421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15724490764277011975432561 11793368073207758981574421)
                  ·
                    refine ⟨552814128431613702261301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11793368073207758981574421 552814128431613702261301)
                    ·
                      rfl

theorem cell23_3229805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_3229805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229805 prefixEnd_3229805 := by exact prefixLift 3229805
  have htrace : WordTrace (prefixWord ++ tailWord_3229805) baseStart_3229805 baseEnd_3229805 := by
    simpa [prefixWord, tailWord_3229805, baseEnd_3229805] using wordTrace_append hprefix tailTrace_3229805
  have hstable : (prefixWord ++ tailWord_3229805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229805).length < 2 ^ (prefixWord ++ tailWord_3229805).sum := by decide
  have hdescent : baseEnd_3229805 < baseStart_3229805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229815 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 3]
def baseStart_3229815 : Nat := 118140960795 + 3229815 * 2 ^ 59
def prefixEnd_3229815 : Nat := 4983230072969 + 3 ^ 40 * 3229815 * 2
def baseEnd_3229815 : Nat := 1658447520101386067658857

theorem tailTrace_3229815 : CollatzResearch.WordTrace tailWord_3229815 prefixEnd_3229815 1658447520101386067658857 := by
  unfold tailWord_3229815
  simp only [CollatzResearch.WordTrace]
  refine ⟨117801030793939338331314899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78534020529292892220876599 117801030793939338331314899)
  ·
    refine ⟨176701546190909007496972349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117801030793939338331314899 176701546190909007496972349)
    ·
      refine ⟨66263079821590877811364631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176701546190909007496972349 66263079821590877811364631)
      ·
        refine ⟨99394619732386316717046947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66263079821590877811364631 99394619732386316717046947)
        ·
          refine ⟨149091929598579475075570421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99394619732386316717046947 149091929598579475075570421)
          ·
            refine ⟨13977368399866825788334727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149091929598579475075570421 13977368399866825788334727)
            ·
              refine ⟨20966052599800238682502091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13977368399866825788334727 20966052599800238682502091)
              ·
                refine ⟨31449078899700358023753137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20966052599800238682502091 31449078899700358023753137)
                ·
                  refine ⟨23586809174775268517814853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31449078899700358023753137 23586809174775268517814853)
                  ·
                    refine ⟨4422526720270362847090285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23586809174775268517814853 4422526720270362847090285)
                    ·
                      refine ⟨1658447520101386067658857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4422526720270362847090285 1658447520101386067658857)
                      ·
                        rfl

theorem cell23_3229815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_3229815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229815 prefixEnd_3229815 := by exact prefixLift 3229815
  have htrace : WordTrace (prefixWord ++ tailWord_3229815) baseStart_3229815 baseEnd_3229815 := by
    simpa [prefixWord, tailWord_3229815, baseEnd_3229815] using wordTrace_append hprefix tailTrace_3229815
  have hstable : (prefixWord ++ tailWord_3229815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229815).length < 2 ^ (prefixWord ++ tailWord_3229815).sum := by decide
  have hdescent : baseEnd_3229815 < baseStart_3229815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229818 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 13]
def baseStart_3229818 : Nat := 118140960795 + 3229818 * 2 ^ 59
def prefixEnd_3229818 : Nat := 4983230072969 + 3 ^ 40 * 3229818 * 2
def baseEnd_3229818 : Nat := 184272117838149950657927

theorem tailTrace_3229818 : CollatzResearch.WordTrace tailWord_3229818 prefixEnd_3229818 184272117838149950657927 := by
  unfold tailWord_3229818
  simp only [CollatzResearch.WordTrace]
  refine ⟨29450285053232117460918527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78534093475285646562449405 29450285053232117460918527)
  ·
    refine ⟨44175427579848176191377791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29450285053232117460918527 44175427579848176191377791)
    ·
      refine ⟨66263141369772264287066687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44175427579848176191377791 66263141369772264287066687)
      ·
        refine ⟨99394712054658396430600031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66263141369772264287066687 99394712054658396430600031)
        ·
          refine ⟨149092068081987594645900047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99394712054658396430600031 149092068081987594645900047)
          ·
            refine ⟨223638102122981391968850071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149092068081987594645900047 223638102122981391968850071)
            ·
              refine ⟨335457153184472087953275107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223638102122981391968850071 335457153184472087953275107)
              ·
                refine ⟨503185729776708131929912661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335457153184472087953275107 503185729776708131929912661)
                ·
                  refine ⟨184272117838149950657927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 503185729776708131929912661 184272117838149950657927)
                  ·
                    rfl

theorem cell23_3229818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_3229818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229818 prefixEnd_3229818 := by exact prefixLift 3229818
  have htrace : WordTrace (prefixWord ++ tailWord_3229818) baseStart_3229818 baseEnd_3229818 := by
    simpa [prefixWord, tailWord_3229818, baseEnd_3229818] using wordTrace_append hprefix tailTrace_3229818
  have hstable : (prefixWord ++ tailWord_3229818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229818).length < 2 ^ (prefixWord ++ tailWord_3229818).sum := by decide
  have hdescent : baseEnd_3229818 < baseStart_3229818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229829 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 1, 4, 2]
def baseStart_3229829 : Nat := 118140960795 + 3229829 * 2 ^ 59
def prefixEnd_3229829 : Nat := 4983230072969 + 3 ^ 40 * 3229829 * 2
def baseEnd_3229829 : Nat := 1658454708830549012883793

theorem tailTrace_3229829 : CollatzResearch.WordTrace tailWord_3229829 prefixEnd_3229829 1658454708830549012883793 := by
  unfold tailWord_3229829
  simp only [CollatzResearch.WordTrace]
  refine ⟨117801541415888618722324541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78534360943925745814883027 117801541415888618722324541)
  ·
    refine ⟨44175578030958232020871703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117801541415888618722324541 44175578030958232020871703)
    ·
      refine ⟨66263367046437348031307555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44175578030958232020871703 66263367046437348031307555)
      ·
        refine ⟨99395050569656022046961333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66263367046437348031307555 99395050569656022046961333)
        ·
          refine ⟨9318285990905252066902625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99395050569656022046961333 9318285990905252066902625)
          ·
            refine ⟨6988714493178939050176969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9318285990905252066902625 6988714493178939050176969)
            ·
              refine ⟨5241535869884204287632727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6988714493178939050176969 5241535869884204287632727)
              ·
                refine ⟨7862303804826306431449091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241535869884204287632727 7862303804826306431449091)
                ·
                  refine ⟨11793455707239459647173637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7862303804826306431449091 11793455707239459647173637)
                  ·
                    refine ⟨2211272945107398683845057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11793455707239459647173637 2211272945107398683845057)
                    ·
                      refine ⟨1658454708830549012883793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2211272945107398683845057 1658454708830549012883793)
                      ·
                        rfl

theorem cell23_3229829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 4, 2].length) (baseStart_3229829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229829 prefixEnd_3229829 := by exact prefixLift 3229829
  have htrace : WordTrace (prefixWord ++ tailWord_3229829) baseStart_3229829 baseEnd_3229829 := by
    simpa [prefixWord, tailWord_3229829, baseEnd_3229829] using wordTrace_append hprefix tailTrace_3229829
  have hstable : (prefixWord ++ tailWord_3229829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229829).length < 2 ^ (prefixWord ++ tailWord_3229829).sum := by decide
  have hdescent : baseEnd_3229829 < baseStart_3229829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229845 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_3229845 : Nat := 118140960795 + 3229845 * 2 ^ 59
def prefixEnd_3229845 : Nat := 4983230072969 + 3 ^ 40 * 3229845 * 2
def baseEnd_3229845 : Nat := 1658462924521020950283719

theorem tailTrace_3229845 : CollatzResearch.WordTrace tailWord_3229845 prefixEnd_3229845 1658462924521020950283719 := by
  unfold tailWord_3229845
  simp only [CollatzResearch.WordTrace]
  refine ⟨117802124983830653454906989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78534749989220435636604659 117802124983830653454906989)
  ·
    refine ⟨44175796868936495045590121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117802124983830653454906989 44175796868936495045590121)
    ·
      refine ⟨33131847651702371284192591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44175796868936495045590121 33131847651702371284192591)
      ·
        refine ⟨49697771477553556926288887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33131847651702371284192591 49697771477553556926288887)
        ·
          refine ⟨74546657216330335389433331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49697771477553556926288887 74546657216330335389433331)
          ·
            refine ⟨111819985824495503084149997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74546657216330335389433331 111819985824495503084149997)
            ·
              refine ⟨41932494684185813656556249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111819985824495503084149997 41932494684185813656556249)
              ·
                refine ⟨31449371013139360242417187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41932494684185813656556249 31449371013139360242417187)
                ·
                  refine ⟨47174056519709040363625781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31449371013139360242417187 47174056519709040363625781)
                  ·
                    refine ⟨4422567798722722534089917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47174056519709040363625781 4422567798722722534089917)
                    ·
                      refine ⟨1658462924521020950283719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4422567798722722534089917 1658462924521020950283719)
                      ·
                        rfl

theorem cell23_3229845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_3229845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229845 prefixEnd_3229845 := by exact prefixLift 3229845
  have htrace : WordTrace (prefixWord ++ tailWord_3229845) baseStart_3229845 baseEnd_3229845 := by
    simpa [prefixWord, tailWord_3229845, baseEnd_3229845] using wordTrace_append hprefix tailTrace_3229845
  have hstable : (prefixWord ++ tailWord_3229845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229845).length < 2 ^ (prefixWord ++ tailWord_3229845).sum := by decide
  have hdescent : baseEnd_3229845 < baseStart_3229845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229850 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2]
def baseStart_3229850 : Nat := 118140960795 + 3229850 * 2 ^ 59
def prefixEnd_3229850 : Nat := 4983230072969 + 3 ^ 40 * 3229850 * 2
def baseEnd_3229850 : Nat := 1658465491924293430721197

theorem tailTrace_3229850 : CollatzResearch.WordTrace tailWord_3229850 prefixEnd_3229850 1658465491924293430721197 := by
  unfold tailWord_3229850
  simp only [CollatzResearch.WordTrace]
  refine ⟨29450576837203134827209751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78534871565875026205892669 29450576837203134827209751)
  ·
    refine ⟨44175865255804702240814627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29450576837203134827209751 44175865255804702240814627)
    ·
      refine ⟨66263797883707053361221941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44175865255804702240814627 66263797883707053361221941)
      ·
        refine ⟨6212231051597536252614557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66263797883707053361221941 6212231051597536252614557)
        ·
          refine ⟨2329586644349076094730459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6212231051597536252614557 2329586644349076094730459)
          ·
            refine ⟨3494379966523614142095689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329586644349076094730459 3494379966523614142095689)
            ·
              refine ⟨2620784974892710606571767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3494379966523614142095689 2620784974892710606571767)
              ·
                refine ⟨3931177462339065909857651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620784974892710606571767 3931177462339065909857651)
                ·
                  refine ⟨5896766193508598864786477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931177462339065909857651 5896766193508598864786477)
                  ·
                    refine ⟨2211287322565724574294929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5896766193508598864786477 2211287322565724574294929)
                    ·
                      refine ⟨1658465491924293430721197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2211287322565724574294929 1658465491924293430721197)
                      ·
                        rfl

theorem cell23_3229850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_3229850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229850 prefixEnd_3229850 := by exact prefixLift 3229850
  have htrace : WordTrace (prefixWord ++ tailWord_3229850) baseStart_3229850 baseEnd_3229850 := by
    simpa [prefixWord, tailWord_3229850, baseEnd_3229850] using wordTrace_append hprefix tailTrace_3229850
  have hstable : (prefixWord ++ tailWord_3229850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229850).length < 2 ^ (prefixWord ++ tailWord_3229850).sum := by decide
  have hdescent : baseEnd_3229850 < baseStart_3229850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229869 : List Nat := [1, 5, 2, 1, 2, 1, 2, 4, 5]
def baseStart_3229869 : Nat := 118140960795 + 3229869 * 2 ^ 59
def prefixEnd_3229869 : Nat := 4983230072969 + 3 ^ 40 * 3229869 * 2
def baseEnd_3229869 : Nat := 184275027561858761820401

theorem tailTrace_3229869 : CollatzResearch.WordTrace tailWord_3229869 prefixEnd_3229869 184275027561858761820401 := by
  unfold tailWord_3229869
  simp only [CollatzResearch.WordTrace]
  refine ⟨117803000335743705553780661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78535333557162470369187107 117803000335743705553780661)
  ·
    refine ⟨11044031281475972395666937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117803000335743705553780661 11044031281475972395666937)
    ·
      refine ⟨8283023461106979296750203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11044031281475972395666937 8283023461106979296750203)
      ·
        refine ⟨12424535191660468945125305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8283023461106979296750203 12424535191660468945125305)
        ·
          refine ⟨9318401393745351708843979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12424535191660468945125305 9318401393745351708843979)
          ·
            refine ⟨13977602090618027563265969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9318401393745351708843979 13977602090618027563265969)
            ·
              refine ⟨10483201567963520672449477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13977602090618027563265969 10483201567963520672449477)
              ·
                refine ⟨1965600293993160126084277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10483201567963520672449477 1965600293993160126084277)
                ·
                  refine ⟨184275027561858761820401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1965600293993160126084277 184275027561858761820401)
                  ·
                    rfl

theorem cell23_3229869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_3229869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229869 prefixEnd_3229869 := by exact prefixLift 3229869
  have htrace : WordTrace (prefixWord ++ tailWord_3229869) baseStart_3229869 baseEnd_3229869 := by
    simpa [prefixWord, tailWord_3229869, baseEnd_3229869] using wordTrace_append hprefix tailTrace_3229869
  have hstable : (prefixWord ++ tailWord_3229869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229869).length < 2 ^ (prefixWord ++ tailWord_3229869).sum := by decide
  have hdescent : baseEnd_3229869 < baseStart_3229869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229902 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3229902 : Nat := 118140960795 + 3229902 * 2 ^ 59
def prefixEnd_3229902 : Nat := 4983230072969 + 3 ^ 40 * 3229902 * 2
def baseEnd_3229902 : Nat := 1658492192918327227270957

theorem tailTrace_3229902 : CollatzResearch.WordTrace tailWord_3229902 prefixEnd_3229902 1658492192918327227270957 := by
  unfold tailWord_3229902
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725525493078019023716495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78536135963082768126487973 14725525493078019023716495)
  ·
    refine ⟨22088288239617028535574743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14725525493078019023716495 22088288239617028535574743)
    ·
      refine ⟨33132432359425542803362115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22088288239617028535574743 33132432359425542803362115)
      ·
        refine ⟨49698648539138314205043173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33132432359425542803362115 49698648539138314205043173)
        ·
          refine ⟨9318496601088433913445595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49698648539138314205043173 9318496601088433913445595)
          ·
            refine ⟨13977744901632650870168393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9318496601088433913445595 13977744901632650870168393)
            ·
              refine ⟨10483308676224488152626295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13977744901632650870168393 10483308676224488152626295)
              ·
                refine ⟨15724963014336732228939443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10483308676224488152626295 15724963014336732228939443)
                ·
                  refine ⟨23587444521505098343409165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15724963014336732228939443 23587444521505098343409165)
                  ·
                    refine ⟨8845291695564411878778437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23587444521505098343409165 8845291695564411878778437)
                    ·
                      refine ⟨1658492192918327227270957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8845291695564411878778437 1658492192918327227270957)
                      ·
                        rfl

theorem cell23_3229902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3229902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229902 prefixEnd_3229902 := by exact prefixLift 3229902
  have htrace : WordTrace (prefixWord ++ tailWord_3229902) baseStart_3229902 baseEnd_3229902 := by
    simpa [prefixWord, tailWord_3229902, baseEnd_3229902] using wordTrace_append hprefix tailTrace_3229902
  have hstable : (prefixWord ++ tailWord_3229902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229902).length < 2 ^ (prefixWord ++ tailWord_3229902).sum := by decide
  have hdescent : baseEnd_3229902 < baseStart_3229902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229916 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3229916 : Nat := 118140960795 + 3229916 * 2 ^ 59
def prefixEnd_3229916 : Nat := 4983230072969 + 3 ^ 40 * 3229916 * 2
def baseEnd_3229916 : Nat := 552833127215830057498631

theorem tailTrace_3229916 : CollatzResearch.WordTrace tailWord_3229916 prefixEnd_3229916 552833127215830057498631 := by
  unfold tailWord_3229916
  simp only [CollatzResearch.WordTrace]
  refine ⟨58902357283286716290370801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78536476377715621720494401 58902357283286716290370801)
  ·
    refine ⟨44176767962465037217778101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58902357283286716290370801 44176767962465037217778101)
    ·
      refine ⟨4141571996481097239166697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44176767962465037217778101 4141571996481097239166697)
      ·
        refine ⟨3106178997360822929375023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4141571996481097239166697 3106178997360822929375023)
        ·
          refine ⟨4659268496041234394062535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106178997360822929375023 4659268496041234394062535)
          ·
            refine ⟨6988902744061851591093803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659268496041234394062535 6988902744061851591093803)
            ·
              refine ⟨10483354116092777386640705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6988902744061851591093803 10483354116092777386640705)
              ·
                refine ⟨7862515587069583039980529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10483354116092777386640705 7862515587069583039980529)
                ·
                  refine ⟨5896886690302187279985397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7862515587069583039980529 5896886690302187279985397)
                  ·
                    refine ⟨552833127215830057498631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5896886690302187279985397 552833127215830057498631)
                    ·
                      rfl

theorem cell23_3229916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3229916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229916 prefixEnd_3229916 := by exact prefixLift 3229916
  have htrace : WordTrace (prefixWord ++ tailWord_3229916) baseStart_3229916 baseEnd_3229916 := by
    simpa [prefixWord, tailWord_3229916, baseEnd_3229916] using wordTrace_append hprefix tailTrace_3229916
  have hstable : (prefixWord ++ tailWord_3229916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229916).length < 2 ^ (prefixWord ++ tailWord_3229916).sum := by decide
  have hdescent : baseEnd_3229916 < baseStart_3229916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229956 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3229956 : Nat := 118140960795 + 3229956 * 2 ^ 59
def prefixEnd_3229956 : Nat := 4983230072969 + 3 ^ 40 * 3229956 * 2
def baseEnd_3229956 : Nat := 1658519920873670015995709

theorem tailTrace_3229956 : CollatzResearch.WordTrace tailWord_3229956 prefixEnd_3229956 1658519920873670015995709 := by
  unfold tailWord_3229956
  simp only [CollatzResearch.WordTrace]
  refine ⟨58903086743214259706098861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78537448990952346274798481 58903086743214259706098861)
  ·
    refine ⟨22088657528705347389787073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58903086743214259706098861 22088657528705347389787073)
    ·
      refine ⟨16566493146529010542340305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22088657528705347389787073 16566493146529010542340305)
      ·
        refine ⟨12424869859896757906755229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16566493146529010542340305 12424869859896757906755229)
        ·
          refine ⟨4659326197461284215033211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12424869859896757906755229 4659326197461284215033211)
          ·
            refine ⟨6988989296191926322549817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659326197461284215033211 6988989296191926322549817)
            ·
              refine ⟨5241741972143944741912363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6988989296191926322549817 5241741972143944741912363)
              ·
                refine ⟨7862612958215917112868545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241741972143944741912363 7862612958215917112868545)
                ·
                  refine ⟨5896959718661937834651409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7862612958215917112868545 5896959718661937834651409)
                  ·
                    refine ⟨4422719788996453375988557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5896959718661937834651409 4422719788996453375988557)
                    ·
                      refine ⟨1658519920873670015995709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4422719788996453375988557 1658519920873670015995709)
                      ·
                        rfl

theorem cell23_3229956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3229956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229956 prefixEnd_3229956 := by exact prefixLift 3229956
  have htrace : WordTrace (prefixWord ++ tailWord_3229956) baseStart_3229956 baseEnd_3229956 := by
    simpa [prefixWord, tailWord_3229956, baseEnd_3229956] using wordTrace_append hprefix tailTrace_3229956
  have hstable : (prefixWord ++ tailWord_3229956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229956).length < 2 ^ (prefixWord ++ tailWord_3229956).sum := by decide
  have hdescent : baseEnd_3229956 < baseStart_3229956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3229979 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 2, 3, 2]
def baseStart_3229979 : Nat := 118140960795 + 3229979 * 2 ^ 59
def prefixEnd_3229979 : Nat := 4983230072969 + 3 ^ 40 * 3229979 * 2
def baseEnd_3229979 : Nat := 1658531730928723426008103

theorem tailTrace_3229979 : CollatzResearch.WordTrace tailWord_3229979 prefixEnd_3229979 1658531730928723426008103 := by
  unfold tailWord_3229979
  simp only [CollatzResearch.WordTrace]
  refine ⟨117807012365345194340284991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78538008243563462893523327 117807012365345194340284991)
  ·
    refine ⟨176710518548017791510427487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117807012365345194340284991 176710518548017791510427487)
    ·
      refine ⟨265065777822026687265641231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176710518548017791510427487 265065777822026687265641231)
      ·
        refine ⟨397598666733040030898461847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265065777822026687265641231 397598666733040030898461847)
        ·
          refine ⟨596398000099560046347692771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397598666733040030898461847 596398000099560046347692771)
          ·
            refine ⟨894597000149340069521539157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596398000099560046347692771 894597000149340069521539157)
            ·
              refine ⟨10483558595500078939705537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 894597000149340069521539157 10483558595500078939705537)
              ·
                refine ⟨7862668946625059204779153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10483558595500078939705537 7862668946625059204779153)
                ·
                  refine ⟨5897001709968794403584365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7862668946625059204779153 5897001709968794403584365)
                  ·
                    refine ⟨2211375641238297901344137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5897001709968794403584365 2211375641238297901344137)
                    ·
                      refine ⟨1658531730928723426008103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2211375641238297901344137 1658531730928723426008103)
                      ·
                        rfl

theorem cell23_3229979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 3, 2].length) (baseStart_3229979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3229979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3229979 prefixEnd_3229979 := by exact prefixLift 3229979
  have htrace : WordTrace (prefixWord ++ tailWord_3229979) baseStart_3229979 baseEnd_3229979 := by
    simpa [prefixWord, tailWord_3229979, baseEnd_3229979] using wordTrace_append hprefix tailTrace_3229979
  have hstable : (prefixWord ++ tailWord_3229979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3229979).length < 2 ^ (prefixWord ++ tailWord_3229979).sum := by decide
  have hdescent : baseEnd_3229979 < baseStart_3229979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3229979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230009 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3230009 : Nat := 118140960795 + 3230009 * 2 ^ 59
def prefixEnd_3230009 : Nat := 4983230072969 + 3 ^ 40 * 3230009 * 2
def baseEnd_3230009 : Nat := 1658547135348358308632965

theorem tailTrace_3230009 : CollatzResearch.WordTrace tailWord_3230009 prefixEnd_3230009 1658547135348358308632965 := by
  unfold tailWord_3230009
  simp only [CollatzResearch.WordTrace]
  refine ⟨117808106555236509463877081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78538737703491006309251387 117808106555236509463877081)
  ·
    refine ⟨88356079916427382097907811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117808106555236509463877081 88356079916427382097907811)
    ·
      refine ⟨132534119874641073146861717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88356079916427382097907811 132534119874641073146861717)
      ·
        refine ⟨6212536869123800303759143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132534119874641073146861717 6212536869123800303759143)
        ·
          refine ⟨9318805303685700455638715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6212536869123800303759143 9318805303685700455638715)
          ·
            refine ⟨13978207955528550683458073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9318805303685700455638715 13978207955528550683458073)
            ·
              refine ⟨10483655966646413012593555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13978207955528550683458073 10483655966646413012593555)
              ·
                refine ⟨15725483949969619518890333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10483655966646413012593555 15725483949969619518890333)
                ·
                  refine ⟨5897056481238607319583875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15725483949969619518890333 5897056481238607319583875)
                  ·
                    refine ⟨8845584721857910979375813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5897056481238607319583875 8845584721857910979375813)
                    ·
                      refine ⟨1658547135348358308632965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8845584721857910979375813 1658547135348358308632965)
                      ·
                        rfl

theorem cell23_3230009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3230009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230009 prefixEnd_3230009 := by exact prefixLift 3230009
  have htrace : WordTrace (prefixWord ++ tailWord_3230009) baseStart_3230009 baseEnd_3230009 := by
    simpa [prefixWord, tailWord_3230009, baseEnd_3230009] using wordTrace_append hprefix tailTrace_3230009
  have hstable : (prefixWord ++ tailWord_3230009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230009).length < 2 ^ (prefixWord ++ tailWord_3230009).sum := by decide
  have hdescent : baseEnd_3230009 < baseStart_3230009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230036 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_3230036 : Nat := 118140960795 + 3230036 * 2 ^ 59
def prefixEnd_3230036 : Nat := 4983230072969 + 3 ^ 40 * 3230036 * 2
def baseEnd_3230036 : Nat := 552853666442009900998447

theorem tailTrace_3230036 : CollatzResearch.WordTrace tailWord_3230036 prefixEnd_3230036 552853666442009900998447 := by
  unfold tailWord_3230036
  simp only [CollatzResearch.WordTrace]
  refine ⟨58904545663069346537554981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78539394217425795383406641 58904545663069346537554981)
  ·
    refine ⟨11044602311825502475791559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58904545663069346537554981 11044602311825502475791559)
    ·
      refine ⟨16566903467738253713687339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11044602311825502475791559 16566903467738253713687339)
      ·
        refine ⟨24850355201607380570531009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16566903467738253713687339 24850355201607380570531009)
        ·
          refine ⟨18637766401205535427898257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24850355201607380570531009 18637766401205535427898257)
          ·
            refine ⟨13978324800904151570923693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18637766401205535427898257 13978324800904151570923693)
            ·
              refine ⟨5241871800339056839096385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13978324800904151570923693 5241871800339056839096385)
              ·
                refine ⟨3931403850254292629322289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5241871800339056839096385 3931403850254292629322289)
                ·
                  refine ⟨2948552887690719471991717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3931403850254292629322289 2948552887690719471991717)
                  ·
                    refine ⟨552853666442009900998447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2948552887690719471991717 552853666442009900998447)
                    ·
                      rfl

theorem cell23_3230036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_3230036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230036 prefixEnd_3230036 := by exact prefixLift 3230036
  have htrace : WordTrace (prefixWord ++ tailWord_3230036) baseStart_3230036 baseEnd_3230036 := by
    simpa [prefixWord, tailWord_3230036, baseEnd_3230036] using wordTrace_append hprefix tailTrace_3230036
  have hstable : (prefixWord ++ tailWord_3230036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230036).length < 2 ^ (prefixWord ++ tailWord_3230036).sum := by decide
  have hdescent : baseEnd_3230036 < baseStart_3230036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230056 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_3230056 : Nat := 118140960795 + 3230056 * 2 ^ 59
def prefixEnd_3230056 : Nat := 4983230072969 + 3 ^ 40 * 3230056 * 2
def baseEnd_3230056 : Nat := 1658571268939119624745249

theorem tailTrace_3230056 : CollatzResearch.WordTrace tailWord_3230056 prefixEnd_3230056 1658571268939119624745249 := by
  unfold tailWord_3230056
  simp only [CollatzResearch.WordTrace]
  refine ⟨58904910393033118245419011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78539880524044157660558681 58904910393033118245419011)
  ·
    refine ⟨88357365589549677368128517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58904910393033118245419011 88357365589549677368128517)
    ·
      refine ⟨16567006048040564506524097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88357365589549677368128517 16567006048040564506524097)
      ·
        refine ⟨12425254536030423379893073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16567006048040564506524097 12425254536030423379893073)
        ·
          refine ⟨9318940902022817534919805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12425254536030423379893073 9318940902022817534919805)
          ·
            refine ⟨3494602838258556575594927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9318940902022817534919805 3494602838258556575594927)
            ·
              refine ⟨5241904257387834863392391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494602838258556575594927 5241904257387834863392391)
              ·
                refine ⟨7862856386081752295088587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241904257387834863392391 7862856386081752295088587)
                ·
                  refine ⟨11794284579122628442632881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7862856386081752295088587 11794284579122628442632881)
                  ·
                    refine ⟨8845713434341971331974661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11794284579122628442632881 8845713434341971331974661)
                    ·
                      refine ⟨1658571268939119624745249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8845713434341971331974661 1658571268939119624745249)
                      ·
                        rfl

theorem cell23_3230056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_3230056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230056 prefixEnd_3230056 := by exact prefixLift 3230056
  have htrace : WordTrace (prefixWord ++ tailWord_3230056) baseStart_3230056 baseEnd_3230056 := by
    simpa [prefixWord, tailWord_3230056, baseEnd_3230056] using wordTrace_append hprefix tailTrace_3230056
  have hstable : (prefixWord ++ tailWord_3230056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230056).length < 2 ^ (prefixWord ++ tailWord_3230056).sum := by decide
  have hdescent : baseEnd_3230056 < baseStart_3230056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230110 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3230110 : Nat := 118140960795 + 3230110 * 2 ^ 59
def prefixEnd_3230110 : Nat := 4983230072969 + 3 ^ 40 * 3230110 * 2
def baseEnd_3230110 : Nat := 1658598996894462413470001

theorem tailTrace_3230110 : CollatzResearch.WordTrace tailWord_3230110 prefixEnd_3230110 1658598996894462413470001 := by
  unfold tailWord_3230110
  simp only [CollatzResearch.WordTrace]
  refine ⟨14726473790983825464162973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78541193551913735808869189 14726473790983825464162973)
  ·
    refine ⟨5522427671618934549061115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14726473790983825464162973 5522427671618934549061115)
    ·
      refine ⟨8283641507428401823591673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5522427671618934549061115 8283641507428401823591673)
      ·
        refine ⟨6212731130571301367693755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8283641507428401823591673 6212731130571301367693755)
        ·
          refine ⟨9319096695856952051540633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6212731130571301367693755 9319096695856952051540633)
          ·
            refine ⟨6989322521892714038655475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9319096695856952051540633 6989322521892714038655475)
            ·
              refine ⟨10483983782839071057983213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6989322521892714038655475 10483983782839071057983213)
              ·
                refine ⟨3931493918564651646743705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10483983782839071057983213 3931493918564651646743705)
                ·
                  refine ⟨2948620438923488735057779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3931493918564651646743705 2948620438923488735057779)
                  ·
                    refine ⟨4422930658385233102586669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2948620438923488735057779 4422930658385233102586669)
                    ·
                      refine ⟨1658598996894462413470001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4422930658385233102586669 1658598996894462413470001)
                      ·
                        rfl

theorem cell23_3230110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3230110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230110 prefixEnd_3230110 := by exact prefixLift 3230110
  have htrace : WordTrace (prefixWord ++ tailWord_3230110) baseStart_3230110 baseEnd_3230110 := by
    simpa [prefixWord, tailWord_3230110, baseEnd_3230110] using wordTrace_append hprefix tailTrace_3230110
  have hstable : (prefixWord ++ tailWord_3230110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230110).length < 2 ^ (prefixWord ++ tailWord_3230110).sum := by decide
  have hdescent : baseEnd_3230110 < baseStart_3230110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230119 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3230119 : Nat := 118140960795 + 3230119 * 2 ^ 59
def prefixEnd_3230119 : Nat := 4983230072969 + 3 ^ 40 * 3230119 * 2
def baseEnd_3230119 : Nat := 1658603618220352878257459

theorem tailTrace_3230119 : CollatzResearch.WordTrace tailWord_3230119 prefixEnd_3230119 1658603618220352878257459 := by
  unfold tailWord_3230119
  simp only [CollatzResearch.WordTrace]
  refine ⟨117812118584837998250381411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78541412389891998833587607 117812118584837998250381411)
  ·
    refine ⟨176718177877256997375572117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117812118584837998250381411 176718177877256997375572117)
    ·
      refine ⟨8283664587996421751979943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 176718177877256997375572117 8283664587996421751979943)
      ·
        refine ⟨12425496881994632627969915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8283664587996421751979943 12425496881994632627969915)
        ·
          refine ⟨18638245322991948941954873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12425496881994632627969915 18638245322991948941954873)
          ·
            refine ⟨13978683992243961706466155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18638245322991948941954873 13978683992243961706466155)
            ·
              refine ⟨20968025988365942559699233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13978683992243961706466155 20968025988365942559699233)
              ·
                refine ⟨15726019491274456919774425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20968025988365942559699233 15726019491274456919774425)
                ·
                  refine ⟨11794514618455842689830819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15726019491274456919774425 11794514618455842689830819)
                  ·
                    refine ⟨17691771927683764034746229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11794514618455842689830819 17691771927683764034746229)
                    ·
                      refine ⟨1658603618220352878257459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17691771927683764034746229 1658603618220352878257459)
                      ·
                        rfl

theorem cell23_3230119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3230119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230119 prefixEnd_3230119 := by exact prefixLift 3230119
  have htrace : WordTrace (prefixWord ++ tailWord_3230119) baseStart_3230119 baseEnd_3230119 := by
    simpa [prefixWord, tailWord_3230119, baseEnd_3230119] using wordTrace_append hprefix tailTrace_3230119
  have hstable : (prefixWord ++ tailWord_3230119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230119).length < 2 ^ (prefixWord ++ tailWord_3230119).sum := by decide
  have hdescent : baseEnd_3230119 < baseStart_3230119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230120 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_3230120 : Nat := 118140960795 + 3230120 * 2 ^ 59
def prefixEnd_3230120 : Nat := 4983230072969 + 3 ^ 40 * 3230120 * 2
def baseEnd_3230120 : Nat := 1658604131701007374344955

theorem tailTrace_3230120 : CollatzResearch.WordTrace tailWord_3230120 prefixEnd_3230120 1658604131701007374344955 := by
  unfold tailWord_3230120
  simp only [CollatzResearch.WordTrace]
  refine ⟨58906077528917187710583907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78541436705222916947445209 58906077528917187710583907)
  ·
    refine ⟨88359116293375781565875861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58906077528917187710583907 88359116293375781565875861)
    ·
      refine ⟨4141833576251989760900431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88359116293375781565875861 4141833576251989760900431)
      ·
        refine ⟨6212750364377984641350647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4141833576251989760900431 6212750364377984641350647)
        ·
          refine ⟨9319125546566976962025971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6212750364377984641350647 9319125546566976962025971)
          ·
            refine ⟨13978688319850465443038957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9319125546566976962025971 13978688319850465443038957)
            ·
              refine ⟨5242008119943924541139609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13978688319850465443038957 5242008119943924541139609)
              ·
                refine ⟨3931506089957943405854707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5242008119943924541139609 3931506089957943405854707)
                ·
                  refine ⟨5897259134936915108782061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931506089957943405854707 5897259134936915108782061)
                  ·
                    refine ⟨2211472175601343165793273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5897259134936915108782061 2211472175601343165793273)
                    ·
                      refine ⟨1658604131701007374344955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2211472175601343165793273 1658604131701007374344955)
                      ·
                        rfl

theorem cell23_3230120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_3230120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230120 prefixEnd_3230120 := by exact prefixLift 3230120
  have htrace : WordTrace (prefixWord ++ tailWord_3230120) baseStart_3230120 baseEnd_3230120 := by
    simpa [prefixWord, tailWord_3230120, baseEnd_3230120] using wordTrace_append hprefix tailTrace_3230120
  have hstable : (prefixWord ++ tailWord_3230120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230120).length < 2 ^ (prefixWord ++ tailWord_3230120).sum := by decide
  have hdescent : baseEnd_3230120 < baseStart_3230120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230133 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_3230133 : Nat := 118140960795 + 3230133 * 2 ^ 59
def prefixEnd_3230133 : Nat := 4983230072969 + 3 ^ 40 * 3230133 * 2
def baseEnd_3230133 : Nat := 1658610806949515823482395

theorem tailTrace_3230133 : CollatzResearch.WordTrace tailWord_3230133 prefixEnd_3230133 1658610806949515823482395 := by
  unfold tailWord_3230133
  simp only [CollatzResearch.WordTrace]
  refine ⟨117812629206787278641391053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78541752804524852427594035 117812629206787278641391053)
  ·
    refine ⟨44179735952545229490521645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117812629206787278641391053 44179735952545229490521645)
    ·
      refine ⟨16567400982204461058945617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44179735952545229490521645 16567400982204461058945617)
      ·
        refine ⟨12425550736653345794209213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16567400982204461058945617 12425550736653345794209213)
        ·
          refine ⟨4659581526245004672828455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12425550736653345794209213 4659581526245004672828455)
          ·
            refine ⟨6989372289367507009242683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659581526245004672828455 6989372289367507009242683)
            ·
              refine ⟨10484058434051260513864025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6989372289367507009242683 10484058434051260513864025)
              ·
                refine ⟨7863043825538445385398019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10484058434051260513864025 7863043825538445385398019)
                ·
                  refine ⟨11794565738307668078097029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7863043825538445385398019 11794565738307668078097029)
                  ·
                    refine ⟨2211481075932687764643193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11794565738307668078097029 2211481075932687764643193)
                    ·
                      refine ⟨1658610806949515823482395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2211481075932687764643193 1658610806949515823482395)
                      ·
                        rfl

theorem cell23_3230133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_3230133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230133 prefixEnd_3230133 := by exact prefixLift 3230133
  have htrace : WordTrace (prefixWord ++ tailWord_3230133) baseStart_3230133 baseEnd_3230133 := by
    simpa [prefixWord, tailWord_3230133, baseEnd_3230133] using wordTrace_append hprefix tailTrace_3230133
  have hstable : (prefixWord ++ tailWord_3230133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230133).length < 2 ^ (prefixWord ++ tailWord_3230133).sum := by decide
  have hdescent : baseEnd_3230133 < baseStart_3230133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230186 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 2, 5]
def baseStart_3230186 : Nat := 118140960795 + 3230186 * 2 ^ 59
def prefixEnd_3230186 : Nat := 4983230072969 + 3 ^ 40 * 3230186 * 2
def baseEnd_3230186 : Nat := 552879340474734705373217

theorem tailTrace_3230186 : CollatzResearch.WordTrace tailWord_3230186 prefixEnd_3230186 552879340474734705373217 := by
  unfold tailWord_3230186
  simp only [CollatzResearch.WordTrace]
  refine ⟨29453640568898817173267603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78543041517063512462046941 29453640568898817173267603)
  ·
    refine ⟨44180460853348225759901405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29453640568898817173267603 44180460853348225759901405)
    ·
      refine ⟨16567672820005584659963027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44180460853348225759901405 16567672820005584659963027)
      ·
        refine ⟨24851509230008376989944541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16567672820005584659963027 24851509230008376989944541)
        ·
          refine ⟨9319315961253141371229203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24851509230008376989944541 9319315961253141371229203)
          ·
            refine ⟨13978973941879712056843805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9319315961253141371229203 13978973941879712056843805)
            ·
              refine ⟨5242115228204892021316427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13978973941879712056843805 5242115228204892021316427)
              ·
                refine ⟨7863172842307338031974641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5242115228204892021316427 7863172842307338031974641)
                ·
                  refine ⟨5897379631730503523980981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7863172842307338031974641 5897379631730503523980981)
                  ·
                    refine ⟨552879340474734705373217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5897379631730503523980981 552879340474734705373217)
                    ·
                      rfl

theorem cell23_3230186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_3230186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230186 prefixEnd_3230186 := by exact prefixLift 3230186
  have htrace : WordTrace (prefixWord ++ tailWord_3230186) baseStart_3230186 baseEnd_3230186 := by
    simpa [prefixWord, tailWord_3230186, baseEnd_3230186] using wordTrace_append hprefix tailTrace_3230186
  have hstable : (prefixWord ++ tailWord_3230186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230186).length < 2 ^ (prefixWord ++ tailWord_3230186).sum := by decide
  have hdescent : baseEnd_3230186 < baseStart_3230186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230239 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 3]
def baseStart_3230239 : Nat := 118140960795 + 3230239 * 2 ^ 59
def prefixEnd_3230239 : Nat := 4983230072969 + 3 ^ 40 * 3230239 * 2
def baseEnd_3230239 : Nat := 1658665235898892408756907

theorem tailTrace_3230239 : CollatzResearch.WordTrace tailWord_3230239 prefixEnd_3230239 1658665235898892408756907 := by
  unfold tailWord_3230239
  simp only [CollatzResearch.WordTrace]
  refine ⟨117816495344403258744749771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78544330229602172496499847 117816495344403258744749771)
  ·
    refine ⟨176724743016604888117124657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117816495344403258744749771 176724743016604888117124657)
    ·
      refine ⟨132543557262453666087843493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176724743016604888117124657 132543557262453666087843493)
      ·
        refine ⟨24851916986710062391470655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132543557262453666087843493 24851916986710062391470655)
        ·
          refine ⟨37277875480065093587205983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24851916986710062391470655 37277875480065093587205983)
          ·
            refine ⟨55916813220097640380808975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37277875480065093587205983 55916813220097640380808975)
            ·
              refine ⟨83875219830146460571213463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55916813220097640380808975 83875219830146460571213463)
              ·
                refine ⟨125812829745219690856820195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83875219830146460571213463 125812829745219690856820195)
                ·
                  refine ⟨188719244617829536285230293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125812829745219690856820195 188719244617829536285230293)
                  ·
                    refine ⟨4423107295730379756685085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 188719244617829536285230293 4423107295730379756685085)
                    ·
                      refine ⟨1658665235898892408756907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4423107295730379756685085 1658665235898892408756907)
                      ·
                        rfl

theorem cell23_3230239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_3230239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230239 prefixEnd_3230239 := by exact prefixLift 3230239
  have htrace : WordTrace (prefixWord ++ tailWord_3230239) baseStart_3230239 baseEnd_3230239 := by
    simpa [prefixWord, tailWord_3230239, baseEnd_3230239] using wordTrace_append hprefix tailTrace_3230239
  have hstable : (prefixWord ++ tailWord_3230239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230239).length < 2 ^ (prefixWord ++ tailWord_3230239).sum := by decide
  have hdescent : baseEnd_3230239 < baseStart_3230239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230250 : List Nat := [3, 1, 4, 1, 1, 2, 3, 3, 1, 4]
def baseStart_3230250 : Nat := 118140960795 + 3230250 * 2 ^ 59
def prefixEnd_3230250 : Nat := 4983230072969 + 3 ^ 40 * 3230250 * 2
def baseEnd_3230250 : Nat := 552890294728697288573119

theorem tailTrace_3230250 : CollatzResearch.WordTrace tailWord_3230250 prefixEnd_3230250 552890294728697288573119 := by
  unfold tailWord_3230250
  simp only [CollatzResearch.WordTrace]
  refine ⟨29454224136840851905850051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78544597698242271748933469 29454224136840851905850051)
  ·
    refine ⟨44181336205261277858775077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29454224136840851905850051 44181336205261277858775077)
    ·
      refine ⟨8284000538486489598520327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44181336205261277858775077 8284000538486489598520327)
      ·
        refine ⟨12426000807729734397780491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8284000538486489598520327 12426000807729734397780491)
        ·
          refine ⟨18639001211594601596670737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12426000807729734397780491 18639001211594601596670737)
          ·
            refine ⟨13979250908695951197503053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18639001211594601596670737 13979250908695951197503053)
            ·
              refine ⟨5242219090760981699063645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13979250908695951197503053 5242219090760981699063645)
              ·
                refine ⟨1965832159035368137148867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5242219090760981699063645 1965832159035368137148867)
                ·
                  refine ⟨2948748238553052205723301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1965832159035368137148867 2948748238553052205723301)
                  ·
                    refine ⟨552890294728697288573119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2948748238553052205723301 552890294728697288573119)
                    ·
                      rfl

theorem cell23_3230250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_3230250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230250 prefixEnd_3230250 := by exact prefixLift 3230250
  have htrace : WordTrace (prefixWord ++ tailWord_3230250) baseStart_3230250 baseEnd_3230250 := by
    simpa [prefixWord, tailWord_3230250, baseEnd_3230250] using wordTrace_append hprefix tailTrace_3230250
  have hstable : (prefixWord ++ tailWord_3230250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230250).length < 2 ^ (prefixWord ++ tailWord_3230250).sum := by decide
  have hdescent : baseEnd_3230250 < baseStart_3230250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230256 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 5, 1, 3]
def baseStart_3230256 : Nat := 118140960795 + 3230256 * 2 ^ 59
def prefixEnd_3230256 : Nat := 4983230072969 + 3 ^ 40 * 3230256 * 2
def baseEnd_3230256 : Nat := 1658673965070018842244329

theorem tailTrace_3230256 : CollatzResearch.WordTrace tailWord_3230256 prefixEnd_3230256 1658673965070018842244329 := by
  unfold tailWord_3230256
  simp only [CollatzResearch.WordTrace]
  refine ⟨58908557692670835324059311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78544743590227780432079081 58908557692670835324059311)
  ·
    refine ⟨88362836539006252986088967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58908557692670835324059311 88362836539006252986088967)
    ·
      refine ⟨132544254808509379479133451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88362836539006252986088967 132544254808509379479133451)
      ·
        refine ⟨198816382212764069218700177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132544254808509379479133451 198816382212764069218700177)
        ·
          refine ⟨149112286659573051914025133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198816382212764069218700177 149112286659573051914025133)
          ·
            refine ⟨55917107497339894467759425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149112286659573051914025133 55917107497339894467759425)
            ·
              refine ⟨41937830623004920850819569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55917107497339894467759425 41937830623004920850819569)
              ·
                refine ⟨31453372967253690638114677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41937830623004920850819569 31453372967253690638114677)
                ·
                  refine ⟨2948753715680033497323251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31453372967253690638114677 2948753715680033497323251)
                  ·
                    refine ⟨4423130573520050245984877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2948753715680033497323251 4423130573520050245984877)
                    ·
                      refine ⟨1658673965070018842244329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4423130573520050245984877 1658673965070018842244329)
                      ·
                        rfl

theorem cell23_3230256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5, 1, 3].length) (baseStart_3230256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230256 prefixEnd_3230256 := by exact prefixLift 3230256
  have htrace : WordTrace (prefixWord ++ tailWord_3230256) baseStart_3230256 baseEnd_3230256 := by
    simpa [prefixWord, tailWord_3230256, baseEnd_3230256] using wordTrace_append hprefix tailTrace_3230256
  have hstable : (prefixWord ++ tailWord_3230256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230256).length < 2 ^ (prefixWord ++ tailWord_3230256).sum := by decide
  have hdescent : baseEnd_3230256 < baseStart_3230256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230296 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 2, 6, 2]
def baseStart_3230296 : Nat := 118140960795 + 3230296 * 2 ^ 59
def prefixEnd_3230296 : Nat := 4983230072969 + 3 ^ 40 * 3230296 * 2
def baseEnd_3230296 : Nat := 1658694504296198685744145

theorem tailTrace_3230296 : CollatzResearch.WordTrace tailWord_3230296 prefixEnd_3230296 1658694504296198685744145 := by
  unfold tailWord_3230296
  simp only [CollatzResearch.WordTrace]
  refine ⟨58909287152598378739787371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78545716203464504986383161 58909287152598378739787371)
  ·
    refine ⟨88363930728897568109681057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58909287152598378739787371 88363930728897568109681057)
    ·
      refine ⟨66272948046673176082260793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88363930728897568109681057 66272948046673176082260793)
      ·
        refine ⟨49704711035004882061695595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66272948046673176082260793 49704711035004882061695595)
        ·
          refine ⟨74557066552507323092543393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49704711035004882061695595 74557066552507323092543393)
          ·
            refine ⟨55917799914380492319407545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74557066552507323092543393 55917799914380492319407545)
            ·
              refine ⟨41938349935785369239555659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55917799914380492319407545 41938349935785369239555659)
              ·
                refine ⟨62907524903678053859333489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41938349935785369239555659 62907524903678053859333489)
                ·
                  refine ⟨47180643677758540394500117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62907524903678053859333489 47180643677758540394500117)
                  ·
                    refine ⟨2211592672394931580992193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47180643677758540394500117 2211592672394931580992193)
                    ·
                      refine ⟨1658694504296198685744145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2211592672394931580992193 1658694504296198685744145)
                      ·
                        rfl

theorem cell23_3230296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_3230296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230296 prefixEnd_3230296 := by exact prefixLift 3230296
  have htrace : WordTrace (prefixWord ++ tailWord_3230296) baseStart_3230296 baseEnd_3230296 := by
    simpa [prefixWord, tailWord_3230296, baseEnd_3230296] using wordTrace_append hprefix tailTrace_3230296
  have hstable : (prefixWord ++ tailWord_3230296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230296).length < 2 ^ (prefixWord ++ tailWord_3230296).sum := by decide
  have hdescent : baseEnd_3230296 < baseStart_3230296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230316 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 5]
def baseStart_3230316 : Nat := 118140960795 + 3230316 * 2 ^ 59
def prefixEnd_3230316 : Nat := 4983230072969 + 3 ^ 40 * 3230316 * 2
def baseEnd_3230316 : Nat := 1658704773909288607494053

theorem tailTrace_3230316 : CollatzResearch.WordTrace tailWord_3230316 prefixEnd_3230316 1658704773909288607494053 := by
  unfold tailWord_3230316
  simp only [CollatzResearch.WordTrace]
  refine ⟨58909651882562150447651401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78546202510082867263535201 58909651882562150447651401)
  ·
    refine ⟨44182238911921612835738551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58909651882562150447651401 44182238911921612835738551)
    ·
      refine ⟨66273358367882419253607827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44182238911921612835738551 66273358367882419253607827)
      ·
        refine ⟨99410037551823628880411741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66273358367882419253607827 99410037551823628880411741)
        ·
          refine ⟨37278764081933860830154403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99410037551823628880411741 37278764081933860830154403)
          ·
            refine ⟨55918146122900791245231605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37278764081933860830154403 55918146122900791245231605)
            ·
              refine ⟨5242326199021949179240463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55918146122900791245231605 5242326199021949179240463)
              ·
                refine ⟨7863489298532923768860695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5242326199021949179240463 7863489298532923768860695)
                ·
                  refine ⟨11795233947799385653291043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7863489298532923768860695 11795233947799385653291043)
                  ·
                    refine ⟨17692850921699078479936565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11795233947799385653291043 17692850921699078479936565)
                    ·
                      refine ⟨1658704773909288607494053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17692850921699078479936565 1658704773909288607494053)
                      ·
                        rfl

theorem cell23_3230316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_3230316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230316 prefixEnd_3230316 := by exact prefixLift 3230316
  have htrace : WordTrace (prefixWord ++ tailWord_3230316) baseStart_3230316 baseEnd_3230316 := by
    simpa [prefixWord, tailWord_3230316, baseEnd_3230316] using wordTrace_append hprefix tailTrace_3230316
  have hstable : (prefixWord ++ tailWord_3230316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230316).length < 2 ^ (prefixWord ++ tailWord_3230316).sum := by decide
  have hdescent : baseEnd_3230316 < baseStart_3230316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230336 : List Nat := [2, 1, 1, 2, 1, 7, 1, 8]
def baseStart_3230336 : Nat := 118140960795 + 3230336 * 2 ^ 59
def prefixEnd_3230336 : Nat := 4983230072969 + 3 ^ 40 * 3230336 * 2
def baseEnd_3230336 : Nat := 61433890500828834416443

theorem tailTrace_3230336 : CollatzResearch.WordTrace tailWord_3230336 prefixEnd_3230336 61433890500828834416443 := by
  unfold tailWord_3230336
  simp only [CollatzResearch.WordTrace]
  refine ⟨58910016612525922155515431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78546688816701229540687241 58910016612525922155515431)
  ·
    refine ⟨88365024918788883233273147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58910016612525922155515431 88365024918788883233273147)
    ·
      refine ⟨132547537378183324849909721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88365024918788883233273147 132547537378183324849909721)
      ·
        refine ⟨99410653033637493637432291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132547537378183324849909721 99410653033637493637432291)
        ·
          refine ⟨149115979550456240456148437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99410653033637493637432291 149115979550456240456148437)
          ·
            refine ⟨3494905770713818135690979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 149115979550456240456148437 3494905770713818135690979)
            ·
              refine ⟨5242358656070727203536469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494905770713818135690979 5242358656070727203536469)
              ·
                refine ⟨61433890500828834416443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5242358656070727203536469 61433890500828834416443)
                ·
                  rfl

theorem cell23_3230336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 8].length) (baseStart_3230336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230336 prefixEnd_3230336 := by exact prefixLift 3230336
  have htrace : WordTrace (prefixWord ++ tailWord_3230336) baseStart_3230336 baseEnd_3230336 := by
    simpa [prefixWord, tailWord_3230336, baseEnd_3230336] using wordTrace_append hprefix tailTrace_3230336
  have hstable : (prefixWord ++ tailWord_3230336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230336).length < 2 ^ (prefixWord ++ tailWord_3230336).sum := by decide
  have hdescent : baseEnd_3230336 < baseStart_3230336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230339 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 6]
def baseStart_3230339 : Nat := 118140960795 + 3230339 * 2 ^ 59
def prefixEnd_3230339 : Nat := 4983230072969 + 3 ^ 40 * 3230339 * 2
def baseEnd_3230339 : Nat := 1658716583964342017506447

theorem tailTrace_3230339 : CollatzResearch.WordTrace tailWord_3230339 prefixEnd_3230339 1658716583964342017506447 := by
  unfold tailWord_3230339
  simp only [CollatzResearch.WordTrace]
  refine ⟨117820142644040975823390071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78546761762693983882260047 117820142644040975823390071)
  ·
    refine ⟨176730213966061463735085107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117820142644040975823390071 176730213966061463735085107)
    ·
      refine ⟨265095320949092195602627661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176730213966061463735085107 265095320949092195602627661)
      ·
        refine ⟨99410745355909573350985373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265095320949092195602627661 99410745355909573350985373)
        ·
          refine ⟨37279029508466090006619515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99410745355909573350985373 37279029508466090006619515)
          ·
            refine ⟨55918544262699135009929273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37279029508466090006619515 55918544262699135009929273)
            ·
              refine ⟨41938908197024351257446955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55918544262699135009929273 41938908197024351257446955)
              ·
                refine ⟨62908362295536526886170433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41938908197024351257446955 62908362295536526886170433)
                ·
                  refine ⟨47181271721652395164627825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62908362295536526886170433 47181271721652395164627825)
                  ·
                    refine ⟨35385953791239296373470869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47181271721652395164627825 35385953791239296373470869)
                    ·
                      refine ⟨1658716583964342017506447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35385953791239296373470869 1658716583964342017506447)
                      ·
                        rfl

theorem cell23_3230339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_3230339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230339 prefixEnd_3230339 := by exact prefixLift 3230339
  have htrace : WordTrace (prefixWord ++ tailWord_3230339) baseStart_3230339 baseEnd_3230339 := by
    simpa [prefixWord, tailWord_3230339, baseEnd_3230339] using wordTrace_append hprefix tailTrace_3230339
  have hstable : (prefixWord ++ tailWord_3230339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230339).length < 2 ^ (prefixWord ++ tailWord_3230339).sum := by decide
  have hdescent : baseEnd_3230339 < baseStart_3230339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230364 : List Nat := [2, 2, 3, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_3230364 : Nat := 118140960795 + 3230364 * 2 ^ 59
def prefixEnd_3230364 : Nat := 4983230072969 + 3 ^ 40 * 3230364 * 2
def baseEnd_3230364 : Nat := 1658729420980704419693833

theorem tailTrace_3230364 : CollatzResearch.WordTrace tailWord_3230364 prefixEnd_3230364 1658729420980704419693833 := by
  unfold tailWord_3230364
  simp only [CollatzResearch.WordTrace]
  refine ⟨58910527234475202546525073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78547369645966936728700097 58910527234475202546525073)
  ·
    refine ⟨44182895425856401909893805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58910527234475202546525073 44182895425856401909893805)
    ·
      refine ⟨16568585784696150716210177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44182895425856401909893805 16568585784696150716210177)
      ·
        refine ⟨12426439338522113037157633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16568585784696150716210177 12426439338522113037157633)
        ·
          refine ⟨9319829503891584777868225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12426439338522113037157633 9319829503891584777868225)
          ·
            refine ⟨6989872127918688583401169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9319829503891584777868225 6989872127918688583401169)
            ·
              refine ⟨5242404095939016437550877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6989872127918688583401169 5242404095939016437550877)
              ·
                refine ⟨1965901535977131164081579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5242404095939016437550877 1965901535977131164081579)
                ·
                  refine ⟨2948852303965696746122369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1965901535977131164081579 2948852303965696746122369)
                  ·
                    refine ⟨2211639227974272559591777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2948852303965696746122369 2211639227974272559591777)
                    ·
                      refine ⟨1658729420980704419693833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2211639227974272559591777 1658729420980704419693833)
                      ·
                        rfl

theorem cell23_3230364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_3230364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230364 prefixEnd_3230364 := by exact prefixLift 3230364
  have htrace : WordTrace (prefixWord ++ tailWord_3230364) baseStart_3230364 baseEnd_3230364 := by
    simpa [prefixWord, tailWord_3230364, baseEnd_3230364] using wordTrace_append hprefix tailTrace_3230364
  have hstable : (prefixWord ++ tailWord_3230364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230364).length < 2 ^ (prefixWord ++ tailWord_3230364).sum := by decide
  have hdescent : baseEnd_3230364 < baseStart_3230364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230396 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_3230396 : Nat := 118140960795 + 3230396 * 2 ^ 59
def prefixEnd_3230396 : Nat := 4983230072969 + 3 ^ 40 * 3230396 * 2
def baseEnd_3230396 : Nat := 552915284120549431497895

theorem tailTrace_3230396 : CollatzResearch.WordTrace tailWord_3230396 prefixEnd_3230396 552915284120549431497895 := by
  unfold tailWord_3230396
  simp only [CollatzResearch.WordTrace]
  refine ⟨58911110802417237279107521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78548147736556316372143361 58911110802417237279107521)
  ·
    refine ⟨44183333101812927959330641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58911110802417237279107521 44183333101812927959330641)
    ·
      refine ⟨33137499826359695969497981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44183333101812927959330641 33137499826359695969497981)
      ·
        refine ⟨12426562434884885988561743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33137499826359695969497981 12426562434884885988561743)
        ·
          refine ⟨18639843652327328982842615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12426562434884885988561743 18639843652327328982842615)
          ·
            refine ⟨27959765478490993474263923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18639843652327328982842615 27959765478490993474263923)
            ·
              refine ⟨41939648217736490211395885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27959765478490993474263923 41939648217736490211395885)
              ·
                refine ⟨15727368081651183829273457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41939648217736490211395885 15727368081651183829273457)
                ·
                  refine ⟨11795526061238387871955093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15727368081651183829273457 11795526061238387871955093)
                  ·
                    refine ⟨552915284120549431497895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11795526061238387871955093 552915284120549431497895)
                    ·
                      rfl

theorem cell23_3230396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_3230396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230396 prefixEnd_3230396 := by exact prefixLift 3230396
  have htrace : WordTrace (prefixWord ++ tailWord_3230396) baseStart_3230396 baseEnd_3230396 := by
    simpa [prefixWord, tailWord_3230396, baseEnd_3230396] using wordTrace_append hprefix tailTrace_3230396
  have hstable : (prefixWord ++ tailWord_3230396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230396).length < 2 ^ (prefixWord ++ tailWord_3230396).sum := by decide
  have hdescent : baseEnd_3230396 < baseStart_3230396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230397 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 2, 1, 3]
def baseStart_3230397 : Nat := 118140960795 + 3230397 * 2 ^ 59
def prefixEnd_3230397 : Nat := 4983230072969 + 3 ^ 40 * 3230397 * 2
def baseEnd_3230397 : Nat := 1658746365842302790581181

theorem tailTrace_3230397 : CollatzResearch.WordTrace tailWord_3230397 prefixEnd_3230397 1658746365842302790581181 := by
  unfold tailWord_3230397
  simp only [CollatzResearch.WordTrace]
  refine ⟨117822258077830851729001445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78548172051887234486000963 117822258077830851729001445)
  ·
    refine ⟨22091673389593284699187771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117822258077830851729001445 22091673389593284699187771)
    ·
      refine ⟨33137510084389927048781657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22091673389593284699187771 33137510084389927048781657)
      ·
        refine ⟨24853132563292445286586243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33137510084389927048781657 24853132563292445286586243)
        ·
          refine ⟨37279698844938667929879365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24853132563292445286586243 37279698844938667929879365)
          ·
            refine ⟨6989943533426000236852381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37279698844938667929879365 6989943533426000236852381)
            ·
              refine ⟨2621228825034750088819643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6989943533426000236852381 2621228825034750088819643)
              ·
                refine ⟨3931843237552125133229465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2621228825034750088819643 3931843237552125133229465)
                ·
                  refine ⟨2948882428164093849922099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3931843237552125133229465 2948882428164093849922099)
                  ·
                    refine ⟨4423323642246140774883149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2948882428164093849922099 4423323642246140774883149)
                    ·
                      refine ⟨1658746365842302790581181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4423323642246140774883149 1658746365842302790581181)
                      ·
                        rfl

theorem cell23_3230397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_3230397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230397 prefixEnd_3230397 := by exact prefixLift 3230397
  have htrace : WordTrace (prefixWord ++ tailWord_3230397) baseStart_3230397 baseEnd_3230397 := by
    simpa [prefixWord, tailWord_3230397, baseEnd_3230397] using wordTrace_append hprefix tailTrace_3230397
  have hstable : (prefixWord ++ tailWord_3230397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230397).length < 2 ^ (prefixWord ++ tailWord_3230397).sum := by decide
  have hdescent : baseEnd_3230397 < baseStart_3230397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230456 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 4, 5]
def baseStart_3230456 : Nat := 118140960795 + 3230456 * 2 ^ 59
def prefixEnd_3230456 : Nat := 4983230072969 + 3 ^ 40 * 3230456 * 2
def baseEnd_3230456 : Nat := 552925553733639353247803

theorem tailTrace_3230456 : CollatzResearch.WordTrace tailWord_3230456 prefixEnd_3230456 552925553733639353247803 := by
  unfold tailWord_3230456
  simp only [CollatzResearch.WordTrace]
  refine ⟨58912204992308552402699611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78549606656411403203599481 58912204992308552402699611)
  ·
    refine ⟨88368307488462828604049417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58912204992308552402699611 88368307488462828604049417)
    ·
      refine ⟨66276230616347121453037063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88368307488462828604049417 66276230616347121453037063)
      ·
        refine ⟨99414345924520682179555595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66276230616347121453037063 99414345924520682179555595)
        ·
          refine ⟨149121518886781023269333393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99414345924520682179555595 149121518886781023269333393)
          ·
            refine ⟨111841139165085767452000045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149121518886781023269333393 111841139165085767452000045)
            ·
              refine ⟨41940427186907162794500017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111841139165085767452000045 41940427186907162794500017)
              ·
                refine ⟨31455320390180372095875013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41940427186907162794500017 31455320390180372095875013)
                ·
                  refine ⟨5897872573158819767976565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31455320390180372095875013 5897872573158819767976565)
                  ·
                    refine ⟨552925553733639353247803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5897872573158819767976565 552925553733639353247803)
                    ·
                      rfl

theorem cell23_3230456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_3230456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230456 prefixEnd_3230456 := by exact prefixLift 3230456
  have htrace : WordTrace (prefixWord ++ tailWord_3230456) baseStart_3230456 baseEnd_3230456 := by
    simpa [prefixWord, tailWord_3230456, baseEnd_3230456] using wordTrace_append hprefix tailTrace_3230456
  have hstable : (prefixWord ++ tailWord_3230456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230456).length < 2 ^ (prefixWord ++ tailWord_3230456).sum := by decide
  have hdescent : baseEnd_3230456 < baseStart_3230456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230513 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 1, 4, 3]
def baseStart_3230513 : Nat := 118140960795 + 3230513 * 2 ^ 59
def prefixEnd_3230513 : Nat := 4983230072969 + 3 ^ 40 * 3230513 * 2
def baseEnd_3230513 : Nat := 1658805929598224336730647

theorem tailTrace_3230513 : CollatzResearch.WordTrace tailWord_3230513 prefixEnd_3230513 1658805929598224336730647 := by
  unfold tailWord_3230513
  simp only [CollatzResearch.WordTrace]
  refine ⟨117826488945410603540224193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78550992630273735693482795 117826488945410603540224193)
  ·
    refine ⟨88369866709057952655168145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117826488945410603540224193 88369866709057952655168145)
    ·
      refine ⟨66277400031793464491376109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88369866709057952655168145 66277400031793464491376109)
      ·
        refine ⟨24854025011922549184266041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66277400031793464491376109 24854025011922549184266041)
        ·
          refine ⟨18640518758941911888199531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24854025011922549184266041 18640518758941911888199531)
          ·
            refine ⟨27960778138412867832299297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18640518758941911888199531 27960778138412867832299297)
            ·
              refine ⟨20970583603809650874224473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27960778138412867832299297 20970583603809650874224473)
              ·
                refine ⟨15727937702857238155668355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20970583603809650874224473 15727937702857238155668355)
                ·
                  refine ⟨23591906554285857233502533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15727937702857238155668355 23591906554285857233502533)
                  ·
                    refine ⟨4423482478928598231281725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23591906554285857233502533 4423482478928598231281725)
                    ·
                      refine ⟨1658805929598224336730647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4423482478928598231281725 1658805929598224336730647)
                      ·
                        rfl

theorem cell23_3230513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_3230513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230513 prefixEnd_3230513 := by exact prefixLift 3230513
  have htrace : WordTrace (prefixWord ++ tailWord_3230513) baseStart_3230513 baseEnd_3230513 := by
    simpa [prefixWord, tailWord_3230513, baseEnd_3230513] using wordTrace_append hprefix tailTrace_3230513
  have hstable : (prefixWord ++ tailWord_3230513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230513).length < 2 ^ (prefixWord ++ tailWord_3230513).sum := by decide
  have hdescent : baseEnd_3230513 < baseStart_3230513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230537 : List Nat := [1, 2, 1, 1, 2, 6, 2, 3, 1, 4]
def baseStart_3230537 : Nat := 118140960795 + 3230537 * 2 ^ 59
def prefixEnd_3230537 : Nat := 4983230072969 + 3 ^ 40 * 3230537 * 2
def baseEnd_3230537 : Nat := 552939417711310747610179

theorem tailTrace_3230537 : CollatzResearch.WordTrace tailWord_3230537 prefixEnd_3230537 552939417711310747610179 := by
  unfold tailWord_3230537
  simp only [CollatzResearch.WordTrace]
  refine ⟨117827364297323655639097865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78551576198215770426065243 117827364297323655639097865)
  ·
    refine ⟨88370523222992741729323399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117827364297323655639097865 88370523222992741729323399)
    ·
      refine ⟨132555784834489112593985099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88370523222992741729323399 132555784834489112593985099)
      ·
        refine ⟨198833677251733668890977649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132555784834489112593985099 198833677251733668890977649)
        ·
          refine ⟨149125257938800251668233237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198833677251733668890977649 149125257938800251668233237)
          ·
            refine ⟨6990246465881261796948433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149125257938800251668233237 6990246465881261796948433)
            ·
              refine ⟨5242684849410946347711325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6990246465881261796948433 5242684849410946347711325)
              ·
                refine ⟨1966006818529104880391747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5242684849410946347711325 1966006818529104880391747)
                ·
                  refine ⟨2949010227793657320587621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966006818529104880391747 2949010227793657320587621)
                  ·
                    refine ⟨552939417711310747610179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2949010227793657320587621 552939417711310747610179)
                    ·
                      rfl

theorem cell23_3230537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 1, 4].length) (baseStart_3230537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230537 prefixEnd_3230537 := by exact prefixLift 3230537
  have htrace : WordTrace (prefixWord ++ tailWord_3230537) baseStart_3230537 baseEnd_3230537 := by
    simpa [prefixWord, tailWord_3230537, baseEnd_3230537] using wordTrace_append hprefix tailTrace_3230537
  have hstable : (prefixWord ++ tailWord_3230537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230537).length < 2 ^ (prefixWord ++ tailWord_3230537).sum := by decide
  have hdescent : baseEnd_3230537 < baseStart_3230537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230583 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_3230583 : Nat := 118140960795 + 3230583 * 2 ^ 59
def prefixEnd_3230583 : Nat := 4983230072969 + 3 ^ 40 * 3230583 * 2
def baseEnd_3230583 : Nat := 1658841873244039062855325

theorem tailTrace_3230583 : CollatzResearch.WordTrace tailWord_3230583 prefixEnd_3230583 1658841873244039062855325 := by
  unfold tailWord_3230583
  simp only [CollatzResearch.WordTrace]
  refine ⟨117829042055157005495272403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78552694703438003663514935 117829042055157005495272403)
  ·
    refine ⟨176743563082735508242908605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117829042055157005495272403 176743563082735508242908605)
    ·
      refine ⟨66278836156025815591090727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176743563082735508242908605 66278836156025815591090727)
      ·
        refine ⟨99418254234038723386636091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66278836156025815591090727 99418254234038723386636091)
        ·
          refine ⟨149127381351058085079954137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99418254234038723386636091 149127381351058085079954137)
          ·
            refine ⟨111845536013293563809965603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149127381351058085079954137 111845536013293563809965603)
            ·
              refine ⟨167768304019940345714948405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111845536013293563809965603 167768304019940345714948405)
              ·
                refine ⟨15728278501869407410776413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167768304019940345714948405 15728278501869407410776413)
                ·
                  refine ⟨5898104438201027779041155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15728278501869407410776413 5898104438201027779041155)
                  ·
                    refine ⟨8847156657301541668561733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5898104438201027779041155 8847156657301541668561733)
                    ·
                      refine ⟨1658841873244039062855325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8847156657301541668561733 1658841873244039062855325)
                      ·
                        rfl

theorem cell23_3230583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_3230583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230583 prefixEnd_3230583 := by exact prefixLift 3230583
  have htrace : WordTrace (prefixWord ++ tailWord_3230583) baseStart_3230583 baseEnd_3230583 := by
    simpa [prefixWord, tailWord_3230583, baseEnd_3230583] using wordTrace_append hprefix tailTrace_3230583
  have hstable : (prefixWord ++ tailWord_3230583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230583).length < 2 ^ (prefixWord ++ tailWord_3230583).sum := by decide
  have hdescent : baseEnd_3230583 < baseStart_3230583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230603 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 5]
def baseStart_3230603 : Nat := 118140960795 + 3230603 * 2 ^ 59
def prefixEnd_3230603 : Nat := 4983230072969 + 3 ^ 40 * 3230603 * 2
def baseEnd_3230603 : Nat := 1658852142857128984605233

theorem tailTrace_3230603 : CollatzResearch.WordTrace tailWord_3230603 prefixEnd_3230603 1658852142857128984605233 := by
  unfold tailWord_3230603
  simp only [CollatzResearch.WordTrace]
  refine ⟨117829771515084548911000463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78553181010056365940666975 117829771515084548911000463)
  ·
    refine ⟨176744657272626823366500695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117829771515084548911000463 176744657272626823366500695)
    ·
      refine ⟨265116985908940235049751043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176744657272626823366500695 265116985908940235049751043)
      ·
        refine ⟨397675478863410352574626565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265116985908940235049751043 397675478863410352574626565)
        ·
          refine ⟨74564152286889441107742481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397675478863410352574626565 74564152286889441107742481)
          ·
            refine ⟨55923114215167080830806861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74564152286889441107742481 55923114215167080830806861)
            ·
              refine ⟨20971167830687655311552573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55923114215167080830806861 20971167830687655311552573)
              ·
                refine ⟨7864187936507870741832215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20971167830687655311552573 7864187936507870741832215)
                ·
                  refine ⟨11796281904761806112748323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7864187936507870741832215 11796281904761806112748323)
                  ·
                    refine ⟨17694422857142709169122485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11796281904761806112748323 17694422857142709169122485)
                    ·
                      refine ⟨1658852142857128984605233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17694422857142709169122485 1658852142857128984605233)
                      ·
                        rfl

theorem cell23_3230603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 5].length) (baseStart_3230603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230603 prefixEnd_3230603 := by exact prefixLift 3230603
  have htrace : WordTrace (prefixWord ++ tailWord_3230603) baseStart_3230603 baseEnd_3230603 := by
    simpa [prefixWord, tailWord_3230603, baseEnd_3230603] using wordTrace_append hprefix tailTrace_3230603
  have hstable : (prefixWord ++ tailWord_3230603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230603).length < 2 ^ (prefixWord ++ tailWord_3230603).sum := by decide
  have hdescent : baseEnd_3230603 < baseStart_3230603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230613 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_3230613 : Nat := 118140960795 + 3230613 * 2 ^ 59
def prefixEnd_3230613 : Nat := 4983230072969 + 3 ^ 40 * 3230613 * 2
def baseEnd_3230613 : Nat := 1658857277663673945480187

theorem tailTrace_3230613 : CollatzResearch.WordTrace tailWord_3230613 prefixEnd_3230613 1658857277663673945480187 := by
  unfold tailWord_3230613
  simp only [CollatzResearch.WordTrace]
  refine ⟨117830136245048320618864493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78553424163365547079242995 117830136245048320618864493)
  ·
    refine ⟨44186301091893120232074185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117830136245048320618864493 44186301091893120232074185)
    ·
      refine ⟨33139725818919840174055639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44186301091893120232074185 33139725818919840174055639)
      ·
        refine ⟨49709588728379760261083459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33139725818919840174055639 49709588728379760261083459)
        ·
          refine ⟨74564383092569640391625189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49709588728379760261083459 74564383092569640391625189)
          ·
            refine ⟨13980821829856807573429723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74564383092569640391625189 13980821829856807573429723)
            ·
              refine ⟨20971232744785211360144585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13980821829856807573429723 20971232744785211360144585)
              ·
                refine ⟨15728424558588908520108439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20971232744785211360144585 15728424558588908520108439)
                ·
                  refine ⟨23592636837883362780162659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15728424558588908520108439 23592636837883362780162659)
                  ·
                    refine ⟨35388955256825044170243989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23592636837883362780162659 35388955256825044170243989)
                    ·
                      refine ⟨1658857277663673945480187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35388955256825044170243989 1658857277663673945480187)
                      ·
                        rfl

theorem cell23_3230613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_3230613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230613 prefixEnd_3230613 := by exact prefixLift 3230613
  have htrace : WordTrace (prefixWord ++ tailWord_3230613) baseStart_3230613 baseEnd_3230613 := by
    simpa [prefixWord, tailWord_3230613, baseEnd_3230613] using wordTrace_append hprefix tailTrace_3230613
  have hstable : (prefixWord ++ tailWord_3230613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230613).length < 2 ^ (prefixWord ++ tailWord_3230613).sum := by decide
  have hdescent : baseEnd_3230613 < baseStart_3230613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230623 : List Nat := [1, 1, 2, 5, 2, 1, 1, 10]
def baseStart_3230623 : Nat := 118140960795 + 3230623 * 2 ^ 59
def prefixEnd_3230623 : Nat := 4983230072969 + 3 ^ 40 * 3230623 * 2
def baseEnd_3230623 : Nat := 61439348610008107642783

theorem tailTrace_3230623 : CollatzResearch.WordTrace tailWord_3230623 prefixEnd_3230623 61439348610008107642783 := by
  unfold tailWord_3230623
  simp only [CollatzResearch.WordTrace]
  refine ⟨117830500975012092326728523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78553667316674728217819015 117830500975012092326728523)
  ·
    refine ⟨176745751462518138490092785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117830500975012092326728523 176745751462518138490092785)
    ·
      refine ⟨132559313596888603867569589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176745751462518138490092785 132559313596888603867569589)
      ·
        refine ⟨12427435649708306612584649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132559313596888603867569589 12427435649708306612584649)
        ·
          refine ⟨9320576737281229959438487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12427435649708306612584649 9320576737281229959438487)
          ·
            refine ⟨13980865105921844939157731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9320576737281229959438487 13980865105921844939157731)
            ·
              refine ⟨20971297658882767408736597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13980865105921844939157731 20971297658882767408736597)
              ·
                refine ⟨61439348610008107642783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20971297658882767408736597 61439348610008107642783)
                ·
                  rfl

theorem cell23_3230623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 10].length) (baseStart_3230623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230623 prefixEnd_3230623 := by exact prefixLift 3230623
  have htrace : WordTrace (prefixWord ++ tailWord_3230623) baseStart_3230623 baseEnd_3230623 := by
    simpa [prefixWord, tailWord_3230623, baseEnd_3230623] using wordTrace_append hprefix tailTrace_3230623
  have hstable : (prefixWord ++ tailWord_3230623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230623).length < 2 ^ (prefixWord ++ tailWord_3230623).sum := by decide
  have hdescent : baseEnd_3230623 < baseStart_3230623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230627 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 2, 4]
def baseStart_3230627 : Nat := 118140960795 + 3230627 * 2 ^ 59
def prefixEnd_3230627 : Nat := 4983230072969 + 3 ^ 40 * 3230627 * 2
def baseEnd_3230627 : Nat := 552954822130945630235041

theorem tailTrace_3230627 : CollatzResearch.WordTrace tailWord_3230627 prefixEnd_3230627 552954822130945630235041 := by
  unfold tailWord_3230627
  simp only [CollatzResearch.WordTrace]
  refine ⟨117830646866997601009874135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78553764577998400673249423 117830646866997601009874135)
  ·
    refine ⟨176745970300496401514811203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117830646866997601009874135 176745970300496401514811203)
    ·
      refine ⟨265118955450744602272216805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176745970300496401514811203 265118955450744602272216805)
      ·
        refine ⟨49709804147014612926040651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265118955450744602272216805 49709804147014612926040651)
        ·
          refine ⟨74564706220521919389060977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49709804147014612926040651 74564706220521919389060977)
          ·
            refine ⟨55923529665391439541795733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74564706220521919389060977 55923529665391439541795733)
            ·
              refine ⟨2621415453065223728521675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55923529665391439541795733 2621415453065223728521675)
              ·
                refine ⟨3932123179597835592782513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2621415453065223728521675 3932123179597835592782513)
                ·
                  refine ⟨2949092384698376694586885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3932123179597835592782513 2949092384698376694586885)
                  ·
                    refine ⟨552954822130945630235041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2949092384698376694586885 552954822130945630235041)
                    ·
                      rfl

theorem cell23_3230627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 2, 4].length) (baseStart_3230627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230627 prefixEnd_3230627 := by exact prefixLift 3230627
  have htrace : WordTrace (prefixWord ++ tailWord_3230627) baseStart_3230627 baseEnd_3230627 := by
    simpa [prefixWord, tailWord_3230627, baseEnd_3230627] using wordTrace_append hprefix tailTrace_3230627
  have hstable : (prefixWord ++ tailWord_3230627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230627).length < 2 ^ (prefixWord ++ tailWord_3230627).sum := by decide
  have hdescent : baseEnd_3230627 < baseStart_3230627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230650 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3]
def baseStart_3230650 : Nat := 118140960795 + 3230650 * 2 ^ 59
def prefixEnd_3230650 : Nat := 4983230072969 + 3 ^ 40 * 3230650 * 2
def baseEnd_3230650 : Nat := 1658876276447890300717517

theorem tailTrace_3230650 : CollatzResearch.WordTrace tailWord_3230650 prefixEnd_3230650 1658876276447890300717517 := by
  unfold tailWord_3230650
  simp only [CollatzResearch.WordTrace]
  refine ⟨29457871436478568984490351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78554323830609517291974269 29457871436478568984490351)
  ·
    refine ⟨44186807154717853476735527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29457871436478568984490351 44186807154717853476735527)
    ·
      refine ⟨66280210732076780215103291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44186807154717853476735527 66280210732076780215103291)
      ·
        refine ⟨99420316098115170322654937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66280210732076780215103291 99420316098115170322654937)
        ·
          refine ⟨74565237073586377741991203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99420316098115170322654937 74565237073586377741991203)
          ·
            refine ⟨111847855610379566612986805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74565237073586377741991203 111847855610379566612986805)
            ·
              refine ⟨10485736463473084369967513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111847855610379566612986805 10485736463473084369967513)
              ·
                refine ⟨7864302347604813277475635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10485736463473084369967513 7864302347604813277475635)
                ·
                  refine ⟨11796453521407219916213453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7864302347604813277475635 11796453521407219916213453)
                  ·
                    refine ⟨4423670070527707468580045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11796453521407219916213453 4423670070527707468580045)
                    ·
                      refine ⟨1658876276447890300717517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4423670070527707468580045 1658876276447890300717517)
                      ·
                        rfl

theorem cell23_3230650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_3230650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230650 prefixEnd_3230650 := by exact prefixLift 3230650
  have htrace : WordTrace (prefixWord ++ tailWord_3230650) baseStart_3230650 baseEnd_3230650 := by
    simpa [prefixWord, tailWord_3230650, baseEnd_3230650] using wordTrace_append hprefix tailTrace_3230650
  have hstable : (prefixWord ++ tailWord_3230650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230650).length < 2 ^ (prefixWord ++ tailWord_3230650).sum := by decide
  have hdescent : baseEnd_3230650 < baseStart_3230650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230654 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_3230654 : Nat := 118140960795 + 3230654 * 2 ^ 59
def prefixEnd_3230654 : Nat := 4983230072969 + 3 ^ 40 * 3230654 * 2
def baseEnd_3230654 : Nat := 1658878330370508285067499

theorem tailTrace_3230654 : CollatzResearch.WordTrace tailWord_3230654 prefixEnd_3230654 1658878330370508285067499 := by
  unfold tailWord_3230654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14728953954737473077638377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78554421091933189747404677 14728953954737473077638377)
  ·
    refine ⟨11046715466053104808228783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14728953954737473077638377 11046715466053104808228783)
    ·
      refine ⟨16570073199079657212343175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11046715466053104808228783 16570073199079657212343175)
      ·
        refine ⟨24855109798619485818514763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16570073199079657212343175 24855109798619485818514763)
        ·
          refine ⟨37282664697929228727772145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24855109798619485818514763 37282664697929228727772145)
          ·
            refine ⟨27961998523446921545829109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37282664697929228727772145 27961998523446921545829109)
            ·
              refine ⟨2621437361573148894921479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27961998523446921545829109 2621437361573148894921479)
              ·
                refine ⟨3932156042359723342382219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2621437361573148894921479 3932156042359723342382219)
                ·
                  refine ⟨5898234063539585013573329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3932156042359723342382219 5898234063539585013573329)
                  ·
                    refine ⟨4423675547654688760179997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5898234063539585013573329 4423675547654688760179997)
                    ·
                      refine ⟨1658878330370508285067499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4423675547654688760179997 1658878330370508285067499)
                      ·
                        rfl

theorem cell23_3230654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_3230654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230654 prefixEnd_3230654 := by exact prefixLift 3230654
  have htrace : WordTrace (prefixWord ++ tailWord_3230654) baseStart_3230654 baseEnd_3230654 := by
    simpa [prefixWord, tailWord_3230654, baseEnd_3230654] using wordTrace_append hprefix tailTrace_3230654
  have hstable : (prefixWord ++ tailWord_3230654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230654).length < 2 ^ (prefixWord ++ tailWord_3230654).sum := by decide
  have hdescent : baseEnd_3230654 < baseStart_3230654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230662 : List Nat := [6, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_3230662 : Nat := 118140960795 + 3230662 * 2 ^ 59
def prefixEnd_3230662 : Nat := 4983230072969 + 3 ^ 40 * 3230662 * 2
def baseEnd_3230662 : Nat := 1658882438215744253767463

theorem tailTrace_3230662 : CollatzResearch.WordTrace tailWord_3230662 prefixEnd_3230662 1658882438215744253767463 := by
  unfold tailWord_3230662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3682247606933462562106195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78554615614580534658265493 3682247606933462562106195)
  ·
    refine ⟨5523371410400193843159293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3682247606933462562106195 5523371410400193843159293)
    ·
      refine ⟨2071264278900072691184735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5523371410400193843159293 2071264278900072691184735)
      ·
        refine ⟨3106896418350109036777103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2071264278900072691184735 3106896418350109036777103)
        ·
          refine ⟨4660344627525163555165655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106896418350109036777103 4660344627525163555165655)
          ·
            refine ⟨6990516941287745332748483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660344627525163555165655 6990516941287745332748483)
            ·
              refine ⟨10485775411931617999122725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6990516941287745332748483 10485775411931617999122725)
              ·
                refine ⟨1966082889737178374835511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10485775411931617999122725 1966082889737178374835511)
                ·
                  refine ⟨2949124334605767562253267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966082889737178374835511 2949124334605767562253267)
                  ·
                    refine ⟨4423686501908651343379901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2949124334605767562253267 4423686501908651343379901)
                    ·
                      refine ⟨1658882438215744253767463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4423686501908651343379901 1658882438215744253767463)
                      ·
                        rfl

theorem cell23_3230662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_3230662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230662 prefixEnd_3230662 := by exact prefixLift 3230662
  have htrace : WordTrace (prefixWord ++ tailWord_3230662) baseStart_3230662 baseEnd_3230662 := by
    simpa [prefixWord, tailWord_3230662, baseEnd_3230662] using wordTrace_append hprefix tailTrace_3230662
  have hstable : (prefixWord ++ tailWord_3230662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230662).length < 2 ^ (prefixWord ++ tailWord_3230662).sum := by decide
  have hdescent : baseEnd_3230662 < baseStart_3230662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230663 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_3230663 : Nat := 118140960795 + 3230663 * 2 ^ 59
def prefixEnd_3230663 : Nat := 4983230072969 + 3 ^ 40 * 3230663 * 2
def baseEnd_3230663 : Nat := 1658882951696398749854957

theorem tailTrace_3230663 : CollatzResearch.WordTrace tailWord_3230663 prefixEnd_3230663 1658882951696398749854957 := by
  unfold tailWord_3230663
  simp only [CollatzResearch.WordTrace]
  refine ⟨117831959894867179158184643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78554639929911452772123095 117831959894867179158184643)
  ·
    refine ⟨176747939842300768737276965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117831959894867179158184643 176747939842300768737276965)
    ·
      refine ⟨33140238720431394138239431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176747939842300768737276965 33140238720431394138239431)
      ·
        refine ⟨49710358080647091207359147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33140238720431394138239431 49710358080647091207359147)
        ·
          refine ⟨74565537120970636811038721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49710358080647091207359147 74565537120970636811038721)
          ·
            refine ⟨55924152840727977608279041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74565537120970636811038721 55924152840727977608279041)
            ·
              refine ⟨41943114630545983206209281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55924152840727977608279041 41943114630545983206209281)
              ·
                refine ⟨31457335972909487404656961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41943114630545983206209281 31457335972909487404656961)
                ·
                  refine ⟨23593001979682115553492721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31457335972909487404656961 23593001979682115553492721)
                  ·
                    refine ⟨17694751484761586665119541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23593001979682115553492721 17694751484761586665119541)
                    ·
                      refine ⟨1658882951696398749854957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17694751484761586665119541 1658882951696398749854957)
                      ·
                        rfl

theorem cell23_3230663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_3230663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230663 prefixEnd_3230663 := by exact prefixLift 3230663
  have htrace : WordTrace (prefixWord ++ tailWord_3230663) baseStart_3230663 baseEnd_3230663 := by
    simpa [prefixWord, tailWord_3230663, baseEnd_3230663] using wordTrace_append hprefix tailTrace_3230663
  have hstable : (prefixWord ++ tailWord_3230663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230663).length < 2 ^ (prefixWord ++ tailWord_3230663).sum := by decide
  have hdescent : baseEnd_3230663 < baseStart_3230663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230667 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 2, 1, 3]
def baseStart_3230667 : Nat := 118140960795 + 3230667 * 2 ^ 59
def prefixEnd_3230667 : Nat := 4983230072969 + 3 ^ 40 * 3230667 * 2
def baseEnd_3230667 : Nat := 1658885005619016734204939

theorem tailTrace_3230667 : CollatzResearch.WordTrace tailWord_3230667 prefixEnd_3230667 1658885005619016734204939 := by
  unfold tailWord_3230667
  simp only [CollatzResearch.WordTrace]
  refine ⟨117832105786852687841330255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78554737191235125227553503 117832105786852687841330255)
  ·
    refine ⟨176748158680279031761995383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117832105786852687841330255 176748158680279031761995383)
    ·
      refine ⟨265122238020418547642993075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176748158680279031761995383 265122238020418547642993075)
      ·
        refine ⟨397683357030627821464489613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265122238020418547642993075 397683357030627821464489613)
        ·
          refine ⟨149131258886485433049183605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397683357030627821464489613 149131258886485433049183605)
          ·
            refine ⟨13981055520608009348360963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149131258886485433049183605 13981055520608009348360963)
            ·
              refine ⟨20971583280912014022541445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13981055520608009348360963 20971583280912014022541445)
              ·
                refine ⟨3932171865171002629226521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20971583280912014022541445 3932171865171002629226521)
                ·
                  refine ⟨2949128898878251971919891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3932171865171002629226521 2949128898878251971919891)
                  ·
                    refine ⟨4423693348317377957879837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2949128898878251971919891 4423693348317377957879837)
                    ·
                      refine ⟨1658885005619016734204939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4423693348317377957879837 1658885005619016734204939)
                      ·
                        rfl

theorem cell23_3230667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 1, 3].length) (baseStart_3230667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230667 prefixEnd_3230667 := by exact prefixLift 3230667
  have htrace : WordTrace (prefixWord ++ tailWord_3230667) baseStart_3230667 baseEnd_3230667 := by
    simpa [prefixWord, tailWord_3230667, baseEnd_3230667] using wordTrace_append hprefix tailTrace_3230667
  have hstable : (prefixWord ++ tailWord_3230667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230667).length < 2 ^ (prefixWord ++ tailWord_3230667).sum := by decide
  have hdescent : baseEnd_3230667 < baseStart_3230667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230673 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_3230673 : Nat := 118140960795 + 3230673 * 2 ^ 59
def prefixEnd_3230673 : Nat := 4983230072969 + 3 ^ 40 * 3230673 * 2
def baseEnd_3230673 : Nat := 1658888086502943710729911

theorem tailTrace_3230673 : CollatzResearch.WordTrace tailWord_3230673 prefixEnd_3230673 1658888086502943710729911 := by
  unfold tailWord_3230673
  simp only [CollatzResearch.WordTrace]
  refine ⟨117832324624830950866048673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78554883083220633910699115 117832324624830950866048673)
  ·
    refine ⟨88374243468623213149536505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117832324624830950866048673 88374243468623213149536505)
    ·
      refine ⟨66280682601467409862152379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88374243468623213149536505 66280682601467409862152379)
      ·
        refine ⟨99421023902201114793228569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66280682601467409862152379 99421023902201114793228569)
        ·
          refine ⟨74565767926650836094921427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99421023902201114793228569 74565767926650836094921427)
          ·
            refine ⟨111848651889976254142382141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74565767926650836094921427 111848651889976254142382141)
            ·
              refine ⟨41943244458741095303393303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111848651889976254142382141 41943244458741095303393303)
              ·
                refine ⟨62914866688111642955089955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41943244458741095303393303 62914866688111642955089955)
                ·
                  refine ⟨94372300032167464432634933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62914866688111642955089955 94372300032167464432634933)
                  ·
                    refine ⟨8847403128015699790559525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94372300032167464432634933 8847403128015699790559525)
                    ·
                      refine ⟨1658888086502943710729911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8847403128015699790559525 1658888086502943710729911)
                      ·
                        rfl

theorem cell23_3230673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_3230673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230673 prefixEnd_3230673 := by exact prefixLift 3230673
  have htrace : WordTrace (prefixWord ++ tailWord_3230673) baseStart_3230673 baseEnd_3230673 := by
    simpa [prefixWord, tailWord_3230673, baseEnd_3230673] using wordTrace_append hprefix tailTrace_3230673
  have hstable : (prefixWord ++ tailWord_3230673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230673).length < 2 ^ (prefixWord ++ tailWord_3230673).sum := by decide
  have hdescent : baseEnd_3230673 < baseStart_3230673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230713 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 9]
def baseStart_3230713 : Nat := 118140960795 + 3230713 * 2 ^ 59
def prefixEnd_3230713 : Nat := 4983230072969 + 3 ^ 40 * 3230713 * 2
def baseEnd_3230713 : Nat := 184323180636569283803303

theorem tailTrace_3230713 : CollatzResearch.WordTrace tailWord_3230713 prefixEnd_3230713 184323180636569283803303 := by
  unfold tailWord_3230713
  simp only [CollatzResearch.WordTrace]
  refine ⟨117833783544686037697504793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78555855696457358465003195 117833783544686037697504793)
  ·
    refine ⟨88375337658514528273128595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117833783544686037697504793 88375337658514528273128595)
    ·
      refine ⟨132563006487771792409692893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88375337658514528273128595 132563006487771792409692893)
      ·
        refine ⟨49711127432914422153634835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132563006487771792409692893 49711127432914422153634835)
        ·
          refine ⟨74566691149371633230452253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49711127432914422153634835 74566691149371633230452253)
          ·
            refine ⟨27962509181014362461419595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74566691149371633230452253 27962509181014362461419595)
            ·
              refine ⟨41943763771521543692129393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27962509181014362461419595 41943763771521543692129393)
              ·
                refine ⟨31457822828641157769097045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41943763771521543692129393 31457822828641157769097045)
                ·
                  refine ⟨184323180636569283803303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31457822828641157769097045 184323180636569283803303)
                  ·
                    rfl

theorem cell23_3230713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 9].length) (baseStart_3230713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230713 prefixEnd_3230713 := by exact prefixLift 3230713
  have htrace : WordTrace (prefixWord ++ tailWord_3230713) baseStart_3230713 baseEnd_3230713 := by
    simpa [prefixWord, tailWord_3230713, baseEnd_3230713] using wordTrace_append hprefix tailTrace_3230713
  have hstable : (prefixWord ++ tailWord_3230713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230713).length < 2 ^ (prefixWord ++ tailWord_3230713).sum := by decide
  have hdescent : baseEnd_3230713 < baseStart_3230713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230718 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3230718 : Nat := 118140960795 + 3230718 * 2 ^ 59
def prefixEnd_3230718 : Nat := 4983230072969 + 3 ^ 40 * 3230718 * 2
def baseEnd_3230718 : Nat := 1658911193132396034667205

theorem tailTrace_3230718 : CollatzResearch.WordTrace tailWord_3230718 prefixEnd_3230718 1658911193132396034667205 := by
  unfold tailWord_3230718
  simp only [CollatzResearch.WordTrace]
  refine ⟨14729245738708490443929601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78555977273111949034291205 14729245738708490443929601)
  ·
    refine ⟨11046934304031367832947201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14729245738708490443929601 11046934304031367832947201)
    ·
      refine ⟨8285200728023525874710401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11046934304031367832947201 8285200728023525874710401)
      ·
        refine ⟨6213900546017644406032801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8285200728023525874710401 6213900546017644406032801)
        ·
          refine ⟨4660425409513233304524601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6213900546017644406032801 4660425409513233304524601)
          ·
            refine ⟨3495319057134924978393451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4660425409513233304524601 3495319057134924978393451)
            ·
              refine ⟨5242978585702387467590177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495319057134924978393451 5242978585702387467590177)
              ·
                refine ⟨3932233939276790600692633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5242978585702387467590177 3932233939276790600692633)
                ·
                  refine ⟨2949175454457592950519475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3932233939276790600692633 2949175454457592950519475)
                  ·
                    refine ⟨4423763181686389425779213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2949175454457592950519475 4423763181686389425779213)
                    ·
                      refine ⟨1658911193132396034667205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4423763181686389425779213 1658911193132396034667205)
                      ·
                        rfl

theorem cell23_3230718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3230718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230718 prefixEnd_3230718 := by exact prefixLift 3230718
  have htrace : WordTrace (prefixWord ++ tailWord_3230718) baseStart_3230718 baseEnd_3230718 := by
    simpa [prefixWord, tailWord_3230718, baseEnd_3230718] using wordTrace_append hprefix tailTrace_3230718
  have hstable : (prefixWord ++ tailWord_3230718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230718).length < 2 ^ (prefixWord ++ tailWord_3230718).sum := by decide
  have hdescent : baseEnd_3230718 < baseStart_3230718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230730 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 7]
def baseStart_3230730 : Nat := 118140960795 + 3230730 * 2 ^ 59
def prefixEnd_3230730 : Nat := 4983230072969 + 3 ^ 40 * 3230730 * 2
def baseEnd_3230730 : Nat := 184324150544472220857461

theorem tailTrace_3230730 : CollatzResearch.WordTrace tailWord_3230730 prefixEnd_3230730 184324150544472220857461 := by
  unfold tailWord_3230730
  simp only [CollatzResearch.WordTrace]
  refine ⟨29458600896406112400218411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78556269057082966400582429 29458600896406112400218411)
  ·
    refine ⟨44187901344609168600327617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29458600896406112400218411 44187901344609168600327617)
    ·
      refine ⟨33140926008456876450245713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44187901344609168600327617 33140926008456876450245713)
      ·
        refine ⟨24855694506342657337684285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33140926008456876450245713 24855694506342657337684285)
        ·
          refine ⟨9320885439878496501631607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24855694506342657337684285 9320885439878496501631607)
          ·
            refine ⟨13981328159817744752447411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9320885439878496501631607 13981328159817744752447411)
            ·
              refine ⟨20971992239726617128671117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13981328159817744752447411 20971992239726617128671117)
              ·
                refine ⟨7864497089897481423251669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20971992239726617128671117 7864497089897481423251669)
                ·
                  refine ⟨184324150544472220857461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7864497089897481423251669 184324150544472220857461)
                  ·
                    rfl

theorem cell23_3230730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_3230730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230730 prefixEnd_3230730 := by exact prefixLift 3230730
  have htrace : WordTrace (prefixWord ++ tailWord_3230730) baseStart_3230730 baseEnd_3230730 := by
    simpa [prefixWord, tailWord_3230730, baseEnd_3230730] using wordTrace_append hprefix tailTrace_3230730
  have hstable : (prefixWord ++ tailWord_3230730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230730).length < 2 ^ (prefixWord ++ tailWord_3230730).sum := by decide
  have hdescent : baseEnd_3230730 < baseStart_3230730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230770 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_3230770 : Nat := 118140960795 + 3230770 * 2 ^ 59
def prefixEnd_3230770 : Nat := 4983230072969 + 3 ^ 40 * 3230770 * 2
def baseEnd_3230770 : Nat := 1658937894126429831216965

theorem tailTrace_3230770 : CollatzResearch.WordTrace tailWord_3230770 prefixEnd_3230770 1658937894126429831216965 := by
  unfold tailWord_3230770
  simp only [CollatzResearch.WordTrace]
  refine ⟨29458965626369884108082441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78557241670319690954886509 29458965626369884108082441)
  ·
    refine ⟨22094224219777413081061831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29458965626369884108082441 22094224219777413081061831)
    ·
      refine ⟨33141336329666119621592747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22094224219777413081061831 33141336329666119621592747)
      ·
        refine ⟨49712004494499179432389121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33141336329666119621592747 49712004494499179432389121)
        ·
          refine ⟨37284003370874384574291841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49712004494499179432389121 37284003370874384574291841)
          ·
            refine ⟨27963002528155788430718881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37284003370874384574291841 27963002528155788430718881)
            ·
              refine ⟨20972251896116841323039161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27963002528155788430718881 20972251896116841323039161)
              ·
                refine ⟨15729188922087630992279371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20972251896116841323039161 15729188922087630992279371)
                ·
                  refine ⟨23593783383131446488419057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15729188922087630992279371 23593783383131446488419057)
                  ·
                    refine ⟨17695337537348584866314293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23593783383131446488419057 17695337537348584866314293)
                    ·
                      refine ⟨1658937894126429831216965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17695337537348584866314293 1658937894126429831216965)
                      ·
                        rfl

theorem cell23_3230770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_3230770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230770 prefixEnd_3230770 := by exact prefixLift 3230770
  have htrace : WordTrace (prefixWord ++ tailWord_3230770) baseStart_3230770 baseEnd_3230770 := by
    simpa [prefixWord, tailWord_3230770, baseEnd_3230770] using wordTrace_append hprefix tailTrace_3230770
  have hstable : (prefixWord ++ tailWord_3230770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230770).length < 2 ^ (prefixWord ++ tailWord_3230770).sum := by decide
  have hdescent : baseEnd_3230770 < baseStart_3230770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230777 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 2, 5]
def baseStart_3230777 : Nat := 118140960795 + 3230777 * 2 ^ 59
def prefixEnd_3230777 : Nat := 4983230072969 + 3 ^ 40 * 3230777 * 2
def baseEnd_3230777 : Nat := 552980496163670434609811

theorem tailTrace_3230777 : CollatzResearch.WordTrace tailWord_3230777 prefixEnd_3230777 552980496163670434609811 := by
  unfold tailWord_3230777
  simp only [CollatzResearch.WordTrace]
  refine ⟨117836117816454176627834585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78557411877636117751889723 117836117816454176627834585)
  ·
    refine ⟨88377088362340632470875939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117836117816454176627834585 88377088362340632470875939)
    ·
      refine ⟨132565632543510948706313909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88377088362340632470875939 132565632543510948706313909)
      ·
        refine ⟨12428028050954151441216929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132565632543510948706313909 12428028050954151441216929)
        ·
          refine ⟨9321021038215613580912697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12428028050954151441216929 9321021038215613580912697)
          ·
            refine ⟨6990765778661710185684523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9321021038215613580912697 6990765778661710185684523)
            ·
              refine ⟨10486148667992565278526785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6990765778661710185684523 10486148667992565278526785)
              ·
                refine ⟨7864611500994423958895089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10486148667992565278526785 7864611500994423958895089)
                ·
                  refine ⟨5898458625745817969171317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7864611500994423958895089 5898458625745817969171317)
                  ·
                    refine ⟨552980496163670434609811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5898458625745817969171317 552980496163670434609811)
                    ·
                      rfl

theorem cell23_3230777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_3230777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230777 prefixEnd_3230777 := by exact prefixLift 3230777
  have htrace : WordTrace (prefixWord ++ tailWord_3230777) baseStart_3230777 baseEnd_3230777 := by
    simpa [prefixWord, tailWord_3230777, baseEnd_3230777] using wordTrace_append hprefix tailTrace_3230777
  have hstable : (prefixWord ++ tailWord_3230777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230777).length < 2 ^ (prefixWord ++ tailWord_3230777).sum := by decide
  have hdescent : baseEnd_3230777 < baseStart_3230777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230800 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 3]
def baseStart_3230800 : Nat := 118140960795 + 3230800 * 2 ^ 59
def prefixEnd_3230800 : Nat := 4983230072969 + 3 ^ 40 * 3230800 * 2
def baseEnd_3230800 : Nat := 1658953298546064713841827

theorem tailTrace_3230800 : CollatzResearch.WordTrace tailWord_3230800 prefixEnd_3230800 1658953298546064713841827 := by
  unfold tailWord_3230800
  simp only [CollatzResearch.WordTrace]
  refine ⟨58918478347685425777960927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78557971130247234370614569 58918478347685425777960927)
  ·
    refine ⟨88377717521528138666941391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58918478347685425777960927 88377717521528138666941391)
    ·
      refine ⟨132566576282292208000412087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88377717521528138666941391 132566576282292208000412087)
      ·
        refine ⟨198849864423438312000618131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132566576282292208000412087 198849864423438312000618131)
        ·
          refine ⟨298274796635157468000927197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198849864423438312000618131 298274796635157468000927197)
          ·
            refine ⟨111853048738184050500347699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298274796635157468000927197 111853048738184050500347699)
            ·
              refine ⟨167779573107276075750521549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111853048738184050500347699 167779573107276075750521549)
              ·
                refine ⟨62917339915228528406445581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167779573107276075750521549 62917339915228528406445581)
                ·
                  refine ⟨23594002468210698152417093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62917339915228528406445581 23594002468210698152417093)
                  ·
                    refine ⟨4423875462789505903578205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23594002468210698152417093 4423875462789505903578205)
                    ·
                      refine ⟨1658953298546064713841827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4423875462789505903578205 1658953298546064713841827)
                      ·
                        rfl

theorem cell23_3230800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 3].length) (baseStart_3230800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230800 prefixEnd_3230800 := by exact prefixLift 3230800
  have htrace : WordTrace (prefixWord ++ tailWord_3230800) baseStart_3230800 baseEnd_3230800 := by
    simpa [prefixWord, tailWord_3230800, baseEnd_3230800] using wordTrace_append hprefix tailTrace_3230800
  have hstable : (prefixWord ++ tailWord_3230800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230800).length < 2 ^ (prefixWord ++ tailWord_3230800).sum := by decide
  have hdescent : baseEnd_3230800 < baseStart_3230800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230817 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_3230817 : Nat := 118140960795 + 3230817 * 2 ^ 59
def prefixEnd_3230817 : Nat := 4983230072969 + 3 ^ 40 * 3230817 * 2
def baseEnd_3230817 : Nat := 1658962027717191147329249

theorem tailTrace_3230817 : CollatzResearch.WordTrace tailWord_3230817 prefixEnd_3230817 1658962027717191147329249 := by
  unfold tailWord_3230817
  simp only [CollatzResearch.WordTrace]
  refine ⟨117837576736309263459290705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78558384490872842306193803 117837576736309263459290705)
  ·
    refine ⟨88378182552231947594468029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117837576736309263459290705 88378182552231947594468029)
    ·
      refine ⟨33141818457086980347925511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88378182552231947594468029 33141818457086980347925511)
      ·
        refine ⟨49712727685630470521888267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33141818457086980347925511 49712727685630470521888267)
        ·
          refine ⟨74569091528445705782832401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49712727685630470521888267 74569091528445705782832401)
          ·
            refine ⟨55926818646334279337124301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74569091528445705782832401 55926818646334279337124301)
            ·
              refine ⟨20972556992375354751421613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55926818646334279337124301 20972556992375354751421613)
              ·
                refine ⟨7864708872140758031783105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20972556992375354751421613 7864708872140758031783105)
                ·
                  refine ⟨5898531654105568523837329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7864708872140758031783105 5898531654105568523837329)
                  ·
                    refine ⟨4423898740579176392877997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5898531654105568523837329 4423898740579176392877997)
                    ·
                      refine ⟨1658962027717191147329249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4423898740579176392877997 1658962027717191147329249)
                      ·
                        rfl

theorem cell23_3230817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_3230817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230817 prefixEnd_3230817 := by exact prefixLift 3230817
  have htrace : WordTrace (prefixWord ++ tailWord_3230817) baseStart_3230817 baseEnd_3230817 := by
    simpa [prefixWord, tailWord_3230817, baseEnd_3230817] using wordTrace_append hprefix tailTrace_3230817
  have hstable : (prefixWord ++ tailWord_3230817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230817).length < 2 ^ (prefixWord ++ tailWord_3230817).sum := by decide
  have hdescent : baseEnd_3230817 < baseStart_3230817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230841 : List Nat := [1, 2, 1, 3, 5, 1, 1, 4, 1, 4]
def baseStart_3230841 : Nat := 118140960795 + 3230841 * 2 ^ 59
def prefixEnd_3230841 : Nat := 4983230072969 + 3 ^ 40 * 3230841 * 2
def baseEnd_3230841 : Nat := 552991450417633017809713

theorem tailTrace_3230841 : CollatzResearch.WordTrace tailWord_3230841 prefixEnd_3230841 552991450417633017809713 := by
  unfold tailWord_3230841
  simp only [CollatzResearch.WordTrace]
  refine ⟨117838452088222315558164377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78558968058814877038776251 117838452088222315558164377)
  ·
    refine ⟨88378839066166736668623283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117838452088222315558164377 88378839066166736668623283)
    ·
      refine ⟨132568258599250105002934925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88378839066166736668623283 132568258599250105002934925)
      ·
        refine ⟨49713096974718789376100597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132568258599250105002934925 49713096974718789376100597)
        ·
          refine ⟨4660602841379886504009431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49713096974718789376100597 4660602841379886504009431)
          ·
            refine ⟨6990904262069829756014147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660602841379886504009431 6990904262069829756014147)
            ·
              refine ⟨10486356393104744634021221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6990904262069829756014147 10486356393104744634021221)
              ·
                refine ⟨1966191823707139618878979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10486356393104744634021221 1966191823707139618878979)
                ·
                  refine ⟨2949287735560709428318469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966191823707139618878979 2949287735560709428318469)
                  ·
                    refine ⟨552991450417633017809713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2949287735560709428318469 552991450417633017809713)
                    ·
                      rfl

theorem cell23_3230841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 1, 4].length) (baseStart_3230841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230841 prefixEnd_3230841 := by exact prefixLift 3230841
  have htrace : WordTrace (prefixWord ++ tailWord_3230841) baseStart_3230841 baseEnd_3230841 := by
    simpa [prefixWord, tailWord_3230841, baseEnd_3230841] using wordTrace_append hprefix tailTrace_3230841
  have hstable : (prefixWord ++ tailWord_3230841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230841).length < 2 ^ (prefixWord ++ tailWord_3230841).sum := by decide
  have hdescent : baseEnd_3230841 < baseStart_3230841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230847 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 9, 1, 3]
def baseStart_3230847 : Nat := 118140960795 + 3230847 * 2 ^ 59
def prefixEnd_3230847 : Nat := 4983230072969 + 3 ^ 40 * 3230847 * 2
def baseEnd_3230847 : Nat := 1658977432136826029954111

theorem tailTrace_3230847 : CollatzResearch.WordTrace tailWord_3230847 prefixEnd_3230847 1658977432136826029954111 := by
  unfold tailWord_3230847
  simp only [CollatzResearch.WordTrace]
  refine ⟨117838670926200578582882795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78559113950800385721921863 117838670926200578582882795)
  ·
    refine ⟨176758006389300867874324193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117838670926200578582882795 176758006389300867874324193)
    ·
      refine ⟨132568504791975650905743145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176758006389300867874324193 132568504791975650905743145)
      ·
        refine ⟨99426378593981738179307359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132568504791975650905743145 99426378593981738179307359)
        ·
          refine ⟨149139567890972607268961039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99426378593981738179307359 149139567890972607268961039)
          ·
            refine ⟨223709351836458910903441559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149139567890972607268961039 223709351836458910903441559)
            ·
              refine ⟨335564027754688366355162339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223709351836458910903441559 335564027754688366355162339)
              ·
                refine ⟨503346041632032549532743509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335564027754688366355162339 503346041632032549532743509)
                ·
                  refine ⟨2949293212687690719918419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 503346041632032549532743509 2949293212687690719918419)
                  ·
                    refine ⟨4423939819031536079877629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2949293212687690719918419 4423939819031536079877629)
                    ·
                      refine ⟨1658977432136826029954111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4423939819031536079877629 1658977432136826029954111)
                      ·
                        rfl

theorem cell23_3230847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_3230847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230847 prefixEnd_3230847 := by exact prefixLift 3230847
  have htrace : WordTrace (prefixWord ++ tailWord_3230847) baseStart_3230847 baseEnd_3230847 := by
    simpa [prefixWord, tailWord_3230847, baseEnd_3230847] using wordTrace_append hprefix tailTrace_3230847
  have hstable : (prefixWord ++ tailWord_3230847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230847).length < 2 ^ (prefixWord ++ tailWord_3230847).sum := by decide
  have hdescent : baseEnd_3230847 < baseStart_3230847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230884 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_3230884 : Nat := 118140960795 + 3230884 * 2 ^ 59
def prefixEnd_3230884 : Nat := 4983230072969 + 3 ^ 40 * 3230884 * 2
def baseEnd_3230884 : Nat := 552998810307014128397147

theorem tailTrace_3230884 : CollatzResearch.WordTrace tailWord_3230884 prefixEnd_3230884 552998810307014128397147 := by
  unfold tailWord_3230884
  simp only [CollatzResearch.WordTrace]
  refine ⟨58920010213533266950989853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78560013618044355934653137 58920010213533266950989853)
  ·
    refine ⟨22095003830074975106621195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58920010213533266950989853 22095003830074975106621195)
    ·
      refine ⟨33142505745112462659931793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22095003830074975106621195 33142505745112462659931793)
      ·
        refine ⟨24856879308834346994948845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33142505745112462659931793 24856879308834346994948845)
        ·
          refine ⟨9321329740812880123105817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24856879308834346994948845 9321329740812880123105817)
          ·
            refine ⟨6990997305609660092329363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9321329740812880123105817 6990997305609660092329363)
            ·
              refine ⟨10486495958414490138494045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6990997305609660092329363 10486495958414490138494045)
              ·
                refine ⟨3932435984405433801935267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10486495958414490138494045 3932435984405433801935267)
                ·
                  refine ⟨5898653976608150702902901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3932435984405433801935267 5898653976608150702902901)
                  ·
                    refine ⟨552998810307014128397147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5898653976608150702902901 552998810307014128397147)
                    ·
                      rfl

theorem cell23_3230884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_3230884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230884 prefixEnd_3230884 := by exact prefixLift 3230884
  have htrace : WordTrace (prefixWord ++ tailWord_3230884) baseStart_3230884 baseEnd_3230884 := by
    simpa [prefixWord, tailWord_3230884, baseEnd_3230884] using wordTrace_append hprefix tailTrace_3230884
  have hstable : (prefixWord ++ tailWord_3230884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230884).length < 2 ^ (prefixWord ++ tailWord_3230884).sum := by decide
  have hdescent : baseEnd_3230884 < baseStart_3230884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230907 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 3]
def baseStart_3230907 : Nat := 118140960795 + 3230907 * 2 ^ 59
def prefixEnd_3230907 : Nat := 4983230072969 + 3 ^ 40 * 3230907 * 2
def baseEnd_3230907 : Nat := 1659008240976095795203835

theorem tailTrace_3230907 : CollatzResearch.WordTrace tailWord_3230907 prefixEnd_3230907 1659008240976095795203835 := by
  unfold tailWord_3230907
  simp only [CollatzResearch.WordTrace]
  refine ⟨117840859305983208830066975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78560572870655472553377983 117840859305983208830066975)
  ·
    refine ⟨176761288958974813245100463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117840859305983208830066975 176761288958974813245100463)
    ·
      refine ⟨265141933438462219867650695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176761288958974813245100463 265141933438462219867650695)
      ·
        refine ⟨397712900157693329801476043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265141933438462219867650695 397712900157693329801476043)
        ·
          refine ⟨596569350236539994702214065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397712900157693329801476043 596569350236539994702214065)
          ·
            refine ⟨447427012677404996026660549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596569350236539994702214065 447427012677404996026660549)
            ·
              refine ⟨83892564877013436754998853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 447427012677404996026660549 83892564877013436754998853)
              ·
                refine ⟨15729855914440019391562285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83892564877013436754998853 15729855914440019391562285)
                ·
                  refine ⟨5898695967915007271835857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15729855914440019391562285 5898695967915007271835857)
                  ·
                    refine ⟨4424021975936255453876893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5898695967915007271835857 4424021975936255453876893)
                    ·
                      refine ⟨1659008240976095795203835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4424021975936255453876893 1659008240976095795203835)
                      ·
                        rfl

theorem cell23_3230907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 3].length) (baseStart_3230907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230907 prefixEnd_3230907 := by exact prefixLift 3230907
  have htrace : WordTrace (prefixWord ++ tailWord_3230907) baseStart_3230907 baseEnd_3230907 := by
    simpa [prefixWord, tailWord_3230907, baseEnd_3230907] using wordTrace_append hprefix tailTrace_3230907
  have hstable : (prefixWord ++ tailWord_3230907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230907).length < 2 ^ (prefixWord ++ tailWord_3230907).sum := by decide
  have hdescent : baseEnd_3230907 < baseStart_3230907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230932 : List Nat := [2, 4, 1, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3230932 : Nat := 118140960795 + 3230932 * 2 ^ 59
def prefixEnd_3230932 : Nat := 4983230072969 + 3 ^ 40 * 3230932 * 2
def baseEnd_3230932 : Nat := 1659021077992458197391221

theorem tailTrace_3230932 : CollatzResearch.WordTrace tailWord_3230932 prefixEnd_3230932 1659021077992458197391221 := by
  unfold tailWord_3230932
  simp only [CollatzResearch.WordTrace]
  refine ⟨58920885565446319049863525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78561180753928425399818033 58920885565446319049863525)
  ·
    refine ⟨11047666043521184821849411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58920885565446319049863525 11047666043521184821849411)
    ·
      refine ⟨16571499065281777232774117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11047666043521184821849411 16571499065281777232774117)
      ·
        refine ⟨3107156074740333231145147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16571499065281777232774117 3107156074740333231145147)
        ·
          refine ⟨4660734112110499846717721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3107156074740333231145147 4660734112110499846717721)
          ·
            refine ⟨3495550584082874885038291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4660734112110499846717721 3495550584082874885038291)
            ·
              refine ⟨5243325876124312327557437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495550584082874885038291 5243325876124312327557437)
              ·
                refine ⟨1966247203546617122834039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5243325876124312327557437 1966247203546617122834039)
                ·
                  refine ⟨2949370805319925684251059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966247203546617122834039 2949370805319925684251059)
                  ·
                    refine ⟨4424056207979888526376589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2949370805319925684251059 4424056207979888526376589)
                    ·
                      refine ⟨1659021077992458197391221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4424056207979888526376589 1659021077992458197391221)
                      ·
                        rfl

theorem cell23_3230932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3230932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230932 prefixEnd_3230932 := by exact prefixLift 3230932
  have htrace : WordTrace (prefixWord ++ tailWord_3230932) baseStart_3230932 baseEnd_3230932 := by
    simpa [prefixWord, tailWord_3230932, baseEnd_3230932] using wordTrace_append hprefix tailTrace_3230932
  have hstable : (prefixWord ++ tailWord_3230932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230932).length < 2 ^ (prefixWord ++ tailWord_3230932).sum := by decide
  have hdescent : baseEnd_3230932 < baseStart_3230932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230937 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 3, 3, 3]
def baseStart_3230937 : Nat := 118140960795 + 3230937 * 2 ^ 59
def prefixEnd_3230937 : Nat := 4983230072969 + 3 ^ 40 * 3230937 * 2
def baseEnd_3230937 : Nat := 1659023645395730677828697

theorem tailTrace_3230937 : CollatzResearch.WordTrace tailWord_3230937 prefixEnd_3230937 1659023645395730677828697 := by
  unfold tailWord_3230937
  simp only [CollatzResearch.WordTrace]
  refine ⟨117841953495874523953659065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78561302330583015969106043 117841953495874523953659065)
  ·
    refine ⟨88381465121905892965244299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117841953495874523953659065 88381465121905892965244299)
    ·
      refine ⟨132572197682858839447866449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88381465121905892965244299 132572197682858839447866449)
      ·
        refine ⟨99429148262144129585899837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132572197682858839447866449 99429148262144129585899837)
        ·
          refine ⟨37285930598304048594712439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99429148262144129585899837 37285930598304048594712439)
          ·
            refine ⟨55928895897456072892068659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37285930598304048594712439 55928895897456072892068659)
            ·
              refine ⟨83893343846184109338102989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55928895897456072892068659 83893343846184109338102989)
              ·
                refine ⟨31460003942319041001788621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83893343846184109338102989 31460003942319041001788621)
                ·
                  refine ⟨11797501478369640375670733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31460003942319041001788621 11797501478369640375670733)
                  ·
                    refine ⟨4424063054388615140876525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11797501478369640375670733 4424063054388615140876525)
                    ·
                      refine ⟨1659023645395730677828697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4424063054388615140876525 1659023645395730677828697)
                      ·
                        rfl

theorem cell23_3230937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_3230937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230937 prefixEnd_3230937 := by exact prefixLift 3230937
  have htrace : WordTrace (prefixWord ++ tailWord_3230937) baseStart_3230937 baseEnd_3230937 := by
    simpa [prefixWord, tailWord_3230937, baseEnd_3230937] using wordTrace_append hprefix tailTrace_3230937
  have hstable : (prefixWord ++ tailWord_3230937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230937).length < 2 ^ (prefixWord ++ tailWord_3230937).sum := by decide
  have hdescent : baseEnd_3230937 < baseStart_3230937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230941 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3230941 : Nat := 118140960795 + 3230941 * 2 ^ 59
def prefixEnd_3230941 : Nat := 4983230072969 + 3 ^ 40 * 3230941 * 2
def baseEnd_3230941 : Nat := 1659025699318348662178679

theorem tailTrace_3230941 : CollatzResearch.WordTrace tailWord_3230941 prefixEnd_3230941 1659025699318348662178679 := by
  unfold tailWord_3230941
  simp only [CollatzResearch.WordTrace]
  refine ⟨117842099387860032636804677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78561399591906688424536451 117842099387860032636804677)
  ·
    refine ⟨22095393635223756119400877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117842099387860032636804677 22095393635223756119400877)
    ·
      refine ⟨8285772613208908544775329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22095393635223756119400877 8285772613208908544775329)
      ·
        refine ⟨6214329459906681408581497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8285772613208908544775329 6214329459906681408581497)
        ·
          refine ⟨4660747094930011056436123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6214329459906681408581497 4660747094930011056436123)
          ·
            refine ⟨6991120642395016584654185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4660747094930011056436123 6991120642395016584654185)
            ·
              refine ⟨5243340481796262438490639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6991120642395016584654185 5243340481796262438490639)
              ·
                refine ⟨7865010722694393657735959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5243340481796262438490639 7865010722694393657735959)
                ·
                  refine ⟨11797516084041590486603939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7865010722694393657735959 11797516084041590486603939)
                  ·
                    refine ⟨17696274126062385729905909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11797516084041590486603939 17696274126062385729905909)
                    ·
                      refine ⟨1659025699318348662178679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17696274126062385729905909 1659025699318348662178679)
                      ·
                        rfl

theorem cell23_3230941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3230941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230941 prefixEnd_3230941 := by exact prefixLift 3230941
  have htrace : WordTrace (prefixWord ++ tailWord_3230941) baseStart_3230941 baseEnd_3230941 := by
    simpa [prefixWord, tailWord_3230941, baseEnd_3230941] using wordTrace_append hprefix tailTrace_3230941
  have hstable : (prefixWord ++ tailWord_3230941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230941).length < 2 ^ (prefixWord ++ tailWord_3230941).sum := by decide
  have hdescent : baseEnd_3230941 < baseStart_3230941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3230955 : List Nat := [1, 1, 1, 1, 2, 7, 3, 2, 1, 2, 2]
def baseStart_3230955 : Nat := 118140960795 + 3230955 * 2 ^ 59
def prefixEnd_3230955 : Nat := 4983230072969 + 3 ^ 40 * 3230955 * 2
def baseEnd_3230955 : Nat := 1659032888047511607403615

theorem tailTrace_3230955 : CollatzResearch.WordTrace tailWord_3230955 prefixEnd_3230955 1659032888047511607403615 := by
  unfold tailWord_3230955
  simp only [CollatzResearch.WordTrace]
  refine ⟨117842610009809313027814319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78561740006539542018542879 117842610009809313027814319)
  ·
    refine ⟨176763915014713969541721479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117842610009809313027814319 176763915014713969541721479)
    ·
      refine ⟨265145872522070954312582219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176763915014713969541721479 265145872522070954312582219)
      ·
        refine ⟨397718808783106431468873329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265145872522070954312582219 397718808783106431468873329)
        ·
          refine ⟨298289106587329823601654997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397718808783106431468873329 298289106587329823601654997)
          ·
            refine ⟨6991150935640542740663789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 298289106587329823601654997 6991150935640542740663789)
            ·
              refine ⟨2621681600865203527748921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6991150935640542740663789 2621681600865203527748921)
              ·
                refine ⟨1966261200648902645811691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2621681600865203527748921 1966261200648902645811691)
                ·
                  refine ⟨2949391800973353968717537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966261200648902645811691 2949391800973353968717537)
                  ·
                    refine ⟨2212043850730015476538153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2949391800973353968717537 2212043850730015476538153)
                    ·
                      refine ⟨1659032888047511607403615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212043850730015476538153 1659032888047511607403615)
                      ·
                        rfl

theorem cell23_3230955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 1, 2, 2].length) (baseStart_3230955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3230955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3230955 prefixEnd_3230955 := by exact prefixLift 3230955
  have htrace : WordTrace (prefixWord ++ tailWord_3230955) baseStart_3230955 baseEnd_3230955 := by
    simpa [prefixWord, tailWord_3230955, baseEnd_3230955] using wordTrace_append hprefix tailTrace_3230955
  have hstable : (prefixWord ++ tailWord_3230955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3230955).length < 2 ^ (prefixWord ++ tailWord_3230955).sum := by decide
  have hdescent : baseEnd_3230955 < baseStart_3230955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3230955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231006 : List Nat := [4, 3, 2, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_3231006 : Nat := 118140960795 + 3231006 * 2 ^ 59
def prefixEnd_3231006 : Nat := 4983230072969 + 3 ^ 40 * 3231006 * 2
def baseEnd_3231006 : Nat := 1659059075560890907865881

theorem tailTrace_3231006 : CollatzResearch.WordTrace tailWord_3231006 prefixEnd_3231006 1659059075560890907865881 := by
  unfold tailWord_3231006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14730558766578068592240109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78562980088416365825280581 14730558766578068592240109)
  ·
    refine ⟨5523959537466775722090041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14730558766578068592240109 5523959537466775722090041)
    ·
      refine ⟨4142969653100081791567531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5523959537466775722090041 4142969653100081791567531)
      ·
        refine ⟨6214454479650122687351297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4142969653100081791567531 6214454479650122687351297)
        ·
          refine ⟨4660840859737592015513473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6214454479650122687351297 4660840859737592015513473)
          ·
            refine ⟨3495630644803194011635105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4660840859737592015513473 3495630644803194011635105)
            ·
              refine ⟨2621722983602395508726329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3495630644803194011635105 2621722983602395508726329)
              ·
                refine ⟨1966292237701796631544747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2621722983602395508726329 1966292237701796631544747)
                ·
                  refine ⟨2949438356552694947317121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966292237701796631544747 2949438356552694947317121)
                  ·
                    refine ⟨2212078767414521210487841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2949438356552694947317121 2212078767414521210487841)
                    ·
                      refine ⟨1659059075560890907865881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212078767414521210487841 1659059075560890907865881)
                      ·
                        rfl

theorem cell23_3231006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_3231006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231006 prefixEnd_3231006 := by exact prefixLift 3231006
  have htrace : WordTrace (prefixWord ++ tailWord_3231006) baseStart_3231006 baseEnd_3231006 := by
    simpa [prefixWord, tailWord_3231006, baseEnd_3231006] using wordTrace_append hprefix tailTrace_3231006
  have hstable : (prefixWord ++ tailWord_3231006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231006).length < 2 ^ (prefixWord ++ tailWord_3231006).sum := by decide
  have hdescent : baseEnd_3231006 < baseStart_3231006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231021 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3231021 : Nat := 118140960795 + 3231021 * 2 ^ 59
def prefixEnd_3231021 : Nat := 4983230072969 + 3 ^ 40 * 3231021 * 2
def baseEnd_3231021 : Nat := 553022259256902783059437

theorem tailTrace_3231021 : CollatzResearch.WordTrace tailWord_3231021 prefixEnd_3231021 553022259256902783059437 := by
  unfold tailWord_3231021
  simp only [CollatzResearch.WordTrace]
  refine ⟨117845017227570206299716917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78563344818380137533144611 117845017227570206299716917)
  ·
    refine ⟨11047970365084706840598461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117845017227570206299716917 11047970365084706840598461)
    ·
      refine ⟨4142988886906765065224423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11047970365084706840598461 4142988886906765065224423)
      ·
        refine ⟨6214483330360147597836635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4142988886906765065224423 6214483330360147597836635)
        ·
          refine ⟨9321724995540221396754953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6214483330360147597836635 9321724995540221396754953)
          ·
            refine ⟨6991293746655166047566215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9321724995540221396754953 6991293746655166047566215)
            ·
              refine ⟨10486940619982749071349323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6991293746655166047566215 10486940619982749071349323)
              ·
                refine ⟨15730410929974123607023985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10486940619982749071349323 15730410929974123607023985)
                ·
                  refine ⟨11797808197480592705267989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15730410929974123607023985 11797808197480592705267989)
                  ·
                    refine ⟨553022259256902783059437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11797808197480592705267989 553022259256902783059437)
                    ·
                      rfl

theorem cell23_3231021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3231021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231021 prefixEnd_3231021 := by exact prefixLift 3231021
  have htrace : WordTrace (prefixWord ++ tailWord_3231021) baseStart_3231021 baseEnd_3231021 := by
    simpa [prefixWord, tailWord_3231021, baseEnd_3231021] using wordTrace_append hprefix tailTrace_3231021
  have hstable : (prefixWord ++ tailWord_3231021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231021).length < 2 ^ (prefixWord ++ tailWord_3231021).sum := by decide
  have hdescent : baseEnd_3231021 < baseStart_3231021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231028 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_3231028 : Nat := 118140960795 + 3231028 * 2 ^ 59
def prefixEnd_3231028 : Nat := 4983230072969 + 3 ^ 40 * 3231028 * 2
def baseEnd_3231028 : Nat := 1659070372135289821790779

theorem tailTrace_3231028 : CollatzResearch.WordTrace tailWord_3231028 prefixEnd_3231028 1659070372135289821790779 := by
  unfold tailWord_3231028
  simp only [CollatzResearch.WordTrace]
  refine ⟨58922636269272423247610869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78563515025696564330147825 58922636269272423247610869)
  ·
    refine ⟨5523997150244289679463519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58922636269272423247610869 5523997150244289679463519)
    ·
      refine ⟨8285995725366434519195279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5523997150244289679463519 8285995725366434519195279)
      ·
        refine ⟨12428993588049651778792919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8285995725366434519195279 12428993588049651778792919)
        ·
          refine ⟨18643490382074477668189379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12428993588049651778792919 18643490382074477668189379)
          ·
            refine ⟨27965235573111716502284069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18643490382074477668189379 27965235573111716502284069)
            ·
              refine ⟨5243481669958446844178263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27965235573111716502284069 5243481669958446844178263)
              ·
                refine ⟨7865222504937670266267395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5243481669958446844178263 7865222504937670266267395)
                ·
                  refine ⟨11797833757406505399401093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7865222504937670266267395 11797833757406505399401093)
                  ·
                    refine ⟨2212093829513719762387705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11797833757406505399401093 2212093829513719762387705)
                    ·
                      refine ⟨1659070372135289821790779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212093829513719762387705 1659070372135289821790779)
                      ·
                        rfl

theorem cell23_3231028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_3231028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231028 prefixEnd_3231028 := by exact prefixLift 3231028
  have htrace : WordTrace (prefixWord ++ tailWord_3231028) baseStart_3231028 baseEnd_3231028 := by
    simpa [prefixWord, tailWord_3231028, baseEnd_3231028] using wordTrace_append hprefix tailTrace_3231028
  have hstable : (prefixWord ++ tailWord_3231028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231028).length < 2 ^ (prefixWord ++ tailWord_3231028).sum := by decide
  have hdescent : baseEnd_3231028 < baseStart_3231028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231074 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3231074 : Nat := 118140960795 + 3231074 * 2 ^ 59
def prefixEnd_3231074 : Nat := 4983230072969 + 3 ^ 40 * 3231074 * 2
def baseEnd_3231074 : Nat := 1659093992245396641815567

theorem tailTrace_3231074 : CollatzResearch.WordTrace tailWord_3231074 prefixEnd_3231074 1659093992245396641815567 := by
  unfold tailWord_3231074
  simp only [CollatzResearch.WordTrace]
  refine ⟨29461737574094549087849069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78564633530918797567597517 29461737574094549087849069)
  ·
    refine ⟨11048151590285455907943401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29461737574094549087849069 11048151590285455907943401)
    ·
      refine ⟨8286113692714091930957551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11048151590285455907943401 8286113692714091930957551)
      ·
        refine ⟨12429170539071137896436327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8286113692714091930957551 12429170539071137896436327)
        ·
          refine ⟨18643755808606706844654491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12429170539071137896436327 18643755808606706844654491)
          ·
            refine ⟨27965633712910060266981737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18643755808606706844654491 27965633712910060266981737)
            ·
              refine ⟨20974225284682545200236303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27965633712910060266981737 20974225284682545200236303)
              ·
                refine ⟨31461337927023817800354455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20974225284682545200236303 31461337927023817800354455)
                ·
                  refine ⟨47192006890535726700531683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31461337927023817800354455 47192006890535726700531683)
                  ·
                    refine ⟨70788010335803590050797525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47192006890535726700531683 70788010335803590050797525)
                    ·
                      refine ⟨1659093992245396641815567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70788010335803590050797525 1659093992245396641815567)
                      ·
                        rfl

theorem cell23_3231074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3231074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231074 prefixEnd_3231074 := by exact prefixLift 3231074
  have htrace : WordTrace (prefixWord ++ tailWord_3231074) baseStart_3231074 baseEnd_3231074 := by
    simpa [prefixWord, tailWord_3231074, baseEnd_3231074] using wordTrace_append hprefix tailTrace_3231074
  have hstable : (prefixWord ++ tailWord_3231074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231074).length < 2 ^ (prefixWord ++ tailWord_3231074).sum := by decide
  have hdescent : baseEnd_3231074 < baseStart_3231074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231084 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_3231084 : Nat := 118140960795 + 3231084 * 2 ^ 59
def prefixEnd_3231084 : Nat := 4983230072969 + 3 ^ 40 * 3231084 * 2
def baseEnd_3231084 : Nat := 1659099127051941602690521

theorem tailTrace_3231084 : CollatzResearch.WordTrace tailWord_3231084 prefixEnd_3231084 1659099127051941602690521 := by
  unfold tailWord_3231084
  simp only [CollatzResearch.WordTrace]
  refine ⟨58923657513170984029630153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78564876684227978706173537 58923657513170984029630153)
  ·
    refine ⟨44192743134878238022222615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58923657513170984029630153 44192743134878238022222615)
    ·
      refine ⟨66289114702317357033333923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44192743134878238022222615 66289114702317357033333923)
      ·
        refine ⟨99433672053476035550000885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66289114702317357033333923 99433672053476035550000885)
        ·
          refine ⟨9321906755013378332812583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99433672053476035550000885 9321906755013378332812583)
          ·
            refine ⟨13982860132520067499218875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9321906755013378332812583 13982860132520067499218875)
            ·
              refine ⟨20974290198780101248828313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13982860132520067499218875 20974290198780101248828313)
              ·
                refine ⟨15730717649085075936621235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20974290198780101248828313 15730717649085075936621235)
                ·
                  refine ⟨23596076473627613904931853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15730717649085075936621235 23596076473627613904931853)
                  ·
                    refine ⟨8848528677610355214349445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23596076473627613904931853 8848528677610355214349445)
                    ·
                      refine ⟨1659099127051941602690521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8848528677610355214349445 1659099127051941602690521)
                      ·
                        rfl

theorem cell23_3231084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_3231084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231084 prefixEnd_3231084 := by exact prefixLift 3231084
  have htrace : WordTrace (prefixWord ++ tailWord_3231084) baseStart_3231084 baseEnd_3231084 := by
    simpa [prefixWord, tailWord_3231084, baseEnd_3231084] using wordTrace_append hprefix tailTrace_3231084
  have hstable : (prefixWord ++ tailWord_3231084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231084).length < 2 ^ (prefixWord ++ tailWord_3231084).sum := by decide
  have hdescent : baseEnd_3231084 < baseStart_3231084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231102 : List Nat := [4, 2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_3231102 : Nat := 118140960795 + 3231102 * 2 ^ 59
def prefixEnd_3231102 : Nat := 4983230072969 + 3 ^ 40 * 3231102 * 2
def baseEnd_3231102 : Nat := 184345374411524725807271

theorem tailTrace_3231102 : CollatzResearch.WordTrace tailWord_3231102 prefixEnd_3231102 184345374411524725807271 := by
  unfold tailWord_3231102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14730996442534594641676945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78565314360184504755610373 14730996442534594641676945)
  ·
    refine ⟨11048247331900945981257709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14730996442534594641676945 11048247331900945981257709)
    ·
      refine ⟨4143092749462854742971641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11048247331900945981257709 4143092749462854742971641)
      ·
        refine ⟨3107319562097141057228731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4143092749462854742971641 3107319562097141057228731)
        ·
          refine ⟨4660979343145711585843097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3107319562097141057228731 4660979343145711585843097)
          ·
            refine ⟨3495734507359283689382323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4660979343145711585843097 3495734507359283689382323)
            ·
              refine ⟨5243601761038925534073485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495734507359283689382323 5243601761038925534073485)
              ·
                refine ⟨1966350660389597075277557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5243601761038925534073485 1966350660389597075277557)
                ·
                  refine ⟨184345374411524725807271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1966350660389597075277557 184345374411524725807271)
                  ·
                    rfl

theorem cell23_3231102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_3231102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231102 prefixEnd_3231102 := by exact prefixLift 3231102
  have htrace : WordTrace (prefixWord ++ tailWord_3231102) baseStart_3231102 baseEnd_3231102 := by
    simpa [prefixWord, tailWord_3231102, baseEnd_3231102] using wordTrace_append hprefix tailTrace_3231102
  have hstable : (prefixWord ++ tailWord_3231102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231102).length < 2 ^ (prefixWord ++ tailWord_3231102).sum := by decide
  have hdescent : baseEnd_3231102 < baseStart_3231102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231104 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 3]
def baseStart_3231104 : Nat := 118140960795 + 3231104 * 2 ^ 59
def prefixEnd_3231104 : Nat := 4983230072969 + 3 ^ 40 * 3231104 * 2
def baseEnd_3231104 : Nat := 1659109396665031524440429

theorem tailTrace_3231104 : CollatzResearch.WordTrace tailWord_3231104 prefixEnd_3231104 1659109396665031524440429 := by
  unfold tailWord_3231104
  simp only [CollatzResearch.WordTrace]
  refine ⟨58924022243134755737494183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78565362990846340983325577 58924022243134755737494183)
  ·
    refine ⟨88386033364702133606241275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58924022243134755737494183 88386033364702133606241275)
    ·
      refine ⟨132579050047053200409361913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88386033364702133606241275 132579050047053200409361913)
      ·
        refine ⟨99434287535289900307021435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132579050047053200409361913 99434287535289900307021435)
        ·
          refine ⟨149151431302934850460532153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99434287535289900307021435 149151431302934850460532153)
          ·
            refine ⟨111863573477201137845399115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149151431302934850460532153 111863573477201137845399115)
            ·
              refine ⟨167795360215801706768098673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111863573477201137845399115 167795360215801706768098673)
              ·
                refine ⟨125846520161851280076074005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167795360215801706768098673 125846520161851280076074005)
                ·
                  refine ⟨5899055632586778753565969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125846520161851280076074005 5899055632586778753565969)
                  ·
                    refine ⟨4424291724440084065174477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5899055632586778753565969 4424291724440084065174477)
                    ·
                      refine ⟨1659109396665031524440429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4424291724440084065174477 1659109396665031524440429)
                      ·
                        rfl

theorem cell23_3231104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_3231104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231104 prefixEnd_3231104 := by exact prefixLift 3231104
  have htrace : WordTrace (prefixWord ++ tailWord_3231104) baseStart_3231104 baseEnd_3231104 := by
    simpa [prefixWord, tailWord_3231104, baseEnd_3231104] using wordTrace_append hprefix tailTrace_3231104
  have hstable : (prefixWord ++ tailWord_3231104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231104).length < 2 ^ (prefixWord ++ tailWord_3231104).sum := by decide
  have hdescent : baseEnd_3231104 < baseStart_3231104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231118 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3231118 : Nat := 118140960795 + 3231118 * 2 ^ 59
def prefixEnd_3231118 : Nat := 4983230072969 + 3 ^ 40 * 3231118 * 2
def baseEnd_3231118 : Nat := 1659116585394194469665365

theorem tailTrace_3231118 : CollatzResearch.WordTrace tailWord_3231118 prefixEnd_3231118 1659116585394194469665365 := by
  unfold tailWord_3231118
  simp only [CollatzResearch.WordTrace]
  refine ⟨14731069388527348983249751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78565703405479194577332005 14731069388527348983249751)
  ·
    refine ⟨22096604082791023474874627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14731069388527348983249751 22096604082791023474874627)
    ·
      refine ⟨33144906124186535212311941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22096604082791023474874627 33144906124186535212311941)
      ·
        refine ⟨6214669898284975352308489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33144906124186535212311941 6214669898284975352308489)
        ·
          refine ⟨4661002423713731514231367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6214669898284975352308489 4661002423713731514231367)
          ·
            refine ⟨6991503635570597271347051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4661002423713731514231367 6991503635570597271347051)
            ·
              refine ⟨10487255453355895907020577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6991503635570597271347051 10487255453355895907020577)
              ·
                refine ⟨7865441590016921930265433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10487255453355895907020577 7865441590016921930265433)
                ·
                  refine ⟨5899081192512691447699075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7865441590016921930265433 5899081192512691447699075)
                  ·
                    refine ⟨8848621788769037171548613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5899081192512691447699075 8848621788769037171548613)
                    ·
                      refine ⟨1659116585394194469665365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8848621788769037171548613 1659116585394194469665365)
                      ·
                        rfl

theorem cell23_3231118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3231118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231118 prefixEnd_3231118 := by exact prefixLift 3231118
  have htrace : WordTrace (prefixWord ++ tailWord_3231118) baseStart_3231118 baseEnd_3231118 := by
    simpa [prefixWord, tailWord_3231118, baseEnd_3231118] using wordTrace_append hprefix tailTrace_3231118
  have hstable : (prefixWord ++ tailWord_3231118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231118).length < 2 ^ (prefixWord ++ tailWord_3231118).sum := by decide
  have hdescent : baseEnd_3231118 < baseStart_3231118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231151 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 3, 1, 3]
def baseStart_3231151 : Nat := 118140960795 + 3231151 * 2 ^ 59
def prefixEnd_3231151 : Nat := 4983230072969 + 3 ^ 40 * 3231151 * 2
def baseEnd_3231151 : Nat := 1659133530255792840552713

theorem tailTrace_3231151 : CollatzResearch.WordTrace tailWord_3231151 prefixEnd_3231151 1659133530255792840552713 := by
  unfold tailWord_3231151
  simp only [CollatzResearch.WordTrace]
  refine ⟨117849758717099238501949307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78566505811399492334632871 117849758717099238501949307)
  ·
    refine ⟨176774638075648857752923961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117849758717099238501949307 176774638075648857752923961)
    ·
      refine ⟨132580978556736643314692971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176774638075648857752923961 132580978556736643314692971)
      ·
        refine ⟨198871467835104964972039457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132580978556736643314692971 198871467835104964972039457)
        ·
          refine ⟨149153600876328723729029593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198871467835104964972039457 149153600876328723729029593)
          ·
            refine ⟨111865200657246542796772195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149153600876328723729029593 111865200657246542796772195)
            ·
              refine ⟨167797800985869814195158293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111865200657246542796772195 167797800985869814195158293)
              ·
                refine ⟨7865521921212647540398045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167797800985869814195158293 7865521921212647540398045)
                ·
                  refine ⟨2949570720454742827649267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7865521921212647540398045 2949570720454742827649267)
                  ·
                    refine ⟨4424356080682114241473901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2949570720454742827649267 4424356080682114241473901)
                    ·
                      refine ⟨1659133530255792840552713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4424356080682114241473901 1659133530255792840552713)
                      ·
                        rfl

theorem cell23_3231151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 1, 3].length) (baseStart_3231151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231151 prefixEnd_3231151 := by exact prefixLift 3231151
  have htrace : WordTrace (prefixWord ++ tailWord_3231151) baseStart_3231151 baseEnd_3231151 := by
    simpa [prefixWord, tailWord_3231151, baseEnd_3231151] using wordTrace_append hprefix tailTrace_3231151
  have hstable : (prefixWord ++ tailWord_3231151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231151).length < 2 ^ (prefixWord ++ tailWord_3231151).sum := by decide
  have hdescent : baseEnd_3231151 < baseStart_3231151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231178 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2]
def baseStart_3231178 : Nat := 118140960795 + 3231178 * 2 ^ 59
def prefixEnd_3231178 : Nat := 4983230072969 + 3 ^ 40 * 3231178 * 2
def baseEnd_3231178 : Nat := 1659147394233464234915089

theorem tailTrace_3231178 : CollatzResearch.WordTrace tailWord_3231178 prefixEnd_3231178 1659147394233464234915089 := by
  unfold tailWord_3231178
  simp only [CollatzResearch.WordTrace]
  refine ⟨29462685872000355528295547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78567162325334281408788125 29462685872000355528295547)
  ·
    refine ⟨44194028808000533292443321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29462685872000355528295547 44194028808000533292443321)
    ·
      refine ⟨33145521606000399969332491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44194028808000533292443321 33145521606000399969332491)
      ·
        refine ⟨49718282409000599953998737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33145521606000399969332491 49718282409000599953998737)
        ·
          refine ⟨37288711806750449965499053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49718282409000599953998737 37288711806750449965499053)
          ·
            refine ⟨13983266927531418737062145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37288711806750449965499053 13983266927531418737062145)
            ·
              refine ⟨10487450195648564052796609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13983266927531418737062145 10487450195648564052796609)
              ·
                refine ⟨7865587646736423039597457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10487450195648564052796609 7865587646736423039597457)
                ·
                  refine ⟨5899190735052317279698093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7865587646736423039597457 5899190735052317279698093)
                  ·
                    refine ⟨2212196525644618979886785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5899190735052317279698093 2212196525644618979886785)
                    ·
                      refine ⟨1659147394233464234915089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212196525644618979886785 1659147394233464234915089)
                      ·
                        rfl

theorem cell23_3231178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_3231178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231178 prefixEnd_3231178 := by exact prefixLift 3231178
  have htrace : WordTrace (prefixWord ++ tailWord_3231178) baseStart_3231178 baseEnd_3231178 := by
    simpa [prefixWord, tailWord_3231178, baseEnd_3231178] using wordTrace_append hprefix tailTrace_3231178
  have hstable : (prefixWord ++ tailWord_3231178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231178).length < 2 ^ (prefixWord ++ tailWord_3231178).sum := by decide
  have hdescent : baseEnd_3231178 < baseStart_3231178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231201 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 1, 6]
def baseStart_3231201 : Nat := 118140960795 + 3231201 * 2 ^ 59
def prefixEnd_3231201 : Nat := 4983230072969 + 3 ^ 40 * 3231201 * 2
def baseEnd_3231201 : Nat := 553053068096172548309161

theorem tailTrace_3231201 : CollatzResearch.WordTrace tailWord_3231201 prefixEnd_3231201 553053068096172548309161 := by
  unfold tailWord_3231201
  simp only [CollatzResearch.WordTrace]
  refine ⟨117851582366918097041269457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78567721577945398027512971 117851582366918097041269457)
  ·
    refine ⟨88388686775188572780952093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117851582366918097041269457 88388686775188572780952093)
    ·
      refine ⟨33145757540695714792857035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88388686775188572780952093 33145757540695714792857035)
      ·
        refine ⟨49718636311043572189285553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33145757540695714792857035 49718636311043572189285553)
        ·
          refine ⟨37288977233282679141964165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49718636311043572189285553 37288977233282679141964165)
          ·
            refine ⟨6991683231240502339118281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37288977233282679141964165 6991683231240502339118281)
            ·
              refine ⟨5243762423430376754338711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6991683231240502339118281 5243762423430376754338711)
              ·
                refine ⟨7865643635145565131508067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5243762423430376754338711 7865643635145565131508067)
                ·
                  refine ⟨11798465452718347697262101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7865643635145565131508067 11798465452718347697262101)
                  ·
                    refine ⟨553053068096172548309161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11798465452718347697262101 553053068096172548309161)
                    ·
                      rfl

theorem cell23_3231201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_3231201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231201 prefixEnd_3231201 := by exact prefixLift 3231201
  have htrace : WordTrace (prefixWord ++ tailWord_3231201) baseStart_3231201 baseEnd_3231201 := by
    simpa [prefixWord, tailWord_3231201, baseEnd_3231201] using wordTrace_append hprefix tailTrace_3231201
  have hstable : (prefixWord ++ tailWord_3231201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231201).length < 2 ^ (prefixWord ++ tailWord_3231201).sum := by decide
  have hdescent : baseEnd_3231201 < baseStart_3231201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231204 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_3231204 : Nat := 118140960795 + 3231204 * 2 ^ 59
def prefixEnd_3231204 : Nat := 4983230072969 + 3 ^ 40 * 3231204 * 2
def baseEnd_3231204 : Nat := 1659160744730481133189969

theorem tailTrace_3231204 : CollatzResearch.WordTrace tailWord_3231204 prefixEnd_3231204 1659160744730481133189969 := by
  unfold tailWord_3231204
  simp only [CollatzResearch.WordTrace]
  refine ⟨58925845892953614276814333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78567794523938152369085777 58925845892953614276814333)
  ·
    refine ⟨22097192209857605353805375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58925845892953614276814333 22097192209857605353805375)
    ·
      refine ⟨33145788314786408030708063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22097192209857605353805375 33145788314786408030708063)
      ·
        refine ⟨49718682472179612046062095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33145788314786408030708063 49718682472179612046062095)
        ·
          refine ⟨74578023708269418069093143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49718682472179612046062095 74578023708269418069093143)
          ·
            refine ⟨111867035562404127103639715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74578023708269418069093143 111867035562404127103639715)
            ·
              refine ⟨167800553343606190655459573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111867035562404127103639715 167800553343606190655459573)
              ·
                refine ⟨15731301875963080373949335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167800553343606190655459573 15731301875963080373949335)
                ·
                  refine ⟨23596952813944620560924003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15731301875963080373949335 23596952813944620560924003)
                  ·
                    refine ⟨35395429220916930841386005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23596952813944620560924003 35395429220916930841386005)
                    ·
                      refine ⟨1659160744730481133189969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35395429220916930841386005 1659160744730481133189969)
                      ·
                        rfl

theorem cell23_3231204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_3231204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231204 prefixEnd_3231204 := by exact prefixLift 3231204
  have htrace : WordTrace (prefixWord ++ tailWord_3231204) baseStart_3231204 baseEnd_3231204 := by
    simpa [prefixWord, tailWord_3231204, baseEnd_3231204] using wordTrace_append hprefix tailTrace_3231204
  have hstable : (prefixWord ++ tailWord_3231204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231204).length < 2 ^ (prefixWord ++ tailWord_3231204).sum := by decide
  have hdescent : baseEnd_3231204 < baseStart_3231204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231242 : List Nat := [3, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2]
def baseStart_3231242 : Nat := 118140960795 + 3231242 * 2 ^ 59
def prefixEnd_3231242 : Nat := 4983230072969 + 3 ^ 40 * 3231242 * 2
def baseEnd_3231242 : Nat := 1659180256995351984514795

theorem tailTrace_3231242 : CollatzResearch.WordTrace tailWord_3231242 prefixEnd_3231242 1659180256995351984514795 := by
  unfold tailWord_3231242
  simp only [CollatzResearch.WordTrace]
  refine ⟨29463269439942390260877995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78568718506513040695674653 29463269439942390260877995)
  ·
    refine ⟨44194904159913585391316993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29463269439942390260877995 44194904159913585391316993)
    ·
      refine ⟨33146178119935189043487745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44194904159913585391316993 33146178119935189043487745)
      ·
        refine ⟨24859633589951391782615809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33146178119935189043487745 24859633589951391782615809)
        ·
          refine ⟨18644725192463543836961857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24859633589951391782615809 18644725192463543836961857)
          ·
            refine ⟨13983543894347657877721393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18644725192463543836961857 13983543894347657877721393)
            ·
              refine ⟨10487657920760743408291045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13983543894347657877721393 10487657920760743408291045)
              ·
                refine ⟨1966435860142639389054571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10487657920760743408291045 1966435860142639389054571)
                ·
                  refine ⟨2949653790213959083581857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966435860142639389054571 2949653790213959083581857)
                  ·
                    refine ⟨2212240342660469312686393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2949653790213959083581857 2212240342660469312686393)
                    ·
                      refine ⟨1659180256995351984514795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212240342660469312686393 1659180256995351984514795)
                      ·
                        rfl

theorem cell23_3231242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_3231242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231242 prefixEnd_3231242 := by exact prefixLift 3231242
  have htrace : WordTrace (prefixWord ++ tailWord_3231242) baseStart_3231242 baseEnd_3231242 := by
    simpa [prefixWord, tailWord_3231242, baseEnd_3231242] using wordTrace_append hprefix tailTrace_3231242
  have hstable : (prefixWord ++ tailWord_3231242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231242).length < 2 ^ (prefixWord ++ tailWord_3231242).sum := by decide
  have hdescent : baseEnd_3231242 < baseStart_3231242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231252 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3231252 : Nat := 118140960795 + 3231252 * 2 ^ 59
def prefixEnd_3231252 : Nat := 4983230072969 + 3 ^ 40 * 3231252 * 2
def baseEnd_3231252 : Nat := 553061797267298981796583

theorem tailTrace_3231252 : CollatzResearch.WordTrace tailWord_3231252 prefixEnd_3231252 553061797267298981796583 := by
  unfold tailWord_3231252
  simp only [CollatzResearch.WordTrace]
  refine ⟨58926721244866666375688005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78568961659822221834250673 58926721244866666375688005)
  ·
    refine ⟨11048760233412499945441501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58926721244866666375688005 11048760233412499945441501)
    ·
      refine ⟨4143285087529687479540563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11048760233412499945441501 4143285087529687479540563)
      ·
        refine ⟨6214927631294531219310845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4143285087529687479540563 6214927631294531219310845)
        ·
          refine ⟨2330597861735449207241567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6214927631294531219310845 2330597861735449207241567)
          ·
            refine ⟨3495896792603173810862351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2330597861735449207241567 3495896792603173810862351)
            ·
              refine ⟨5243845188904760716293527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495896792603173810862351 5243845188904760716293527)
              ·
                refine ⟨7865767783357141074440291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5243845188904760716293527 7865767783357141074440291)
                ·
                  refine ⟨11798651675035711611660437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7865767783357141074440291 11798651675035711611660437)
                  ·
                    refine ⟨553061797267298981796583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11798651675035711611660437 553061797267298981796583)
                    ·
                      rfl

theorem cell23_3231252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3231252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231252 prefixEnd_3231252 := by exact prefixLift 3231252
  have htrace : WordTrace (prefixWord ++ tailWord_3231252) baseStart_3231252 baseEnd_3231252 := by
    simpa [prefixWord, tailWord_3231252, baseEnd_3231252] using wordTrace_append hprefix tailTrace_3231252
  have hstable : (prefixWord ++ tailWord_3231252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231252).length < 2 ^ (prefixWord ++ tailWord_3231252).sum := by decide
  have hdescent : baseEnd_3231252 < baseStart_3231252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231285 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_3231285 : Nat := 118140960795 + 3231285 * 2 ^ 59
def prefixEnd_3231285 : Nat := 4983230072969 + 3 ^ 40 * 3231285 * 2
def baseEnd_3231285 : Nat := 1659202336663495316277097

theorem tailTrace_3231285 : CollatzResearch.WordTrace tailWord_3231285 prefixEnd_3231285 1659202336663495316277097 := by
  unfold tailWord_3231285
  simp only [CollatzResearch.WordTrace]
  refine ⟨117854646098613779387327309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78569764065742519591551539 117854646098613779387327309)
  ·
    refine ⟨44195492286980167270247741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117854646098613779387327309 44195492286980167270247741)
    ·
      refine ⟨16573309607617562726342903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44195492286980167270247741 16573309607617562726342903)
      ·
        refine ⟨24859964411426344089514355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16573309607617562726342903 24859964411426344089514355)
        ·
          refine ⟨37289946617139516134271533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24859964411426344089514355 37289946617139516134271533)
          ·
            refine ⟨13983729981427318550351825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37289946617139516134271533 13983729981427318550351825)
            ·
              refine ⟨10487797486070488912763869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13983729981427318550351825 10487797486070488912763869)
              ·
                refine ⟨3932924057276433342286451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10487797486070488912763869 3932924057276433342286451)
                ·
                  refine ⟨5899386085914650013429677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3932924057276433342286451 5899386085914650013429677)
                  ·
                    refine ⟨2212269782217993755036129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5899386085914650013429677 2212269782217993755036129)
                    ·
                      refine ⟨1659202336663495316277097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212269782217993755036129 1659202336663495316277097)
                      ·
                        rfl

theorem cell23_3231285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_3231285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231285 prefixEnd_3231285 := by exact prefixLift 3231285
  have htrace : WordTrace (prefixWord ++ tailWord_3231285) baseStart_3231285 baseEnd_3231285 := by
    simpa [prefixWord, tailWord_3231285, baseEnd_3231285] using wordTrace_append hprefix tailTrace_3231285
  have hstable : (prefixWord ++ tailWord_3231285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231285).length < 2 ^ (prefixWord ++ tailWord_3231285).sum := by decide
  have hdescent : baseEnd_3231285 < baseStart_3231285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231301 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 2, 4, 3]
def baseStart_3231301 : Nat := 118140960795 + 3231301 * 2 ^ 59
def prefixEnd_3231301 : Nat := 4983230072969 + 3 ^ 40 * 3231301 * 2
def baseEnd_3231301 : Nat := 1659210552353967253677023

theorem tailTrace_3231301 : CollatzResearch.WordTrace tailWord_3231301 prefixEnd_3231301 1659210552353967253677023 := by
  unfold tailWord_3231301
  simp only [CollatzResearch.WordTrace]
  refine ⟨117855229666555814119909757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78570153111037209413273171 117855229666555814119909757)
  ·
    refine ⟨44195711124958430294966159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117855229666555814119909757 44195711124958430294966159)
    ·
      refine ⟨66293566687437645442449239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44195711124958430294966159 66293566687437645442449239)
      ·
        refine ⟨99440350031156468163673859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66293566687437645442449239 99440350031156468163673859)
        ·
          refine ⟨149160525046734702245510789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99440350031156468163673859 149160525046734702245510789)
          ·
            refine ⟨27967598446262756671033273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149160525046734702245510789 27967598446262756671033273)
            ·
              refine ⟨20975698834697067503274955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27967598446262756671033273 20975698834697067503274955)
              ·
                refine ⟨31463548252045601254912433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20975698834697067503274955 31463548252045601254912433)
                ·
                  refine ⟨23597661189034200941184325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31463548252045601254912433 23597661189034200941184325)
                  ·
                    refine ⟨4424561472943912676472061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23597661189034200941184325 4424561472943912676472061)
                    ·
                      refine ⟨1659210552353967253677023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4424561472943912676472061 1659210552353967253677023)
                      ·
                        rfl

theorem cell23_3231301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_3231301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231301 prefixEnd_3231301 := by exact prefixLift 3231301
  have htrace : WordTrace (prefixWord ++ tailWord_3231301) baseStart_3231301 baseEnd_3231301 := by
    simpa [prefixWord, tailWord_3231301, baseEnd_3231301] using wordTrace_append hprefix tailTrace_3231301
  have hstable : (prefixWord ++ tailWord_3231301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231301).length < 2 ^ (prefixWord ++ tailWord_3231301).sum := by decide
  have hdescent : baseEnd_3231301 < baseStart_3231301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231349 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_3231349 : Nat := 118140960795 + 3231349 * 2 ^ 59
def prefixEnd_3231349 : Nat := 4983230072969 + 3 ^ 40 * 3231349 * 2
def baseEnd_3231349 : Nat := 1659235199425383065876803

theorem tailTrace_3231349 : CollatzResearch.WordTrace tailWord_3231349 prefixEnd_3231349 1659235199425383065876803 := by
  unfold tailWord_3231349
  simp only [CollatzResearch.WordTrace]
  refine ⟨117856980370381918317657101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78571320246921278878438067 117856980370381918317657101)
  ·
    refine ⟨44196367638893219369121413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117856980370381918317657101 44196367638893219369121413)
    ·
      refine ⟨8286818932292478631710265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44196367638893219369121413 8286818932292478631710265)
      ·
        refine ⟨6215114199219358973782699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8286818932292478631710265 6215114199219358973782699)
        ·
          refine ⟨9322671298829038460674049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215114199219358973782699 9322671298829038460674049)
          ·
            refine ⟨6992003474121778845505537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9322671298829038460674049 6992003474121778845505537)
            ·
              refine ⟨5244002605591334134129153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6992003474121778845505537 5244002605591334134129153)
              ·
                refine ⟨3933001954193500600596865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5244002605591334134129153 3933001954193500600596865)
                ·
                  refine ⟨2949751465645125450447649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3933001954193500600596865 2949751465645125450447649)
                  ·
                    refine ⟨2212313599233844087835737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2949751465645125450447649 2212313599233844087835737)
                    ·
                      refine ⟨1659235199425383065876803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212313599233844087835737 1659235199425383065876803)
                      ·
                        rfl

theorem cell23_3231349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_3231349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231349 prefixEnd_3231349 := by exact prefixLift 3231349
  have htrace : WordTrace (prefixWord ++ tailWord_3231349) baseStart_3231349 baseEnd_3231349 := by
    simpa [prefixWord, tailWord_3231349, baseEnd_3231349] using wordTrace_append hprefix tailTrace_3231349
  have hstable : (prefixWord ++ tailWord_3231349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231349).length < 2 ^ (prefixWord ++ tailWord_3231349).sum := by decide
  have hdescent : baseEnd_3231349 < baseStart_3231349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231371 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 4]
def baseStart_3231371 : Nat := 118140960795 + 3231371 * 2 ^ 59
def prefixEnd_3231371 : Nat := 4983230072969 + 3 ^ 40 * 3231371 * 2
def baseEnd_3231371 : Nat := 1659246495999781979801701

theorem tailTrace_3231371 : CollatzResearch.WordTrace tailWord_3231371 prefixEnd_3231371 1659246495999781979801701 := by
  unfold tailWord_3231371
  simp only [CollatzResearch.WordTrace]
  refine ⟨117857782776302216074957967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78571855184201477383305311 117857782776302216074957967)
  ·
    refine ⟨176786674164453324112436951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117857782776302216074957967 176786674164453324112436951)
    ·
      refine ⟨265180011246679986168655427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176786674164453324112436951 265180011246679986168655427)
      ·
        refine ⟨397770016870019979252983141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265180011246679986168655427 397770016870019979252983141)
        ·
          refine ⟨74581878163128746109934339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397770016870019979252983141 74581878163128746109934339)
          ·
            refine ⟨111872817244693119164901509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74581878163128746109934339 111872817244693119164901509)
            ·
              refine ⟨20976153233379959843419033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111872817244693119164901509 20976153233379959843419033)
              ·
                refine ⟨15732114925034969882564275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20976153233379959843419033 15732114925034969882564275)
                ·
                  refine ⟨23598172387552454823846413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15732114925034969882564275 23598172387552454823846413)
                  ·
                    refine ⟨8849314645332170558942405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23598172387552454823846413 8849314645332170558942405)
                    ·
                      refine ⟨1659246495999781979801701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8849314645332170558942405 1659246495999781979801701)
                      ·
                        rfl

theorem cell23_3231371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 4].length) (baseStart_3231371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231371 prefixEnd_3231371 := by exact prefixLift 3231371
  have htrace : WordTrace (prefixWord ++ tailWord_3231371) baseStart_3231371 baseEnd_3231371 := by
    simpa [prefixWord, tailWord_3231371, baseEnd_3231371] using wordTrace_append hprefix tailTrace_3231371
  have hstable : (prefixWord ++ tailWord_3231371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231371).length < 2 ^ (prefixWord ++ tailWord_3231371).sum := by decide
  have hdescent : baseEnd_3231371 < baseStart_3231371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231400 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_3231400 : Nat := 118140960795 + 3231400 * 2 ^ 59
def prefixEnd_3231400 : Nat := 4983230072969 + 3 ^ 40 * 3231400 * 2
def baseEnd_3231400 : Nat := 1659261386938762366339069

theorem tailTrace_3231400 : CollatzResearch.WordTrace tailWord_3231400 prefixEnd_3231400 1659261386938762366339069 := by
  unfold tailWord_3231400
  simp only [CollatzResearch.WordTrace]
  refine ⟨58929420246598577013881827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78572560328798102685175769 58929420246598577013881827)
  ·
    refine ⟨88394130369897865520822741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58929420246598577013881827 88394130369897865520822741)
    ·
      refine ⟨2071737430544481223144283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 88394130369897865520822741 2071737430544481223144283)
      ·
        refine ⟨3107606145816721834716425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2071737430544481223144283 3107606145816721834716425)
        ·
          refine ⟨2330704609362541376037319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3107606145816721834716425 2330704609362541376037319)
          ·
            refine ⟨3496056914043812064055979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2330704609362541376037319 3496056914043812064055979)
            ·
              refine ⟨5244085371065718096083969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496056914043812064055979 5244085371065718096083969)
              ·
                refine ⟨3933064028299288572062977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5244085371065718096083969 3933064028299288572062977)
                ·
                  refine ⟨2949798021224466429047233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3933064028299288572062977 2949798021224466429047233)
                  ·
                    refine ⟨2212348515918349821785425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2949798021224466429047233 2212348515918349821785425)
                    ·
                      refine ⟨1659261386938762366339069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212348515918349821785425 1659261386938762366339069)
                      ·
                        rfl

theorem cell23_3231400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_3231400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231400 prefixEnd_3231400 := by exact prefixLift 3231400
  have htrace : WordTrace (prefixWord ++ tailWord_3231400) baseStart_3231400 baseEnd_3231400 := by
    simpa [prefixWord, tailWord_3231400, baseEnd_3231400] using wordTrace_append hprefix tailTrace_3231400
  have hstable : (prefixWord ++ tailWord_3231400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231400).length < 2 ^ (prefixWord ++ tailWord_3231400).sum := by decide
  have hdescent : baseEnd_3231400 < baseStart_3231400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231405 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_3231405 : Nat := 118140960795 + 3231405 * 2 ^ 59
def prefixEnd_3231405 : Nat := 4983230072969 + 3 ^ 40 * 3231405 * 2
def baseEnd_3231405 : Nat := 1659263954342034846776545

theorem tailTrace_3231405 : CollatzResearch.WordTrace tailWord_3231405 prefixEnd_3231405 1659263954342034846776545 := by
  unfold tailWord_3231405
  simp only [CollatzResearch.WordTrace]
  refine ⟨117859022858179039881695669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78572681905452693254463779 117859022858179039881695669)
  ·
    refine ⟨11049283392954284988908969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117859022858179039881695669 11049283392954284988908969)
    ·
      refine ⟨8286962544715713741681727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11049283392954284988908969 8286962544715713741681727)
      ·
        refine ⟨12430443817073570612522591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8286962544715713741681727 12430443817073570612522591)
        ·
          refine ⟨18645665725610355918783887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12430443817073570612522591 18645665725610355918783887)
          ·
            refine ⟨27968498588415533878175831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18645665725610355918783887 27968498588415533878175831)
            ·
              refine ⟨41952747882623300817263747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27968498588415533878175831 41952747882623300817263747)
              ·
                refine ⟨62929121823934951225895621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41952747882623300817263747 62929121823934951225895621)
                ·
                  refine ⟨11799210341987803354855429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62929121823934951225895621 11799210341987803354855429)
                  ·
                    refine ⟨2212351939122713129035393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11799210341987803354855429 2212351939122713129035393)
                    ·
                      refine ⟨1659263954342034846776545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212351939122713129035393 1659263954342034846776545)
                      ·
                        rfl

theorem cell23_3231405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_3231405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231405 prefixEnd_3231405 := by exact prefixLift 3231405
  have htrace : WordTrace (prefixWord ++ tailWord_3231405) baseStart_3231405 baseEnd_3231405 := by
    simpa [prefixWord, tailWord_3231405, baseEnd_3231405] using wordTrace_append hprefix tailTrace_3231405
  have hstable : (prefixWord ++ tailWord_3231405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231405).length < 2 ^ (prefixWord ++ tailWord_3231405).sum := by decide
  have hdescent : baseEnd_3231405 < baseStart_3231405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231408 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 3]
def baseStart_3231408 : Nat := 118140960795 + 3231408 * 2 ^ 59
def prefixEnd_3231408 : Nat := 4983230072969 + 3 ^ 40 * 3231408 * 2
def baseEnd_3231408 : Nat := 1659265494783998335039031

theorem tailTrace_3231408 : CollatzResearch.WordTrace tailWord_3231408 prefixEnd_3231408 1659265494783998335039031 := by
  unfold tailWord_3231408
  simp only [CollatzResearch.WordTrace]
  refine ⟨58929566138584085697027439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78572754851445447596036585 58929566138584085697027439)
  ·
    refine ⟨88394349207876128545541159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58929566138584085697027439 88394349207876128545541159)
    ·
      refine ⟨132591523811814192818311739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88394349207876128545541159 132591523811814192818311739)
      ·
        refine ⟨198887285717721289227467609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132591523811814192818311739 198887285717721289227467609)
        ·
          refine ⟨149165464288290966920600707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198887285717721289227467609 149165464288290966920600707)
          ·
            refine ⟨223748196432436450380901061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149165464288290966920600707 223748196432436450380901061)
            ·
              refine ⟨41952786831081834446418949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223748196432436450380901061 41952786831081834446418949)
              ·
                refine ⟨7866147530827843958703553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41952786831081834446418949 7866147530827843958703553)
                ·
                  refine ⟨5899610648120882969027665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7866147530827843958703553 5899610648120882969027665)
                  ·
                    refine ⟨4424707986090662226770749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5899610648120882969027665 4424707986090662226770749)
                    ·
                      refine ⟨1659265494783998335039031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4424707986090662226770749 1659265494783998335039031)
                      ·
                        rfl

theorem cell23_3231408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 3].length) (baseStart_3231408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231408 prefixEnd_3231408 := by exact prefixLift 3231408
  have htrace : WordTrace (prefixWord ++ tailWord_3231408) baseStart_3231408 baseEnd_3231408 := by
    simpa [prefixWord, tailWord_3231408, baseEnd_3231408] using wordTrace_append hprefix tailTrace_3231408
  have hstable : (prefixWord ++ tailWord_3231408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231408).length < 2 ^ (prefixWord ++ tailWord_3231408).sum := by decide
  have hdescent : baseEnd_3231408 < baseStart_3231408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231411 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 8]
def baseStart_3231411 : Nat := 118140960795 + 3231411 * 2 ^ 59
def prefixEnd_3231411 : Nat := 4983230072969 + 3 ^ 40 * 3231411 * 2
def baseEnd_3231411 : Nat := 184363003913995758144613

theorem tailTrace_3231411 : CollatzResearch.WordTrace tailWord_3231411 prefixEnd_3231411 184363003913995758144613 := by
  unfold tailWord_3231411
  simp only [CollatzResearch.WordTrace]
  refine ⟨117859241696157302906414087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78572827797438201937609391 117859241696157302906414087)
  ·
    refine ⟨176788862544235954359621131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117859241696157302906414087 176788862544235954359621131)
    ·
      refine ⟨265183293816353931539431697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176788862544235954359621131 265183293816353931539431697)
      ·
        refine ⟨198887470362265448654573773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265183293816353931539431697 198887470362265448654573773)
        ·
          refine ⟨74582801385849543245465165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198887470362265448654573773 74582801385849543245465165)
          ·
            refine ⟨27968550519693578717049437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74582801385849543245465165 27968550519693578717049437)
            ·
              refine ⟨10488206444885092018893539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27968550519693578717049437 10488206444885092018893539)
              ·
                refine ⟨15732309667327638028340309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10488206444885092018893539 15732309667327638028340309)
                ·
                  refine ⟨184363003913995758144613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15732309667327638028340309 184363003913995758144613)
                  ·
                    rfl

theorem cell23_3231411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 8].length) (baseStart_3231411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231411 prefixEnd_3231411 := by exact prefixLift 3231411
  have htrace : WordTrace (prefixWord ++ tailWord_3231411) baseStart_3231411 baseEnd_3231411 := by
    simpa [prefixWord, tailWord_3231411, baseEnd_3231411] using wordTrace_append hprefix tailTrace_3231411
  have hstable : (prefixWord ++ tailWord_3231411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231411).length < 2 ^ (prefixWord ++ tailWord_3231411).sum := by decide
  have hdescent : baseEnd_3231411 < baseStart_3231411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231415 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 3, 4]
def baseStart_3231415 : Nat := 118140960795 + 3231415 * 2 ^ 59
def prefixEnd_3231415 : Nat := 4983230072969 + 3 ^ 40 * 3231415 * 2
def baseEnd_3231415 : Nat := 553089696382859935883833

theorem tailTrace_3231415 : CollatzResearch.WordTrace tailWord_3231415 prefixEnd_3231415 553089696382859935883833 := by
  unfold tailWord_3231415
  simp only [CollatzResearch.WordTrace]
  refine ⟨117859387588142811589559699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78572925058761874393039799 117859387588142811589559699)
  ·
    refine ⟨176789081382214217384339549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117859387588142811589559699 176789081382214217384339549)
    ·
      refine ⟨66295905518330331519127331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176789081382214217384339549 66295905518330331519127331)
      ·
        refine ⟨99443858277495497278690997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66295905518330331519127331 99443858277495497278690997)
        ·
          refine ⟨9322861713515202869877281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99443858277495497278690997 9322861713515202869877281)
          ·
            refine ⟨6992146285136402152407961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9322861713515202869877281 6992146285136402152407961)
            ·
              refine ⟨5244109713852301614305971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6992146285136402152407961 5244109713852301614305971)
              ·
                refine ⟨7866164570778452421458957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5244109713852301614305971 7866164570778452421458957)
                ·
                  refine ⟨2949811714041919658047109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7866164570778452421458957 2949811714041919658047109)
                  ·
                    refine ⟨553089696382859935883833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2949811714041919658047109 553089696382859935883833)
                    ·
                      rfl

theorem cell23_3231415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_3231415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231415 prefixEnd_3231415 := by exact prefixLift 3231415
  have htrace : WordTrace (prefixWord ++ tailWord_3231415) baseStart_3231415 baseEnd_3231415 := by
    simpa [prefixWord, tailWord_3231415, baseEnd_3231415] using wordTrace_append hprefix tailTrace_3231415
  have hstable : (prefixWord ++ tailWord_3231415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231415).length < 2 ^ (prefixWord ++ tailWord_3231415).sum := by decide
  have hdescent : baseEnd_3231415 < baseStart_3231415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231431 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_3231431 : Nat := 118140960795 + 3231431 * 2 ^ 59
def prefixEnd_3231431 : Nat := 4983230072969 + 3 ^ 40 * 3231431 * 2
def baseEnd_3231431 : Nat := 1659277304839051745051425

theorem tailTrace_3231431 : CollatzResearch.WordTrace tailWord_3231431 prefixEnd_3231431 1659277304839051745051425 := by
  unfold tailWord_3231431
  simp only [CollatzResearch.WordTrace]
  refine ⟨117859971156084846322142147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78573314104056564214761431 117859971156084846322142147)
  ·
    refine ⟨176789956734127269483213221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117859971156084846322142147 176789956734127269483213221)
    ·
      refine ⟨33148116887648863028102479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176789956734127269483213221 33148116887648863028102479)
      ·
        refine ⟨49722175331473294542153719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33148116887648863028102479 49722175331473294542153719)
        ·
          refine ⟨74583262997209941813230579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49722175331473294542153719 74583262997209941813230579)
          ·
            refine ⟨111874894495814912719845869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74583262997209941813230579 111874894495814912719845869)
            ·
              refine ⟨41953085435930592269942201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111874894495814912719845869 41953085435930592269942201)
              ·
                refine ⟨31464814076947944202456651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41953085435930592269942201 31464814076947944202456651)
                ·
                  refine ⟨47197221115421916303684977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31464814076947944202456651 47197221115421916303684977)
                  ·
                    refine ⟨35397915836566437227763733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47197221115421916303684977 35397915836566437227763733)
                    ·
                      refine ⟨1659277304839051745051425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35397915836566437227763733 1659277304839051745051425)
                      ·
                        rfl

theorem cell23_3231431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_3231431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231431 prefixEnd_3231431 := by exact prefixLift 3231431
  have htrace : WordTrace (prefixWord ++ tailWord_3231431) baseStart_3231431 baseEnd_3231431 := by
    simpa [prefixWord, tailWord_3231431, baseEnd_3231431] using wordTrace_append hprefix tailTrace_3231431
  have hstable : (prefixWord ++ tailWord_3231431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231431).length < 2 ^ (prefixWord ++ tailWord_3231431).sum := by decide
  have hdescent : baseEnd_3231431 < baseStart_3231431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231438 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_3231438 : Nat := 118140960795 + 3231438 * 2 ^ 59
def prefixEnd_3231438 : Nat := 4983230072969 + 3 ^ 40 * 3231438 * 2
def baseEnd_3231438 : Nat := 1659280899203633217663893

theorem tailTrace_3231438 : CollatzResearch.WordTrace tailWord_3231438 prefixEnd_3231438 1659280899203633217663893 := by
  unfold tailWord_3231438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14732528308382435814705871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78573484311372991011764645 14732528308382435814705871)
  ·
    refine ⟨22098792462573653722058807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14732528308382435814705871 22098792462573653722058807)
    ·
      refine ⟨33148188693860480583088211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22098792462573653722058807 33148188693860480583088211)
      ·
        refine ⟨49722283040790720874632317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33148188693860480583088211 49722283040790720874632317)
        ·
          refine ⟨18645856140296520327987119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49722283040790720874632317 18645856140296520327987119)
          ·
            refine ⟨27968784210444780491980679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18645856140296520327987119 27968784210444780491980679)
            ·
              refine ⟨41953176315667170737971019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27968784210444780491980679 41953176315667170737971019)
              ·
                refine ⟨62929764473500756106956529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41953176315667170737971019 62929764473500756106956529)
                ·
                  refine ⟨47197323355125567080217397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62929764473500756106956529 47197323355125567080217397)
                  ·
                    refine ⟨4424749064543021913770381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47197323355125567080217397 4424749064543021913770381)
                    ·
                      refine ⟨1659280899203633217663893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4424749064543021913770381 1659280899203633217663893)
                      ·
                        rfl

theorem cell23_3231438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_3231438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231438 prefixEnd_3231438 := by exact prefixLift 3231438
  have htrace : WordTrace (prefixWord ++ tailWord_3231438) baseStart_3231438 baseEnd_3231438 := by
    simpa [prefixWord, tailWord_3231438, baseEnd_3231438] using wordTrace_append hprefix tailTrace_3231438
  have hstable : (prefixWord ++ tailWord_3231438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231438).length < 2 ^ (prefixWord ++ tailWord_3231438).sum := by decide
  have hdescent : baseEnd_3231438 < baseStart_3231438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231492 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_3231492 : Nat := 118140960795 + 3231492 * 2 ^ 59
def prefixEnd_3231492 : Nat := 4983230072969 + 3 ^ 40 * 3231492 * 2
def baseEnd_3231492 : Nat := 553102875719658668796215

theorem tailTrace_3231492 : CollatzResearch.WordTrace tailWord_3231492 prefixEnd_3231492 553102875719658668796215 := by
  unfold tailWord_3231492
  simp only [CollatzResearch.WordTrace]
  refine ⟨58931098004431926870056365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78574797339242569160075153 58931098004431926870056365)
  ·
    refine ⟨22099161751661972576271137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58931098004431926870056365 22099161751661972576271137)
    ·
      refine ⟨16574371313746479432203353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22099161751661972576271137 16574371313746479432203353)
      ·
        refine ⟨12430778485309859574152515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16574371313746479432203353 12430778485309859574152515)
        ·
          refine ⟨18646167727964789361228773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12430778485309859574152515 18646167727964789361228773)
          ·
            refine ⟨3496156448993398005230395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18646167727964789361228773 3496156448993398005230395)
            ·
              refine ⟨5244234673490097007845593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496156448993398005230395 5244234673490097007845593)
              ·
                refine ⟨3933176005117572755884195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5244234673490097007845593 3933176005117572755884195)
                ·
                  refine ⟨5899764007676359133826293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933176005117572755884195 5899764007676359133826293)
                  ·
                    refine ⟨553102875719658668796215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5899764007676359133826293 553102875719658668796215)
                    ·
                      rfl

theorem cell23_3231492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_3231492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231492 prefixEnd_3231492 := by exact prefixLift 3231492
  have htrace : WordTrace (prefixWord ++ tailWord_3231492) baseStart_3231492 baseEnd_3231492 := by
    simpa [prefixWord, tailWord_3231492, baseEnd_3231492] using wordTrace_append hprefix tailTrace_3231492
  have hstable : (prefixWord ++ tailWord_3231492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231492).length < 2 ^ (prefixWord ++ tailWord_3231492).sum := by decide
  have hdescent : baseEnd_3231492 < baseStart_3231492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231522 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3231522 : Nat := 118140960795 + 3231522 * 2 ^ 59
def prefixEnd_3231522 : Nat := 4983230072969 + 3 ^ 40 * 3231522 * 2
def baseEnd_3231522 : Nat := 553108010526203629671169

theorem tailTrace_3231522 : CollatzResearch.WordTrace tailWord_3231522 prefixEnd_3231522 553108010526203629671169 := by
  unfold tailWord_3231522
  simp only [CollatzResearch.WordTrace]
  refine ⟨29465822549688792215926205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78575526799170112575803213 29465822549688792215926205)
  ·
    refine ⟨11049683456133297080972327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29465822549688792215926205 11049683456133297080972327)
    ·
      refine ⟨16574525184199945621458491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11049683456133297080972327 16574525184199945621458491)
      ·
        refine ⟨24861787776299918432187737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16574525184199945621458491 24861787776299918432187737)
        ·
          refine ⟨18646340832224938824140803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24861787776299918432187737 18646340832224938824140803)
          ·
            refine ⟨27969511248337408236211205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18646340832224938824140803 27969511248337408236211205)
            ·
              refine ⟨5244283359063264044289601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27969511248337408236211205 5244283359063264044289601)
              ·
                refine ⟨3933212519297448033217201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5244283359063264044289601 3933212519297448033217201)
                ·
                  refine ⟨2949909389473086024912901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3933212519297448033217201 2949909389473086024912901)
                  ·
                    refine ⟨553108010526203629671169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2949909389473086024912901 553108010526203629671169)
                    ·
                      rfl

theorem cell23_3231522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3231522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231522 prefixEnd_3231522 := by exact prefixLift 3231522
  have htrace : WordTrace (prefixWord ++ tailWord_3231522) baseStart_3231522 baseEnd_3231522 := by
    simpa [prefixWord, tailWord_3231522, baseEnd_3231522] using wordTrace_append hprefix tailTrace_3231522
  have hstable : (prefixWord ++ tailWord_3231522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231522).length < 2 ^ (prefixWord ++ tailWord_3231522).sum := by decide
  have hdescent : baseEnd_3231522 < baseStart_3231522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231542 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3231542 : Nat := 118140960795 + 3231542 * 2 ^ 59
def prefixEnd_3231542 : Nat := 4983230072969 + 3 ^ 40 * 3231542 * 2
def baseEnd_3231542 : Nat := 1659334301191700810763415

theorem tailTrace_3231542 : CollatzResearch.WordTrace tailWord_3231542 prefixEnd_3231542 1659334301191700810763415 := by
  unfold tailWord_3231542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7366501228667669517464555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78576013105788474852955253 7366501228667669517464555)
  ·
    refine ⟨11049751843001504276196833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7366501228667669517464555 11049751843001504276196833)
    ·
      refine ⟨8287313882251128207147625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11049751843001504276196833 8287313882251128207147625)
      ·
        refine ⟨6215485411688346155360719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8287313882251128207147625 6215485411688346155360719)
        ·
          refine ⟨9323228117532519233041079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215485411688346155360719 9323228117532519233041079)
          ·
            refine ⟨13984842176298778849561619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9323228117532519233041079 13984842176298778849561619)
            ·
              refine ⟨20977263264448168274342429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13984842176298778849561619 20977263264448168274342429)
              ·
                refine ⟨7866473724168063102878411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20977263264448168274342429 7866473724168063102878411)
                ·
                  refine ⟨11799710586252094654317617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7866473724168063102878411 11799710586252094654317617)
                  ·
                    refine ⟨8849782939689070990738213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11799710586252094654317617 8849782939689070990738213)
                    ·
                      refine ⟨1659334301191700810763415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8849782939689070990738213 1659334301191700810763415)
                      ·
                        rfl

theorem cell23_3231542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3231542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231542 prefixEnd_3231542 := by exact prefixLift 3231542
  have htrace : WordTrace (prefixWord ++ tailWord_3231542) baseStart_3231542 baseEnd_3231542 := by
    simpa [prefixWord, tailWord_3231542, baseEnd_3231542] using wordTrace_append hprefix tailTrace_3231542
  have hstable : (prefixWord ++ tailWord_3231542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231542).length < 2 ^ (prefixWord ++ tailWord_3231542).sum := by decide
  have hdescent : baseEnd_3231542 < baseStart_3231542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231578 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_3231578 : Nat := 118140960795 + 3231578 * 2 ^ 59
def prefixEnd_3231578 : Nat := 4983230072969 + 3 ^ 40 * 3231578 * 2
def baseEnd_3231578 : Nat := 553117595498420889971083

theorem tailTrace_3231578 : CollatzResearch.WordTrace tailWord_3231578 prefixEnd_3231578 553117595498420889971083 := by
  unfold tailWord_3231578
  simp only [CollatzResearch.WordTrace]
  refine ⟨29466333171638072606935847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78576888457701526951828925 29466333171638072606935847)
  ·
    refine ⟨44199499757457108910403771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29466333171638072606935847 44199499757457108910403771)
    ·
      refine ⟨66299249636185663365605657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44199499757457108910403771 66299249636185663365605657)
      ·
        refine ⟨49724437227139247524204243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66299249636185663365605657 49724437227139247524204243)
        ·
          refine ⟨74586655840708871286306365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49724437227139247524204243 74586655840708871286306365)
          ·
            refine ⟨27969995940265826732364887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74586655840708871286306365 27969995940265826732364887)
            ·
              refine ⟨41954993910398740098547331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27969995940265826732364887 41954993910398740098547331)
              ·
                refine ⟨62932490865598110147820997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41954993910398740098547331 62932490865598110147820997)
                ·
                  refine ⟨11799842037299645652716437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62932490865598110147820997 11799842037299645652716437)
                  ·
                    refine ⟨553117595498420889971083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11799842037299645652716437 553117595498420889971083)
                    ·
                      rfl

theorem cell23_3231578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_3231578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231578 prefixEnd_3231578 := by exact prefixLift 3231578
  have htrace : WordTrace (prefixWord ++ tailWord_3231578) baseStart_3231578 baseEnd_3231578 := by
    simpa [prefixWord, tailWord_3231578, baseEnd_3231578] using wordTrace_append hprefix tailTrace_3231578
  have hstable : (prefixWord ++ tailWord_3231578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231578).length < 2 ^ (prefixWord ++ tailWord_3231578).sum := by decide
  have hdescent : baseEnd_3231578 < baseStart_3231578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231605 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3231605 : Nat := 118140960795 + 3231605 * 2 ^ 59
def prefixEnd_3231605 : Nat := 4983230072969 + 3 ^ 40 * 3231605 * 2
def baseEnd_3231605 : Nat := 1659366650472934064275625

theorem tailTrace_3231605 : CollatzResearch.WordTrace tailWord_3231605 prefixEnd_3231605 1659366650472934064275625 := by
  unfold tailWord_3231605
  simp only [CollatzResearch.WordTrace]
  refine ⟨117866317457454474038976269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78577544971636316025984179 117866317457454474038976269)
  ·
    refine ⟨44199869046545427764616101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117866317457454474038976269 44199869046545427764616101)
    ·
      refine ⟨8287475446227267705865519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44199869046545427764616101 8287475446227267705865519)
      ·
        refine ⟨12431213169340901558798279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8287475446227267705865519 12431213169340901558798279)
        ·
          refine ⟨18646819754011352338197419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12431213169340901558798279 18646819754011352338197419)
          ·
            refine ⟨27970229631017028507296129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18646819754011352338197419 27970229631017028507296129)
            ·
              refine ⟨20977672223262771380472097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27970229631017028507296129 20977672223262771380472097)
              ·
                refine ⟨15733254167447078535354073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20977672223262771380472097 15733254167447078535354073)
                ·
                  refine ⟨11799940625585308901515555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15733254167447078535354073 11799940625585308901515555)
                  ·
                    refine ⟨17699910938377963352273333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11799940625585308901515555 17699910938377963352273333)
                    ·
                      refine ⟨1659366650472934064275625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17699910938377963352273333 1659366650472934064275625)
                      ·
                        rfl

theorem cell23_3231605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3231605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231605 prefixEnd_3231605 := by exact prefixLift 3231605
  have htrace : WordTrace (prefixWord ++ tailWord_3231605) baseStart_3231605 baseEnd_3231605 := by
    simpa [prefixWord, tailWord_3231605, baseEnd_3231605] using wordTrace_append hprefix tailTrace_3231605
  have hstable : (prefixWord ++ tailWord_3231605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231605).length < 2 ^ (prefixWord ++ tailWord_3231605).sum := by decide
  have hdescent : baseEnd_3231605 < baseStart_3231605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231642 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 7]
def baseStart_3231642 : Nat := 118140960795 + 3231642 * 2 ^ 59
def prefixEnd_3231642 : Nat := 4983230072969 + 3 ^ 40 * 3231642 * 2
def baseEnd_3231642 : Nat := 184376183250794491056995

theorem tailTrace_3231642 : CollatzResearch.WordTrace tailWord_3231642 prefixEnd_3231642 184376183250794491056995 := by
  unfold tailWord_3231642
  simp only [CollatzResearch.WordTrace]
  refine ⟨29466916739580107339518295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78578444638880286238715453 29466916739580107339518295)
  ·
    refine ⟨44200375109370161009277443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29466916739580107339518295 44200375109370161009277443)
    ·
      refine ⟨66300562664055241513916165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44200375109370161009277443 66300562664055241513916165)
      ·
        refine ⟨12431355499510357783859281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66300562664055241513916165 12431355499510357783859281)
        ·
          refine ⟨9323516624632768337894461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12431355499510357783859281 9323516624632768337894461)
          ·
            refine ⟨3496318734237288126710423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9323516624632768337894461 3496318734237288126710423)
            ·
              refine ⟨5244478101355932190065635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496318734237288126710423 5244478101355932190065635)
              ·
                refine ⟨7866717152033898285098453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5244478101355932190065635 7866717152033898285098453)
                ·
                  refine ⟨184376183250794491056995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7866717152033898285098453 184376183250794491056995)
                  ·
                    rfl

theorem cell23_3231642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_3231642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231642 prefixEnd_3231642 := by exact prefixLift 3231642
  have htrace : WordTrace (prefixWord ++ tailWord_3231642) baseStart_3231642 baseEnd_3231642 := by
    simpa [prefixWord, tailWord_3231642, baseEnd_3231642] using wordTrace_append hprefix tailTrace_3231642
  have hstable : (prefixWord ++ tailWord_3231642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231642).length < 2 ^ (prefixWord ++ tailWord_3231642).sum := by decide
  have hdescent : baseEnd_3231642 < baseStart_3231642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231675 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 4]
def baseStart_3231675 : Nat := 118140960795 + 3231675 * 2 ^ 59
def prefixEnd_3231675 : Nat := 4983230072969 + 3 ^ 40 * 3231675 * 2
def baseEnd_3231675 : Nat := 1659402594118748790400303

theorem tailTrace_3231675 : CollatzResearch.WordTrace tailWord_3231675 prefixEnd_3231675 1659402594118748790400303 := by
  unfold tailWord_3231675
  simp only [CollatzResearch.WordTrace]
  refine ⟨117868870567200875994024479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78579247044800583996016319 117868870567200875994024479)
  ·
    refine ⟨176803305850801313991036719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117868870567200875994024479 176803305850801313991036719)
    ·
      refine ⟨265204958776201970986555079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176803305850801313991036719 265204958776201970986555079)
      ·
        refine ⟨397807438164302956479832619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265204958776201970986555079 397807438164302956479832619)
        ·
          refine ⟨596711157246454434719748929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397807438164302956479832619 596711157246454434719748929)
          ·
            refine ⟨447533367934840826039811697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596711157246454434719748929 447533367934840826039811697)
            ·
              refine ⟨335650025951130619529858773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447533367934840826039811697 335650025951130619529858773)
              ·
                refine ⟨7866797483229623895231065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 335650025951130619529858773 7866797483229623895231065)
                ·
                  refine ⟨5900098112422217921423299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7866797483229623895231065 5900098112422217921423299)
                  ·
                    refine ⟨8850147168633326882134949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5900098112422217921423299 8850147168633326882134949)
                    ·
                      refine ⟨1659402594118748790400303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8850147168633326882134949 1659402594118748790400303)
                      ·
                        rfl

theorem cell23_3231675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 4].length) (baseStart_3231675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231675 prefixEnd_3231675 := by exact prefixLift 3231675
  have htrace : WordTrace (prefixWord ++ tailWord_3231675) baseStart_3231675 baseEnd_3231675 := by
    simpa [prefixWord, tailWord_3231675, baseEnd_3231675] using wordTrace_append hprefix tailTrace_3231675
  have hstable : (prefixWord ++ tailWord_3231675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231675).length < 2 ^ (prefixWord ++ tailWord_3231675).sum := by decide
  have hdescent : baseEnd_3231675 < baseStart_3231675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231685 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 7, 4]
def baseStart_3231685 : Nat := 118140960795 + 3231685 * 2 ^ 59
def prefixEnd_3231685 : Nat := 4983230072969 + 3 ^ 40 * 3231685 * 2
def baseEnd_3231685 : Nat := 553135909641764583758419

theorem tailTrace_3231685 : CollatzResearch.WordTrace tailWord_3231685 prefixEnd_3231685 553135909641764583758419 := by
  unfold tailWord_3231685
  simp only [CollatzResearch.WordTrace]
  refine ⟨117869235297164647701888509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78579490198109765134592339 117869235297164647701888509)
  ·
    refine ⟨44200963236436742888208191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117869235297164647701888509 44200963236436742888208191)
    ·
      refine ⟨66301444854655114332312287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44200963236436742888208191 66301444854655114332312287)
      ·
        refine ⟨99452167281982671498468431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66301444854655114332312287 99452167281982671498468431)
        ·
          refine ⟨149178250922974007247702647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99452167281982671498468431 149178250922974007247702647)
          ·
            refine ⟨223767376384461010871553971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149178250922974007247702647 223767376384461010871553971)
            ·
              refine ⟨335651064576691516307330957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223767376384461010871553971 335651064576691516307330957)
              ·
                refine ⟨125869149216259318615249109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335651064576691516307330957 125869149216259318615249109)
                ·
                  refine ⟨2950058184756077780044901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 125869149216259318615249109 2950058184756077780044901)
                  ·
                    refine ⟨553135909641764583758419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2950058184756077780044901 553135909641764583758419)
                    ·
                      rfl

theorem cell23_3231685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_3231685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231685 prefixEnd_3231685 := by exact prefixLift 3231685
  have htrace : WordTrace (prefixWord ++ tailWord_3231685) baseStart_3231685 baseEnd_3231685 := by
    simpa [prefixWord, tailWord_3231685, baseEnd_3231685] using wordTrace_append hprefix tailTrace_3231685
  have hstable : (prefixWord ++ tailWord_3231685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231685).length < 2 ^ (prefixWord ++ tailWord_3231685).sum := by decide
  have hdescent : baseEnd_3231685 < baseStart_3231685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231692 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3231692 : Nat := 118140960795 + 3231692 * 2 ^ 59
def prefixEnd_3231692 : Nat := 4983230072969 + 3 ^ 40 * 3231692 * 2
def baseEnd_3231692 : Nat := 1659411323289875223887725

theorem tailTrace_3231692 : CollatzResearch.WordTrace tailWord_3231692 prefixEnd_3231692 1659411323289875223887725 := by
  unfold tailWord_3231692
  simp only [CollatzResearch.WordTrace]
  refine ⟨58934745304069643948696665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78579660405426191931595553 58934745304069643948696665)
  ·
    refine ⟨44201058978052232961522499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58934745304069643948696665 44201058978052232961522499)
    ·
      refine ⟨66301588467078349442283749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44201058978052232961522499 66301588467078349442283749)
      ·
        refine ⟨12431547837577190520428203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66301588467078349442283749 12431547837577190520428203)
        ·
          refine ⟨18647321756365785780642305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12431547837577190520428203 18647321756365785780642305)
          ·
            refine ⟨13985491317274339335481729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18647321756365785780642305 13985491317274339335481729)
            ·
              refine ⟨10489118487955754501611297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13985491317274339335481729 10489118487955754501611297)
              ·
                refine ⟨7866838865966815876208473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10489118487955754501611297 7866838865966815876208473)
                ·
                  refine ⟨5900129149475111907156355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7866838865966815876208473 5900129149475111907156355)
                  ·
                    refine ⟨8850193724212667860734533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5900129149475111907156355 8850193724212667860734533)
                    ·
                      refine ⟨1659411323289875223887725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8850193724212667860734533 1659411323289875223887725)
                      ·
                        rfl

theorem cell23_3231692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3231692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231692 prefixEnd_3231692 := by exact prefixLift 3231692
  have htrace : WordTrace (prefixWord ++ tailWord_3231692) baseStart_3231692 baseEnd_3231692 := by
    simpa [prefixWord, tailWord_3231692, baseEnd_3231692] using wordTrace_append hprefix tailTrace_3231692
  have hstable : (prefixWord ++ tailWord_3231692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231692).length < 2 ^ (prefixWord ++ tailWord_3231692).sum := by decide
  have hdescent : baseEnd_3231692 < baseStart_3231692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231719 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 3, 4]
def baseStart_3231719 : Nat := 118140960795 + 3231719 * 2 ^ 59
def prefixEnd_3231719 : Nat := 4983230072969 + 3 ^ 40 * 3231719 * 2
def baseEnd_3231719 : Nat := 553141729089182206083367

theorem tailTrace_3231719 : CollatzResearch.WordTrace tailWord_3231719 prefixEnd_3231719 553141729089182206083367 := by
  unfold tailWord_3231719
  simp only [CollatzResearch.WordTrace]
  refine ⟨117870475379041471508626211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78580316919360981005750807 117870475379041471508626211)
  ·
    refine ⟨176805713068562207262939317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117870475379041471508626211 176805713068562207262939317)
    ·
      refine ⟨16575535600177706930900561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176805713068562207262939317 16575535600177706930900561)
      ·
        refine ⟨12431651700133280198175421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16575535600177706930900561 12431651700133280198175421)
        ·
          refine ⟨4661869387549980074315783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12431651700133280198175421 4661869387549980074315783)
          ·
            refine ⟨6992804081324970111473675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4661869387549980074315783 6992804081324970111473675)
            ·
              refine ⟨10489206121987455167210513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6992804081324970111473675 10489206121987455167210513)
              ·
                refine ⟨7866904591490591375407885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10489206121987455167210513 7866904591490591375407885)
                ·
                  refine ⟨2950089221808971765777957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7866904591490591375407885 2950089221808971765777957)
                  ·
                    refine ⟨553141729089182206083367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2950089221808971765777957 553141729089182206083367)
                    ·
                      rfl

theorem cell23_3231719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_3231719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231719 prefixEnd_3231719 := by exact prefixLift 3231719
  have htrace : WordTrace (prefixWord ++ tailWord_3231719) baseStart_3231719 baseEnd_3231719 := by
    simpa [prefixWord, tailWord_3231719, baseEnd_3231719] using wordTrace_append hprefix tailTrace_3231719
  have hstable : (prefixWord ++ tailWord_3231719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231719).length < 2 ^ (prefixWord ++ tailWord_3231719).sum := by decide
  have hdescent : baseEnd_3231719 < baseStart_3231719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231792 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 4, 4]
def baseStart_3231792 : Nat := 118140960795 + 3231792 * 2 ^ 59
def prefixEnd_3231792 : Nat := 4983230072969 + 3 ^ 40 * 3231792 * 2
def baseEnd_3231792 : Nat := 553154223785108277545755

theorem tailTrace_3231792 : CollatzResearch.WordTrace tailWord_3231792 prefixEnd_3231792 553154223785108277545755 := by
  unfold tailWord_3231792
  simp only [CollatzResearch.WordTrace]
  refine ⟨58936568953888502488016815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78582091938518003317355753 58936568953888502488016815)
  ·
    refine ⟨88404853430832753732025223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58936568953888502488016815 88404853430832753732025223)
    ·
      refine ⟨132607280146249130598037835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88404853430832753732025223 132607280146249130598037835)
      ·
        refine ⟨198910920219373695897056753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132607280146249130598037835 198910920219373695897056753)
        ·
          refine ⟨149183190164530271922792565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198910920219373695897056753 149183190164530271922792565)
          ·
            refine ⟨13985924077924712992761803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149183190164530271922792565 13985924077924712992761803)
            ·
              refine ⟨20978886116887069489142705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13985924077924712992761803 20978886116887069489142705)
              ·
                refine ⟨15734164587665302116857029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20978886116887069489142705 15734164587665302116857029)
                ·
                  refine ⟨2950155860187244146910693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15734164587665302116857029 2950155860187244146910693)
                  ·
                    refine ⟨553154223785108277545755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2950155860187244146910693 553154223785108277545755)
                    ·
                      rfl

theorem cell23_3231792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4, 4].length) (baseStart_3231792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231792 prefixEnd_3231792 := by exact prefixLift 3231792
  have htrace : WordTrace (prefixWord ++ tailWord_3231792) baseStart_3231792 baseEnd_3231792 := by
    simpa [prefixWord, tailWord_3231792, baseEnd_3231792] using wordTrace_append hprefix tailTrace_3231792
  have hstable : (prefixWord ++ tailWord_3231792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231792).length < 2 ^ (prefixWord ++ tailWord_3231792).sum := by decide
  have hdescent : baseEnd_3231792 < baseStart_3231792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231793 : List Nat := [1, 2, 2, 3, 1, 5, 1, 3, 1, 1, 3]
def baseStart_3231793 : Nat := 118140960795 + 3231793 * 2 ^ 59
def prefixEnd_3231793 : Nat := 4983230072969 + 3 ^ 40 * 3231793 * 2
def baseEnd_3231793 : Nat := 1659463184835979328724761

theorem tailTrace_3231793 : CollatzResearch.WordTrace tailWord_3231793 prefixEnd_3231793 1659463184835979328724761 := by
  unfold tailWord_3231793
  simp only [CollatzResearch.WordTrace]
  refine ⟨117873174380773382146820033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78582116253848921431213355 117873174380773382146820033)
  ·
    refine ⟨88404880785580036610115025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117873174380773382146820033 88404880785580036610115025)
    ·
      refine ⟨66303660589185027457586269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88404880785580036610115025 66303660589185027457586269)
      ·
        refine ⟨24863872720944385296594851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66303660589185027457586269 24863872720944385296594851)
        ·
          refine ⟨37295809081416577944892277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24863872720944385296594851 37295809081416577944892277)
          ·
            refine ⟨3496482101382804182333651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37295809081416577944892277 3496482101382804182333651)
            ·
              refine ⟨5244723152074206273500477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496482101382804182333651 5244723152074206273500477)
              ·
                refine ⟨1966771182027827352562679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5244723152074206273500477 1966771182027827352562679)
                ·
                  refine ⟨2950156773041741028844019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966771182027827352562679 2950156773041741028844019)
                  ·
                    refine ⟨4425235159562611543266029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2950156773041741028844019 4425235159562611543266029)
                    ·
                      refine ⟨1659463184835979328724761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4425235159562611543266029 1659463184835979328724761)
                      ·
                        rfl

theorem cell23_3231793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_3231793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231793 prefixEnd_3231793 := by exact prefixLift 3231793
  have htrace : WordTrace (prefixWord ++ tailWord_3231793) baseStart_3231793 baseEnd_3231793 := by
    simpa [prefixWord, tailWord_3231793, baseEnd_3231793] using wordTrace_append hprefix tailTrace_3231793
  have hstable : (prefixWord ++ tailWord_3231793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231793).length < 2 ^ (prefixWord ++ tailWord_3231793).sum := by decide
  have hdescent : baseEnd_3231793 < baseStart_3231793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231799 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 5, 2, 2]
def baseStart_3231799 : Nat := 118140960795 + 3231799 * 2 ^ 59
def prefixEnd_3231799 : Nat := 4983230072969 + 3 ^ 40 * 3231799 * 2
def baseEnd_3231799 : Nat := 1659466265719906305249733

theorem tailTrace_3231799 : CollatzResearch.WordTrace tailWord_3231799 prefixEnd_3231799 1659466265719906305249733 := by
  unfold tailWord_3231799
  simp only [CollatzResearch.WordTrace]
  refine ⟨117873393218751645171538451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78582262145834430114358967 117873393218751645171538451)
  ·
    refine ⟨176810089828127467757307677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117873393218751645171538451 176810089828127467757307677)
    ·
      refine ⟨66303783685547800408990379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176810089828127467757307677 66303783685547800408990379)
      ·
        refine ⟨99455675528321700613485569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66303783685547800408990379 99455675528321700613485569)
        ·
          refine ⟨74591756646241275460114177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99455675528321700613485569 74591756646241275460114177)
          ·
            refine ⟨55943817484680956595085633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74591756646241275460114177 55943817484680956595085633)
            ·
              refine ⟨41957863113510717446314225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55943817484680956595085633 41957863113510717446314225)
              ·
                refine ⟨31468397335133038084735669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41957863113510717446314225 31468397335133038084735669)
                ·
                  refine ⟨2950162250168722320443969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31468397335133038084735669 2950162250168722320443969)
                  ·
                    refine ⟨2212621687626541740332977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2950162250168722320443969 2212621687626541740332977)
                    ·
                      refine ⟨1659466265719906305249733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212621687626541740332977 1659466265719906305249733)
                      ·
                        rfl

theorem cell23_3231799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 2, 2].length) (baseStart_3231799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231799 prefixEnd_3231799 := by exact prefixLift 3231799
  have htrace : WordTrace (prefixWord ++ tailWord_3231799) baseStart_3231799 baseEnd_3231799 := by
    simpa [prefixWord, tailWord_3231799, baseEnd_3231799] using wordTrace_append hprefix tailTrace_3231799
  have hstable : (prefixWord ++ tailWord_3231799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231799).length < 2 ^ (prefixWord ++ tailWord_3231799).sum := by decide
  have hdescent : baseEnd_3231799 < baseStart_3231799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231802 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3]
def baseStart_3231802 : Nat := 118140960795 + 3231802 * 2 ^ 59
def prefixEnd_3231802 : Nat := 4983230072969 + 3 ^ 40 * 3231802 * 2
def baseEnd_3231802 : Nat := 1659467806161869793512219

theorem tailTrace_3231802 : CollatzResearch.WordTrace tailWord_3231802 prefixEnd_3231802 1659467806161869793512219 := by
  unfold tailWord_3231802
  simp only [CollatzResearch.WordTrace]
  refine ⟨29468375659435194170974415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78582335091827184455931773 29468375659435194170974415)
  ·
    refine ⟨44202563489152791256461623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29468375659435194170974415 44202563489152791256461623)
    ·
      refine ⟨66303845233729186884692435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44202563489152791256461623 66303845233729186884692435)
      ·
        refine ⟨99455767850593780327038653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66303845233729186884692435 99455767850593780327038653)
        ·
          refine ⟨37295912943972667622639495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99455767850593780327038653 37295912943972667622639495)
          ·
            refine ⟨55943869415959001433959243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37295912943972667622639495 55943869415959001433959243)
            ·
              refine ⟨83915804123938502150938865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55943869415959001433959243 83915804123938502150938865)
              ·
                refine ⟨62936853092953876613204149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83915804123938502150938865 62936853092953876613204149)
                ·
                  refine ⟨5900329977464425932487889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62936853092953876613204149 5900329977464425932487889)
                  ·
                    refine ⟨4425247483098319449365917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5900329977464425932487889 4425247483098319449365917)
                    ·
                      refine ⟨1659467806161869793512219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4425247483098319449365917 1659467806161869793512219)
                      ·
                        rfl

theorem cell23_3231802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_3231802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231802 prefixEnd_3231802 := by exact prefixLift 3231802
  have htrace : WordTrace (prefixWord ++ tailWord_3231802) baseStart_3231802 baseEnd_3231802 := by
    simpa [prefixWord, tailWord_3231802, baseEnd_3231802] using wordTrace_append hprefix tailTrace_3231802
  have hstable : (prefixWord ++ tailWord_3231802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231802).length < 2 ^ (prefixWord ++ tailWord_3231802).sum := by decide
  have hdescent : baseEnd_3231802 < baseStart_3231802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231809 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3231809 : Nat := 118140960795 + 3231809 * 2 ^ 59
def prefixEnd_3231809 : Nat := 4983230072969 + 3 ^ 40 * 3231809 * 2
def baseEnd_3231809 : Nat := 553157133508817088708229

theorem tailTrace_3231809 : CollatzResearch.WordTrace tailWord_3231809 prefixEnd_3231809 553157133508817088708229 := by
  unfold tailWord_3231809
  simp only [CollatzResearch.WordTrace]
  refine ⟨117873757948715416879402481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78582505299143611252934987 117873757948715416879402481)
  ·
    refine ⟨88405318461536562659551861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117873757948715416879402481 88405318461536562659551861)
    ·
      refine ⟨8287998605769052749332987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88405318461536562659551861 8287998605769052749332987)
      ·
        refine ⟨12431997908653579123999481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8287998605769052749332987 12431997908653579123999481)
        ·
          refine ⟨9323998431490184342999611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12431997908653579123999481 9323998431490184342999611)
          ·
            refine ⟨13985997647235276514499417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9323998431490184342999611 13985997647235276514499417)
            ·
              refine ⟨10489498235426457385874563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13985997647235276514499417 10489498235426457385874563)
              ·
                refine ⟨15734247353139686078811845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10489498235426457385874563 15734247353139686078811845)
                ·
                  refine ⟨2950171378713691139777221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15734247353139686078811845 2950171378713691139777221)
                  ·
                    refine ⟨553157133508817088708229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2950171378713691139777221 553157133508817088708229)
                    ·
                      rfl

theorem cell23_3231809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3231809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231809 prefixEnd_3231809 := by exact prefixLift 3231809
  have htrace : WordTrace (prefixWord ++ tailWord_3231809) baseStart_3231809 baseEnd_3231809 := by
    simpa [prefixWord, tailWord_3231809, baseEnd_3231809] using wordTrace_append hprefix tailTrace_3231809
  have hstable : (prefixWord ++ tailWord_3231809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231809).length < 2 ^ (prefixWord ++ tailWord_3231809).sum := by decide
  have hdescent : baseEnd_3231809 < baseStart_3231809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231822 : List Nat := [4, 1, 1, 1, 1, 5, 2, 8]
def baseStart_3231822 : Nat := 118140960795 + 3231822 * 2 ^ 59
def prefixEnd_3231822 : Nat := 4983230072969 + 3 ^ 40 * 3231822 * 2
def baseEnd_3231822 : Nat := 61462150954628137602301

theorem tailTrace_3231822 : CollatzResearch.WordTrace tailWord_3231822 prefixEnd_3231822 61462150954628137602301 := by
  unfold tailWord_3231822
  simp only [CollatzResearch.WordTrace]
  refine ⟨14734279012208540012453215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78582821398445546733083813 14734279012208540012453215)
  ·
    refine ⟨22101418518312810018679823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14734279012208540012453215 22101418518312810018679823)
    ·
      refine ⟨33152127777469215028019735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22101418518312810018679823 33152127777469215028019735)
      ·
        refine ⟨49728191666203822542029603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33152127777469215028019735 49728191666203822542029603)
        ·
          refine ⟨74592287499305733813044405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49728191666203822542029603 74592287499305733813044405)
          ·
            refine ⟨6993026953059912544972913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74592287499305733813044405 6993026953059912544972913)
            ·
              refine ⟨5244770214794934408729685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6993026953059912544972913 5244770214794934408729685)
              ·
                refine ⟨61462150954628137602301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5244770214794934408729685 61462150954628137602301)
                ·
                  rfl

theorem cell23_3231822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_3231822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231822 prefixEnd_3231822 := by exact prefixLift 3231822
  have htrace : WordTrace (prefixWord ++ tailWord_3231822) baseStart_3231822 baseEnd_3231822 := by
    simpa [prefixWord, tailWord_3231822, baseEnd_3231822] using wordTrace_append hprefix tailTrace_3231822
  have hstable : (prefixWord ++ tailWord_3231822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231822).length < 2 ^ (prefixWord ++ tailWord_3231822).sum := by decide
  have hdescent : baseEnd_3231822 < baseStart_3231822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231825 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_3231825 : Nat := 118140960795 + 3231825 * 2 ^ 59
def prefixEnd_3231825 : Nat := 4983230072969 + 3 ^ 40 * 3231825 * 2
def baseEnd_3231825 : Nat := 1659479616216923203524613

theorem tailTrace_3231825 : CollatzResearch.WordTrace tailWord_3231825 prefixEnd_3231825 1659479616216923203524613 := by
  unfold tailWord_3231825
  simp only [CollatzResearch.WordTrace]
  refine ⟨117874341516657451611984929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78582894344438301074656619 117874341516657451611984929)
  ·
    refine ⟨88405756137493088708988697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117874341516657451611984929 88405756137493088708988697)
    ·
      refine ⟨66304317103119816531741523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88405756137493088708988697 66304317103119816531741523)
      ·
        refine ⟨99456475654679724797612285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66304317103119816531741523 99456475654679724797612285)
        ·
          refine ⟨37296178370504896799104607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99456475654679724797612285 37296178370504896799104607)
          ·
            refine ⟨55944267555757345198656911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37296178370504896799104607 55944267555757345198656911)
            ·
              refine ⟨83916401333636017797985367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55944267555757345198656911 83916401333636017797985367)
              ·
                refine ⟨125874602000454026696978051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83916401333636017797985367 125874602000454026696978051)
                ·
                  refine ⟨188811903000681040045467077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125874602000454026696978051 188811903000681040045467077)
                  ·
                    refine ⟨35402231812627695008525077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188811903000681040045467077 35402231812627695008525077)
                    ·
                      refine ⟨1659479616216923203524613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35402231812627695008525077 1659479616216923203524613)
                      ·
                        rfl

theorem cell23_3231825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_3231825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231825 prefixEnd_3231825 := by exact prefixLift 3231825
  have htrace : WordTrace (prefixWord ++ tailWord_3231825) baseStart_3231825 baseEnd_3231825 := by
    simpa [prefixWord, tailWord_3231825, baseEnd_3231825] using wordTrace_append hprefix tailTrace_3231825
  have hstable : (prefixWord ++ tailWord_3231825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231825).length < 2 ^ (prefixWord ++ tailWord_3231825).sum := by decide
  have hdescent : baseEnd_3231825 < baseStart_3231825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231826 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_3231826 : Nat := 118140960795 + 3231826 * 2 ^ 59
def prefixEnd_3231826 : Nat := 4983230072969 + 3 ^ 40 * 3231826 * 2
def baseEnd_3231826 : Nat := 553160043232525899870703

theorem tailTrace_3231826 : CollatzResearch.WordTrace tailWord_3231826 prefixEnd_3231826 553160043232525899870703 := by
  unfold tailWord_3231826
  simp only [CollatzResearch.WordTrace]
  refine ⟨29468594497413457195692833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78582918659769219188514221 29468594497413457195692833)
  ·
    refine ⟨22101445873060092896769625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29468594497413457195692833 22101445873060092896769625)
    ·
      refine ⟨16576084404795069672577219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22101445873060092896769625 16576084404795069672577219)
      ·
        refine ⟨24864126607192604508865829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16576084404795069672577219 24864126607192604508865829)
        ·
          refine ⟨4662023738848613345412343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24864126607192604508865829 4662023738848613345412343)
          ·
            refine ⟨6993035608272920018118515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4662023738848613345412343 6993035608272920018118515)
            ·
              refine ⟨10489553412409380027177773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6993035608272920018118515 10489553412409380027177773)
              ·
                refine ⟨3933582529653517510191665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10489553412409380027177773 3933582529653517510191665)
                ·
                  refine ⟨2950186897240138132643749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3933582529653517510191665 2950186897240138132643749)
                  ·
                    refine ⟨553160043232525899870703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2950186897240138132643749 553160043232525899870703)
                    ·
                      rfl

theorem cell23_3231826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_3231826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231826 prefixEnd_3231826 := by exact prefixLift 3231826
  have htrace : WordTrace (prefixWord ++ tailWord_3231826) baseStart_3231826 baseEnd_3231826 := by
    simpa [prefixWord, tailWord_3231826, baseEnd_3231826] using wordTrace_append hprefix tailTrace_3231826
  have hstable : (prefixWord ++ tailWord_3231826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231826).length < 2 ^ (prefixWord ++ tailWord_3231826).sum := by decide
  have hdescent : baseEnd_3231826 < baseStart_3231826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231836 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_3231836 : Nat := 118140960795 + 3231836 * 2 ^ 59
def prefixEnd_3231836 : Nat := 4983230072969 + 3 ^ 40 * 3231836 * 2
def baseEnd_3231836 : Nat := 1659485264504122660487063

theorem tailTrace_3231836 : CollatzResearch.WordTrace tailWord_3231836 prefixEnd_3231836 1659485264504122660487063 := by
  unfold tailWord_3231836
  simp only [CollatzResearch.WordTrace]
  refine ⟨58937371359808800245317681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78583161813078400327090241 58937371359808800245317681)
  ·
    refine ⟨44203028519856600183988261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58937371359808800245317681 44203028519856600183988261)
    ·
      refine ⟨8288067847473112534497799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44203028519856600183988261 8288067847473112534497799)
      ·
        refine ⟨12432101771209668801746699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8288067847473112534497799 12432101771209668801746699)
        ·
          refine ⟨18648152656814503202620049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12432101771209668801746699 18648152656814503202620049)
          ·
            refine ⟨13986114492610877401965037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18648152656814503202620049 13986114492610877401965037)
            ·
              refine ⟨5244792934729079025736889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13986114492610877401965037 5244792934729079025736889)
              ·
                refine ⟨3933594701046809269302667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5244792934729079025736889 3933594701046809269302667)
                ·
                  refine ⟨5900392051570213903954001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933594701046809269302667 5900392051570213903954001)
                  ·
                    refine ⟨4425294038677660427965501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5900392051570213903954001 4425294038677660427965501)
                    ·
                      refine ⟨1659485264504122660487063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4425294038677660427965501 1659485264504122660487063)
                      ·
                        rfl

theorem cell23_3231836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_3231836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231836 prefixEnd_3231836 := by exact prefixLift 3231836
  have htrace : WordTrace (prefixWord ++ tailWord_3231836) baseStart_3231836 baseEnd_3231836 := by
    simpa [prefixWord, tailWord_3231836, baseEnd_3231836] using wordTrace_append hprefix tailTrace_3231836
  have hstable : (prefixWord ++ tailWord_3231836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231836).length < 2 ^ (prefixWord ++ tailWord_3231836).sum := by decide
  have hdescent : baseEnd_3231836 < baseStart_3231836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231882 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_3231882 : Nat := 118140960795 + 3231882 * 2 ^ 59
def prefixEnd_3231882 : Nat := 4983230072969 + 3 ^ 40 * 3231882 * 2
def baseEnd_3231882 : Nat := 553169628204743160170617

theorem tailTrace_3231882 : CollatzResearch.WordTrace tailWord_3231882 prefixEnd_3231882 553169628204743160170617 := by
  unfold tailWord_3231882
  simp only [CollatzResearch.WordTrace]
  refine ⟨29469105119362737586702475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78584280318300633564539933 29469105119362737586702475)
  ·
    refine ⟨44203657679044106380053713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29469105119362737586702475 44203657679044106380053713)
    ·
      refine ⟨33152743259283079785040285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44203657679044106380053713 33152743259283079785040285)
      ·
        refine ⟨12432278722231154919390107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33152743259283079785040285 12432278722231154919390107)
        ·
          refine ⟨18648418083346732379085161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12432278722231154919390107 18648418083346732379085161)
          ·
            refine ⟨13986313562510049284313871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18648418083346732379085161 13986313562510049284313871)
            ·
              refine ⟨20979470343765073926470807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13986313562510049284313871 20979470343765073926470807)
              ·
                refine ⟨31469205515647610889706211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20979470343765073926470807 31469205515647610889706211)
                ·
                  refine ⟨47203808273471416334559317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31469205515647610889706211 47203808273471416334559317)
                  ·
                    refine ⟨553169628204743160170617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47203808273471416334559317 553169628204743160170617)
                    ·
                      rfl

theorem cell23_3231882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_3231882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231882 prefixEnd_3231882 := by exact prefixLift 3231882
  have htrace : WordTrace (prefixWord ++ tailWord_3231882) baseStart_3231882 baseEnd_3231882 := by
    simpa [prefixWord, tailWord_3231882, baseEnd_3231882] using wordTrace_append hprefix tailTrace_3231882
  have hstable : (prefixWord ++ tailWord_3231882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231882).length < 2 ^ (prefixWord ++ tailWord_3231882).sum := by decide
  have hdescent : baseEnd_3231882 < baseStart_3231882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231929 : List Nat := [1, 2, 1, 4, 1, 2, 1, 6, 5]
def baseStart_3231929 : Nat := 118140960795 + 3231929 * 2 ^ 59
def prefixEnd_3231929 : Nat := 4983230072969 + 3 ^ 40 * 3231929 * 2
def baseEnd_3231929 : Nat := 184392557578332310736015

theorem tailTrace_3231929 : CollatzResearch.WordTrace tailWord_3231929 prefixEnd_3231929 184392557578332310736015 := by
  unfold tailWord_3231929
  simp only [CollatzResearch.WordTrace]
  refine ⟨117878134708280677373770841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78585423138853784915847227 117878134708280677373770841)
  ·
    refine ⟨88408601031210508030328131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117878134708280677373770841 88408601031210508030328131)
    ·
      refine ⟨132612901546815762045492197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88408601031210508030328131 132612901546815762045492197)
      ·
        refine ⟨24864919040027955383529787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132612901546815762045492197 24864919040027955383529787)
        ·
          refine ⟨37297378560041933075294681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24864919040027955383529787 37297378560041933075294681)
          ·
            refine ⟨27973033920031449806471011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37297378560041933075294681 27973033920031449806471011)
            ·
              refine ⟨41959550880047174709706517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27973033920031449806471011 41959550880047174709706517)
              ·
                refine ⟨1966853947502211314517493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41959550880047174709706517 1966853947502211314517493)
                ·
                  refine ⟨184392557578332310736015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1966853947502211314517493 184392557578332310736015)
                  ·
                    rfl

theorem cell23_3231929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 5].length) (baseStart_3231929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231929 prefixEnd_3231929 := by exact prefixLift 3231929
  have htrace : WordTrace (prefixWord ++ tailWord_3231929) baseStart_3231929 baseEnd_3231929 := by
    simpa [prefixWord, tailWord_3231929, baseEnd_3231929] using wordTrace_append hprefix tailTrace_3231929
  have hstable : (prefixWord ++ tailWord_3231929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231929).length < 2 ^ (prefixWord ++ tailWord_3231929).sum := by decide
  have hdescent : baseEnd_3231929 < baseStart_3231929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231979 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 4]
def baseStart_3231979 : Nat := 118140960795 + 3231979 * 2 ^ 59
def prefixEnd_3231979 : Nat := 4983230072969 + 3 ^ 40 * 3231979 * 2
def baseEnd_3231979 : Nat := 1659558692237715600998905

theorem tailTrace_3231979 : CollatzResearch.WordTrace tailWord_3231979 prefixEnd_3231979 1659558692237715600998905 := by
  unfold tailWord_3231979
  simp only [CollatzResearch.WordTrace]
  refine ⟨117879958358099535913090991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78586638905399690608727327 117879958358099535913090991)
  ·
    refine ⟨176819937537149303869636487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117879958358099535913090991 176819937537149303869636487)
    ·
      refine ⟨265229906305723955804454731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176819937537149303869636487 265229906305723955804454731)
      ·
        refine ⟨397844859458585933706682097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265229906305723955804454731 397844859458585933706682097)
        ·
          refine ⟨298383644593939450280011573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397844859458585933706682097 298383644593939450280011573)
          ·
            refine ⟨27973466680681823463751085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298383644593939450280011573 27973466680681823463751085)
            ·
              refine ⟨10490050005255683798906657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27973466680681823463751085 10490050005255683798906657)
              ·
                refine ⟨7867537503941762849179993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10490050005255683798906657 7867537503941762849179993)
                ·
                  refine ⟨5900653127956322136884995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7867537503941762849179993 5900653127956322136884995)
                  ·
                    refine ⟨8850979691934483205327493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5900653127956322136884995 8850979691934483205327493)
                    ·
                      refine ⟨1659558692237715600998905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8850979691934483205327493 1659558692237715600998905)
                      ·
                        rfl

theorem cell23_3231979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 4].length) (baseStart_3231979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231979 prefixEnd_3231979 := by exact prefixLift 3231979
  have htrace : WordTrace (prefixWord ++ tailWord_3231979) baseStart_3231979 baseEnd_3231979 := by
    simpa [prefixWord, tailWord_3231979, baseEnd_3231979] using wordTrace_append hprefix tailTrace_3231979
  have hstable : (prefixWord ++ tailWord_3231979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231979).length < 2 ^ (prefixWord ++ tailWord_3231979).sum := by decide
  have hdescent : baseEnd_3231979 < baseStart_3231979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231992 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_3231992 : Nat := 118140960795 + 3231992 * 2 ^ 59
def prefixEnd_3231992 : Nat := 4983230072969 + 3 ^ 40 * 3231992 * 2
def baseEnd_3231992 : Nat := 1659565367486224050136345

theorem tailTrace_3231992 : CollatzResearch.WordTrace tailWord_3231992 prefixEnd_3231992 1659565367486224050136345 := by
  unfold tailWord_3231992
  simp only [CollatzResearch.WordTrace]
  refine ⟨58940216253526219566657115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78586955004701626088876153 58940216253526219566657115)
  ·
    refine ⟨88410324380289329349985673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58940216253526219566657115 88410324380289329349985673)
    ·
      refine ⟨66307743285216997012489255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88410324380289329349985673 66307743285216997012489255)
      ·
        refine ⟨99461614927825495518733883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66307743285216997012489255 99461614927825495518733883)
        ·
          refine ⟨149192422391738243278100825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99461614927825495518733883 149192422391738243278100825)
          ·
            refine ⟨111894316793803682458575619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149192422391738243278100825 111894316793803682458575619)
            ·
              refine ⟨167841475190705523687863429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111894316793803682458575619 167841475190705523687863429)
              ·
                refine ⟨31470276598257285691474393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167841475190705523687863429 31470276598257285691474393)
                ·
                  refine ⟨23602707448692964268605795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31470276598257285691474393 23602707448692964268605795)
                  ·
                    refine ⟨35404061173039446402908693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23602707448692964268605795 35404061173039446402908693)
                    ·
                      refine ⟨1659565367486224050136345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35404061173039446402908693 1659565367486224050136345)
                      ·
                        rfl

theorem cell23_3231992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_3231992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231992 prefixEnd_3231992 := by exact prefixLift 3231992
  have htrace : WordTrace (prefixWord ++ tailWord_3231992) baseStart_3231992 baseEnd_3231992 := by
    simpa [prefixWord, tailWord_3231992, baseEnd_3231992] using wordTrace_append hprefix tailTrace_3231992
  have hstable : (prefixWord ++ tailWord_3231992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231992).length < 2 ^ (prefixWord ++ tailWord_3231992).sum := by decide
  have hdescent : baseEnd_3231992 < baseStart_3231992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3231999 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 3]
def baseStart_3231999 : Nat := 118140960795 + 3231999 * 2 ^ 59
def prefixEnd_3231999 : Nat := 4983230072969 + 3 ^ 40 * 3231999 * 2
def baseEnd_3231999 : Nat := 1659568961850805522748813

theorem tailTrace_3231999 : CollatzResearch.WordTrace tailWord_3231999 prefixEnd_3231999 1659568961850805522748813 := by
  unfold tailWord_3231999
  simp only [CollatzResearch.WordTrace]
  refine ⟨117880687818027079328819051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78587125212018052885879367 117880687818027079328819051)
  ·
    refine ⟨176821031727040618993228577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117880687818027079328819051 176821031727040618993228577)
    ·
      refine ⟨132615773795280464244921433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176821031727040618993228577 132615773795280464244921433)
      ·
        refine ⟨99461830346460348183691075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132615773795280464244921433 99461830346460348183691075)
        ·
          refine ⟨149192745519690522275536613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99461830346460348183691075 149192745519690522275536613)
          ·
            refine ⟨27973639784941972926663115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149192745519690522275536613 27973639784941972926663115)
            ·
              refine ⟨41960459677412959389994673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27973639784941972926663115 41960459677412959389994673)
              ·
                refine ⟨31470344758059719542496005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41960459677412959389994673 31470344758059719542496005)
                ·
                  refine ⟨5900689642136197414218001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31470344758059719542496005 5900689642136197414218001)
                  ·
                    refine ⟨4425517231602148060663501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5900689642136197414218001 4425517231602148060663501)
                    ·
                      refine ⟨1659568961850805522748813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4425517231602148060663501 1659568961850805522748813)
                      ·
                        rfl

theorem cell23_3231999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_3231999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3231999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3231999 prefixEnd_3231999 := by exact prefixLift 3231999
  have htrace : WordTrace (prefixWord ++ tailWord_3231999) baseStart_3231999 baseEnd_3231999 := by
    simpa [prefixWord, tailWord_3231999, baseEnd_3231999] using wordTrace_append hprefix tailTrace_3231999
  have hstable : (prefixWord ++ tailWord_3231999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3231999).length < 2 ^ (prefixWord ++ tailWord_3231999).sum := by decide
  have hdescent : baseEnd_3231999 < baseStart_3231999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3231999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232036 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 6]
def baseStart_3232036 : Nat := 118140960795 + 3232036 * 2 ^ 59
def prefixEnd_3232036 : Nat := 4983230072969 + 3 ^ 40 * 3232036 * 2
def baseEnd_3232036 : Nat := 184398662292780208665127

theorem tailTrace_3232036 : CollatzResearch.WordTrace tailWord_3232036 prefixEnd_3232036 184398662292780208665127 := by
  unfold tailWord_3232036
  simp only [CollatzResearch.WordTrace]
  refine ⟨58941018659446517323957981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78588024879262023098610641 58941018659446517323957981)
  ·
    refine ⟨22102881997292443996484243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58941018659446517323957981 22102881997292443996484243)
    ·
      refine ⟨33154322995938665994726365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22102881997292443996484243 33154322995938665994726365)
      ·
        refine ⟨12432871123476999748022387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33154322995938665994726365 12432871123476999748022387)
        ·
          refine ⟨18649306685215499622033581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12432871123476999748022387 18649306685215499622033581)
          ·
            refine ⟨6993490006955812358262593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18649306685215499622033581 6993490006955812358262593)
            ·
              refine ⟨5245117505216859268696945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6993490006955812358262593 5245117505216859268696945)
              ·
                refine ⟨3933838128912644451522709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5245117505216859268696945 3933838128912644451522709)
                ·
                  refine ⟨184398662292780208665127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3933838128912644451522709 184398662292780208665127)
                  ·
                    rfl

theorem cell23_3232036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_3232036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232036 prefixEnd_3232036 := by exact prefixLift 3232036
  have htrace : WordTrace (prefixWord ++ tailWord_3232036) baseStart_3232036 baseEnd_3232036 := by
    simpa [prefixWord, tailWord_3232036, baseEnd_3232036] using wordTrace_append hprefix tailTrace_3232036
  have hstable : (prefixWord ++ tailWord_3232036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232036).length < 2 ^ (prefixWord ++ tailWord_3232036).sum := by decide
  have hdescent : baseEnd_3232036 < baseStart_3232036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232040 : List Nat := [2, 1, 5, 1, 3, 1, 1, 4, 1, 4]
def baseStart_3232040 : Nat := 118140960795 + 3232040 * 2 ^ 59
def prefixEnd_3232040 : Nat := 4983230072969 + 3 ^ 40 * 3232040 * 2
def baseEnd_3232040 : Nat := 553196671519213287445375

theorem tailTrace_3232040 : CollatzResearch.WordTrace tailWord_3232040 prefixEnd_3232040 553196671519213287445375 := by
  unfold tailWord_3232040
  simp only [CollatzResearch.WordTrace]
  refine ⟨58941091605439271665530787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78588122140585695554041049 58941091605439271665530787)
  ·
    refine ⟨88411637408158907498296181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58941091605439271665530787 88411637408158907498296181)
    ·
      refine ⟨8288591007014897577965267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88411637408158907498296181 8288591007014897577965267)
      ·
        refine ⟨12432886510522346366947901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8288591007014897577965267 12432886510522346366947901)
        ·
          refine ⟨4662332441445879887605463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12432886510522346366947901 4662332441445879887605463)
          ·
            refine ⟨6993498662168819831408195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4662332441445879887605463 6993498662168819831408195)
            ·
              refine ⟨10490247993253229747112293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6993498662168819831408195 10490247993253229747112293)
              ·
                refine ⟨1966921498734980577583555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10490247993253229747112293 1966921498734980577583555)
                ·
                  refine ⟨2950382248102470866375333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966921498734980577583555 2950382248102470866375333)
                  ·
                    refine ⟨553196671519213287445375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2950382248102470866375333 553196671519213287445375)
                    ·
                      rfl

theorem cell23_3232040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_3232040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232040 prefixEnd_3232040 := by exact prefixLift 3232040
  have htrace : WordTrace (prefixWord ++ tailWord_3232040) baseStart_3232040 baseEnd_3232040 := by
    simpa [prefixWord, tailWord_3232040, baseEnd_3232040] using wordTrace_append hprefix tailTrace_3232040
  have hstable : (prefixWord ++ tailWord_3232040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232040).length < 2 ^ (prefixWord ++ tailWord_3232040).sum := by decide
  have hdescent : baseEnd_3232040 < baseStart_3232040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232056 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 4, 3, 2]
def baseStart_3232056 : Nat := 118140960795 + 3232056 * 2 ^ 59
def prefixEnd_3232056 : Nat := 4983230072969 + 3 ^ 40 * 3232056 * 2
def baseEnd_3232056 : Nat := 1659598230248111799736051

theorem tailTrace_3232056 : CollatzResearch.WordTrace tailWord_3232056 prefixEnd_3232056 1659598230248111799736051 := by
  unfold tailWord_3232056
  simp only [CollatzResearch.WordTrace]
  refine ⟨58941383389410289031822011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78588511185880385375762681 58941383389410289031822011)
  ·
    refine ⟨88412075084115433547733017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58941383389410289031822011 88412075084115433547733017)
    ·
      refine ⟨66309056313086575160799763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88412075084115433547733017 66309056313086575160799763)
      ·
        refine ⟨99463584469629862741199645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66309056313086575160799763 99463584469629862741199645)
        ·
          refine ⟨37298844176111198527949867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99463584469629862741199645 37298844176111198527949867)
          ·
            refine ⟨55948266264166797791924801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37298844176111198527949867 55948266264166797791924801)
            ·
              refine ⟨41961199698125098343943601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55948266264166797791924801 41961199698125098343943601)
              ·
                refine ⟨31470899773593823757957701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41961199698125098343943601 31470899773593823757957701)
                ·
                  refine ⟨5900793707548841954617069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31470899773593823757957701 5900793707548841954617069)
                  ·
                    refine ⟨2212797640330815732981401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5900793707548841954617069 2212797640330815732981401)
                    ·
                      refine ⟨1659598230248111799736051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212797640330815732981401 1659598230248111799736051)
                      ·
                        rfl

theorem cell23_3232056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 3, 2].length) (baseStart_3232056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232056 prefixEnd_3232056 := by exact prefixLift 3232056
  have htrace : WordTrace (prefixWord ++ tailWord_3232056) baseStart_3232056 baseEnd_3232056 := by
    simpa [prefixWord, tailWord_3232056, baseEnd_3232056] using wordTrace_append hprefix tailTrace_3232056
  have hstable : (prefixWord ++ tailWord_3232056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232056).length < 2 ^ (prefixWord ++ tailWord_3232056).sum := by decide
  have hdescent : baseEnd_3232056 < baseStart_3232056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232080 : List Nat := [2, 1, 1, 1, 1, 7, 2, 3, 1, 1, 3]
def baseStart_3232080 : Nat := 118140960795 + 3232080 * 2 ^ 59
def prefixEnd_3232080 : Nat := 4983230072969 + 3 ^ 40 * 3232080 * 2
def baseEnd_3232080 : Nat := 1659610553783819705835941

theorem tailTrace_3232080 : CollatzResearch.WordTrace tailWord_3232080 prefixEnd_3232080 1659610553783819705835941 := by
  unfold tailWord_3232080
  simp only [CollatzResearch.WordTrace]
  refine ⟨58941821065366815081258847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78589094753822420108345129 58941821065366815081258847)
  ·
    refine ⟨88412731598050222621888271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58941821065366815081258847 88412731598050222621888271)
    ·
      refine ⟨132619097397075333932832407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88412731598050222621888271 132619097397075333932832407)
      ·
        refine ⟨198928646095613000899248611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132619097397075333932832407 198928646095613000899248611)
        ·
          refine ⟨298392969143419501348872917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198928646095613000899248611 298392969143419501348872917)
          ·
            refine ⟨6993585214298894562864209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 298392969143419501348872917 6993585214298894562864209)
            ·
              refine ⟨5245188910724170922148157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6993585214298894562864209 5245188910724170922148157)
              ·
                refine ⟨1966945841521564095805559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5245188910724170922148157 1966945841521564095805559)
                ·
                  refine ⟨2950418762282346143708339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966945841521564095805559 2950418762282346143708339)
                  ·
                    refine ⟨4425628143423519215562509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2950418762282346143708339 4425628143423519215562509)
                    ·
                      refine ⟨1659610553783819705835941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4425628143423519215562509 1659610553783819705835941)
                      ·
                        rfl

theorem cell23_3232080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 1, 1, 3].length) (baseStart_3232080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232080 prefixEnd_3232080 := by exact prefixLift 3232080
  have htrace : WordTrace (prefixWord ++ tailWord_3232080) baseStart_3232080 baseEnd_3232080 := by
    simpa [prefixWord, tailWord_3232080, baseEnd_3232080] using wordTrace_append hprefix tailTrace_3232080
  have hstable : (prefixWord ++ tailWord_3232080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232080).length < 2 ^ (prefixWord ++ tailWord_3232080).sum := by decide
  have hdescent : baseEnd_3232080 < baseStart_3232080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232089 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 5]
def baseStart_3232089 : Nat := 118140960795 + 3232089 * 2 ^ 59
def prefixEnd_3232089 : Nat := 4983230072969 + 3 ^ 40 * 3232089 * 2
def baseEnd_3232089 : Nat := 1659615175109710170623399

theorem tailTrace_3232089 : CollatzResearch.WordTrace tailWord_3232089 prefixEnd_3232089 1659615175109710170623399 := by
  unfold tailWord_3232089
  simp only [CollatzResearch.WordTrace]
  refine ⟨117883970387701024699595321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78589313591800683133063547 117883970387701024699595321)
  ·
    refine ⟨88412977790775768524696491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117883970387701024699595321 88412977790775768524696491)
    ·
      refine ⟨132619466686163652787044737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88412977790775768524696491 132619466686163652787044737)
      ·
        refine ⟨99464600014622739590283553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132619466686163652787044737 99464600014622739590283553)
        ·
          refine ⟨74598450010967054692712665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99464600014622739590283553 74598450010967054692712665)
          ·
            refine ⟨55948837508225291019534499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74598450010967054692712665 55948837508225291019534499)
            ·
              refine ⟨83923256262337936529301749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55948837508225291019534499 83923256262337936529301749)
              ·
                refine ⟨7867805274594181549622039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83923256262337936529301749 7867805274594181549622039)
                ·
                  refine ⟨11801707911891272324433059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7867805274594181549622039 11801707911891272324433059)
                  ·
                    refine ⟨17702561867836908486649589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11801707911891272324433059 17702561867836908486649589)
                    ·
                      refine ⟨1659615175109710170623399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17702561867836908486649589 1659615175109710170623399)
                      ·
                        rfl

theorem cell23_3232089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_3232089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232089 prefixEnd_3232089 := by exact prefixLift 3232089
  have htrace : WordTrace (prefixWord ++ tailWord_3232089) baseStart_3232089 baseEnd_3232089 := by
    simpa [prefixWord, tailWord_3232089, baseEnd_3232089] using wordTrace_append hprefix tailTrace_3232089
  have hstable : (prefixWord ++ tailWord_3232089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232089).length < 2 ^ (prefixWord ++ tailWord_3232089).sum := by decide
  have hdescent : baseEnd_3232089 < baseStart_3232089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232099 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 6]
def baseStart_3232099 : Nat := 118140960795 + 3232099 * 2 ^ 59
def prefixEnd_3232099 : Nat := 4983230072969 + 3 ^ 40 * 3232099 * 2
def baseEnd_3232099 : Nat := 1659620309916255131498353

theorem tailTrace_3232099 : CollatzResearch.WordTrace tailWord_3232099 prefixEnd_3232099 1659620309916255131498353 := by
  unfold tailWord_3232099
  simp only [CollatzResearch.WordTrace]
  refine ⟨117884335117664796407459351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78589556745109864271639567 117884335117664796407459351)
  ·
    refine ⟨176826502676497194611189027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117884335117664796407459351 176826502676497194611189027)
    ·
      refine ⟨265239754014745791916783541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176826502676497194611189027 265239754014745791916783541)
      ·
        refine ⟨24866226938882417992198457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265239754014745791916783541 24866226938882417992198457)
        ·
          refine ⟨18649670204161813494148843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24866226938882417992198457 18649670204161813494148843)
          ·
            refine ⟨27974505306242720241223265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18649670204161813494148843 27974505306242720241223265)
            ·
              refine ⟨20980878979682040180917449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27974505306242720241223265 20980878979682040180917449)
              ·
                refine ⟨15735659234761530135688087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20980878979682040180917449 15735659234761530135688087)
                ·
                  refine ⟨23603488852142295203532131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15735659234761530135688087 23603488852142295203532131)
                  ·
                    refine ⟨35405233278213442805298197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23603488852142295203532131 35405233278213442805298197)
                    ·
                      refine ⟨1659620309916255131498353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35405233278213442805298197 1659620309916255131498353)
                      ·
                        rfl

theorem cell23_3232099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_3232099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232099 prefixEnd_3232099 := by exact prefixLift 3232099
  have htrace : WordTrace (prefixWord ++ tailWord_3232099) baseStart_3232099 baseEnd_3232099 := by
    simpa [prefixWord, tailWord_3232099, baseEnd_3232099] using wordTrace_append hprefix tailTrace_3232099
  have hstable : (prefixWord ++ tailWord_3232099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232099).length < 2 ^ (prefixWord ++ tailWord_3232099).sum := by decide
  have hdescent : baseEnd_3232099 < baseStart_3232099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232106 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3232106 : Nat := 118140960795 + 3232106 * 2 ^ 59
def prefixEnd_3232106 : Nat := 4983230072969 + 3 ^ 40 * 3232106 * 2
def baseEnd_3232106 : Nat := 1659623904280836604110821

theorem tailTrace_3232106 : CollatzResearch.WordTrace tailWord_3232106 prefixEnd_3232106 1659623904280836604110821 := by
  unfold tailWord_3232106
  simp only [CollatzResearch.WordTrace]
  refine ⟨29471147607159859150741043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78589726952426291068642781 29471147607159859150741043)
  ·
    refine ⟨44206721410739788726111565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29471147607159859150741043 44206721410739788726111565)
    ·
      refine ⟨16577520529027420772291837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44206721410739788726111565 16577520529027420772291837)
      ·
        refine ⟨6216570198385282789609439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16577520529027420772291837 6216570198385282789609439)
        ·
          refine ⟨9324855297577924184414159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6216570198385282789609439 9324855297577924184414159)
          ·
            refine ⟨13987282946366886276621239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9324855297577924184414159 13987282946366886276621239)
            ·
              refine ⟨20980924419550329414931859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13987282946366886276621239 20980924419550329414931859)
              ·
                refine ⟨31471386629325494122397789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20980924419550329414931859 31471386629325494122397789)
                ·
                  refine ⟨11801769985997060295899171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31471386629325494122397789 11801769985997060295899171)
                  ·
                    refine ⟨17702654978995590443848757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11801769985997060295899171 17702654978995590443848757)
                    ·
                      refine ⟨1659623904280836604110821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17702654978995590443848757 1659623904280836604110821)
                      ·
                        rfl

theorem cell23_3232106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3232106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232106 prefixEnd_3232106 := by exact prefixLift 3232106
  have htrace : WordTrace (prefixWord ++ tailWord_3232106) baseStart_3232106 baseEnd_3232106 := by
    simpa [prefixWord, tailWord_3232106, baseEnd_3232106] using wordTrace_append hprefix tailTrace_3232106
  have hstable : (prefixWord ++ tailWord_3232106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232106).length < 2 ^ (prefixWord ++ tailWord_3232106).sum := by decide
  have hdescent : baseEnd_3232106 < baseStart_3232106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232109 : List Nat := [1, 5, 1, 1, 1, 2, 2, 10]
def baseStart_3232109 : Nat := 118140960795 + 3232109 * 2 ^ 59
def prefixEnd_3232109 : Nat := 4983230072969 + 3 ^ 40 * 3232109 * 2
def baseEnd_3232109 : Nat := 61467609063807410828641

theorem tailTrace_3232109 : CollatzResearch.WordTrace tailWord_3232109 prefixEnd_3232109 61467609063807410828641 := by
  unfold tailWord_3232109
  simp only [CollatzResearch.WordTrace]
  refine ⟨117884699847628568115323381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78589799898419045410215587 117884699847628568115323381)
  ·
    refine ⟨11051690610715178260811567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117884699847628568115323381 11051690610715178260811567)
    ·
      refine ⟨16577535916072767391217351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11051690610715178260811567 16577535916072767391217351)
      ·
        refine ⟨24866303874109151086826027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16577535916072767391217351 24866303874109151086826027)
        ·
          refine ⟨37299455811163726630239041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24866303874109151086826027 37299455811163726630239041)
          ·
            refine ⟨27974591858372794972679281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37299455811163726630239041 27974591858372794972679281)
            ·
              refine ⟨20980943893779596229509461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27974591858372794972679281 20980943893779596229509461)
              ·
                refine ⟨61467609063807410828641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20980943893779596229509461 61467609063807410828641)
                ·
                  rfl

theorem cell23_3232109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 10].length) (baseStart_3232109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232109 prefixEnd_3232109 := by exact prefixLift 3232109
  have htrace : WordTrace (prefixWord ++ tailWord_3232109) baseStart_3232109 baseEnd_3232109 := by
    simpa [prefixWord, tailWord_3232109, baseEnd_3232109] using wordTrace_append hprefix tailTrace_3232109
  have hstable : (prefixWord ++ tailWord_3232109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232109).length < 2 ^ (prefixWord ++ tailWord_3232109).sum := by decide
  have hdescent : baseEnd_3232109 < baseStart_3232109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232123 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 1, 2, 3]
def baseStart_3232123 : Nat := 118140960795 + 3232123 * 2 ^ 59
def prefixEnd_3232123 : Nat := 4983230072969 + 3 ^ 40 * 3232123 * 2
def baseEnd_3232123 : Nat := 1659632633451963037598243

theorem tailTrace_3232123 : CollatzResearch.WordTrace tailWord_3232123 prefixEnd_3232123 1659632633451963037598243 := by
  unfold tailWord_3232123
  simp only [CollatzResearch.WordTrace]
  refine ⟨117885210469577848506333023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78590140313051899004222015 117885210469577848506333023)
  ·
    refine ⟨176827815704366772759499535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117885210469577848506333023 176827815704366772759499535)
    ·
      refine ⟨265241723556550159139249303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176827815704366772759499535 265241723556550159139249303)
      ·
        refine ⟨397862585334825238708873955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265241723556550159139249303 397862585334825238708873955)
        ·
          refine ⟨596793878002237858063310933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397862585334825238708873955 596793878002237858063310933)
          ·
            refine ⟨6993678257838724899179425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 596793878002237858063310933 6993678257838724899179425)
            ·
              refine ⟨5245258693379043674384569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6993678257838724899179425 5245258693379043674384569)
              ·
                refine ⟨3933944020034282755788427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5245258693379043674384569 3933944020034282755788427)
                ·
                  refine ⟨5900916030051424133682641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933944020034282755788427 5900916030051424133682641)
                  ·
                    refine ⟨4425687022538568100261981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5900916030051424133682641 4425687022538568100261981)
                    ·
                      refine ⟨1659632633451963037598243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4425687022538568100261981 1659632633451963037598243)
                      ·
                        rfl

theorem cell23_3232123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 2, 3].length) (baseStart_3232123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232123 prefixEnd_3232123 := by exact prefixLift 3232123
  have htrace : WordTrace (prefixWord ++ tailWord_3232123) baseStart_3232123 baseEnd_3232123 := by
    simpa [prefixWord, tailWord_3232123, baseEnd_3232123] using wordTrace_append hprefix tailTrace_3232123
  have hstable : (prefixWord ++ tailWord_3232123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232123).length < 2 ^ (prefixWord ++ tailWord_3232123).sum := by decide
  have hdescent : baseEnd_3232123 < baseStart_3232123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232136 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_3232136 : Nat := 118140960795 + 3232136 * 2 ^ 59
def prefixEnd_3232136 : Nat := 4983230072969 + 3 ^ 40 * 3232136 * 2
def baseEnd_3232136 : Nat := 1659639308700471486735683

theorem tailTrace_3232136 : CollatzResearch.WordTrace tailWord_3232136 prefixEnd_3232136 1659639308700471486735683 := by
  unfold tailWord_3232136
  simp only [CollatzResearch.WordTrace]
  refine ⟨58942842309265375863278131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78590456412353834484370841 58942842309265375863278131)
  ·
    refine ⟨88414263463898063794917197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58942842309265375863278131 88414263463898063794917197)
    ·
      refine ⟨33155348798961773923093949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88414263463898063794917197 33155348798961773923093949)
      ·
        refine ⟨12433255799610665221160231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33155348798961773923093949 12433255799610665221160231)
        ·
          refine ⟨18649883699415997831740347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12433255799610665221160231 18649883699415997831740347)
          ·
            refine ⟨27974825549123996747610521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18649883699415997831740347 27974825549123996747610521)
            ·
              refine ⟨20981119161842997560707891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27974825549123996747610521 20981119161842997560707891)
              ·
                refine ⟨31471678742764496341061837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20981119161842997560707891 31471678742764496341061837)
                ·
                  refine ⟨11801879528536686127898189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31471678742764496341061837 11801879528536686127898189)
                  ·
                    refine ⟨4425704823201257297961821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11801879528536686127898189 4425704823201257297961821)
                    ·
                      refine ⟨1659639308700471486735683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4425704823201257297961821 1659639308700471486735683)
                      ·
                        rfl

theorem cell23_3232136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_3232136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232136 prefixEnd_3232136 := by exact prefixLift 3232136
  have htrace : WordTrace (prefixWord ++ tailWord_3232136) baseStart_3232136 baseEnd_3232136 := by
    simpa [prefixWord, tailWord_3232136, baseEnd_3232136] using wordTrace_append hprefix tailTrace_3232136
  have hstable : (prefixWord ++ tailWord_3232136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232136).length < 2 ^ (prefixWord ++ tailWord_3232136).sum := by decide
  have hdescent : baseEnd_3232136 < baseStart_3232136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232137 : List Nat := [1, 2, 1, 1, 6, 1, 3, 3, 1, 2, 2]
def baseStart_3232137 : Nat := 118140960795 + 3232137 * 2 ^ 59
def prefixEnd_3232137 : Nat := 4983230072969 + 3 ^ 40 * 3232137 * 2
def baseEnd_3232137 : Nat := 1659639822181125982823179

theorem tailTrace_3232137 : CollatzResearch.WordTrace tailWord_3232137 prefixEnd_3232137 1659639822181125982823179 := by
  unfold tailWord_3232137
  simp only [CollatzResearch.WordTrace]
  refine ⟨117885721091527128897342665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78590480727684752598228443 117885721091527128897342665)
  ·
    refine ⟨88414290818645346673006999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117885721091527128897342665 88414290818645346673006999)
    ·
      refine ⟨132621436227968020009510499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88414290818645346673006999 132621436227968020009510499)
      ·
        refine ⟨198932154341952030014265749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132621436227968020009510499 198932154341952030014265749)
        ·
          refine ⟨9324944734779001406918707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 198932154341952030014265749 9324944734779001406918707)
          ·
            refine ⟨13987417102168502110378061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9324944734779001406918707 13987417102168502110378061)
            ·
              refine ⟨5245281413313188291391773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13987417102168502110378061 5245281413313188291391773)
              ·
                refine ⟨1966980529992445609271915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5245281413313188291391773 1966980529992445609271915)
                ·
                  refine ⟨2950470794988668413907873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966980529992445609271915 2950470794988668413907873)
                  ·
                    refine ⟨2212853096241501310430905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2950470794988668413907873 2212853096241501310430905)
                    ·
                      refine ⟨1659639822181125982823179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212853096241501310430905 1659639822181125982823179)
                      ·
                        rfl

theorem cell23_3232137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 1, 2, 2].length) (baseStart_3232137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232137 prefixEnd_3232137 := by exact prefixLift 3232137
  have htrace : WordTrace (prefixWord ++ tailWord_3232137) baseStart_3232137 baseEnd_3232137 := by
    simpa [prefixWord, tailWord_3232137, baseEnd_3232137] using wordTrace_append hprefix tailTrace_3232137
  have hstable : (prefixWord ++ tailWord_3232137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232137).length < 2 ^ (prefixWord ++ tailWord_3232137).sum := by decide
  have hdescent : baseEnd_3232137 < baseStart_3232137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232149 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_3232149 : Nat := 118140960795 + 3232149 * 2 ^ 59
def prefixEnd_3232149 : Nat := 4983230072969 + 3 ^ 40 * 3232149 * 2
def baseEnd_3232149 : Nat := 1659645983948979935873123

theorem tailTrace_3232149 : CollatzResearch.WordTrace tailWord_3232149 prefixEnd_3232149 1659645983948979935873123 := by
  unfold tailWord_3232149
  simp only [CollatzResearch.WordTrace]
  refine ⟨117886158767483654946779501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78590772511655769964519667 117886158767483654946779501)
  ·
    refine ⟨44207309537806370605042313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117886158767483654946779501 44207309537806370605042313)
    ·
      refine ⟨33155482153354777953781735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44207309537806370605042313 33155482153354777953781735)
      ·
        refine ⟨49733223230032166930672603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33155482153354777953781735 49733223230032166930672603)
        ·
          refine ⟨74599834845048250396008905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49733223230032166930672603 74599834845048250396008905)
          ·
            refine ⟨55949876133786187797006679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74599834845048250396008905 55949876133786187797006679)
            ·
              refine ⟨83924814200679281695510019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55949876133786187797006679 83924814200679281695510019)
              ·
                refine ⟨125887221301018922543265029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83924814200679281695510019 125887221301018922543265029)
                ·
                  refine ⟨23603853993941047976862193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125887221301018922543265029 23603853993941047976862193)
                  ·
                    refine ⟨17702890495455785982646645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23603853993941047976862193 17702890495455785982646645)
                    ·
                      refine ⟨1659645983948979935873123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17702890495455785982646645 1659645983948979935873123)
                      ·
                        rfl

theorem cell23_3232149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_3232149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232149 prefixEnd_3232149 := by exact prefixLift 3232149
  have htrace : WordTrace (prefixWord ++ tailWord_3232149) baseStart_3232149 baseEnd_3232149 := by
    simpa [prefixWord, tailWord_3232149, baseEnd_3232149] using wordTrace_append hprefix tailTrace_3232149
  have hstable : (prefixWord ++ tailWord_3232149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232149).length < 2 ^ (prefixWord ++ tailWord_3232149).sum := by decide
  have hdescent : baseEnd_3232149 < baseStart_3232149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232153 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 2, 1, 3]
def baseStart_3232153 : Nat := 118140960795 + 3232153 * 2 ^ 59
def prefixEnd_3232153 : Nat := 4983230072969 + 3 ^ 40 * 3232153 * 2
def baseEnd_3232153 : Nat := 1659648037871597920223105

theorem tailTrace_3232153 : CollatzResearch.WordTrace tailWord_3232153 prefixEnd_3232153 1659648037871597920223105 := by
  unfold tailWord_3232153
  simp only [CollatzResearch.WordTrace]
  refine ⟨117886304659469163629925113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78590869772979442419950075 117886304659469163629925113)
  ·
    refine ⟨88414728494601872722443835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117886304659469163629925113 88414728494601872722443835)
    ·
      refine ⟨132622092741902809083665753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88414728494601872722443835 132622092741902809083665753)
      ·
        refine ⟨99466569556427106812749315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132622092741902809083665753 99466569556427106812749315)
        ·
          refine ⟨149199854334640660219123973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99466569556427106812749315 149199854334640660219123973)
          ·
            refine ⟨27974972687745123791085745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149199854334640660219123973 27974972687745123791085745)
            ·
              refine ⟨20981229515808842843314309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27974972687745123791085745 20981229515808842843314309)
              ·
                refine ⟨3933980534214158033121433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20981229515808842843314309 3933980534214158033121433)
                ·
                  refine ⟨2950485400660618524841075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3933980534214158033121433 2950485400660618524841075)
                  ·
                    refine ⟨4425728100990927787261613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2950485400660618524841075 4425728100990927787261613)
                    ·
                      refine ⟨1659648037871597920223105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4425728100990927787261613 1659648037871597920223105)
                      ·
                        rfl

theorem cell23_3232153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_3232153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232153 prefixEnd_3232153 := by exact prefixLift 3232153
  have htrace : WordTrace (prefixWord ++ tailWord_3232153) baseStart_3232153 baseEnd_3232153 := by
    simpa [prefixWord, tailWord_3232153, baseEnd_3232153] using wordTrace_append hprefix tailTrace_3232153
  have hstable : (prefixWord ++ tailWord_3232153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232153).length < 2 ^ (prefixWord ++ tailWord_3232153).sum := by decide
  have hdescent : baseEnd_3232153 < baseStart_3232153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232154 : List Nat := [3, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2]
def baseStart_3232154 : Nat := 118140960795 + 3232154 * 2 ^ 59
def prefixEnd_3232154 : Nat := 4983230072969 + 3 ^ 40 * 3232154 * 2
def baseEnd_3232154 : Nat := 1659648551352252416310601

theorem tailTrace_3232154 : CollatzResearch.WordTrace tailWord_3232154 prefixEnd_3232154 1659648551352252416310601 := by
  unfold tailWord_3232154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29471585283116385200177879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78590894088310360533807677 29471585283116385200177879)
  ·
    refine ⟨44207377924674577800266819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29471585283116385200177879 44207377924674577800266819)
    ·
      refine ⟨66311066887011866700400229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44207377924674577800266819 66311066887011866700400229)
      ·
        refine ⟨12433325041314725006325043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66311066887011866700400229 12433325041314725006325043)
        ·
          refine ⟨18649987561972087509487565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12433325041314725006325043 18649987561972087509487565)
          ·
            refine ⟨6993745335739532816057837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18649987561972087509487565 6993745335739532816057837)
            ·
              refine ⟨2622654500902324806021689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6993745335739532816057837 2622654500902324806021689)
              ·
                refine ⟨1966990875676743604516267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2622654500902324806021689 1966990875676743604516267)
                ·
                  refine ⟨2950486313515115406774401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966990875676743604516267 2950486313515115406774401)
                  ·
                    refine ⟨2212864735136336555080801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2950486313515115406774401 2212864735136336555080801)
                    ·
                      refine ⟨1659648551352252416310601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2212864735136336555080801 1659648551352252416310601)
                      ·
                        rfl

theorem cell23_3232154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_3232154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232154 prefixEnd_3232154 := by exact prefixLift 3232154
  have htrace : WordTrace (prefixWord ++ tailWord_3232154) baseStart_3232154 baseEnd_3232154 := by
    simpa [prefixWord, tailWord_3232154, baseEnd_3232154] using wordTrace_append hprefix tailTrace_3232154
  have hstable : (prefixWord ++ tailWord_3232154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232154).length < 2 ^ (prefixWord ++ tailWord_3232154).sum := by decide
  have hdescent : baseEnd_3232154 < baseStart_3232154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232169 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 2, 6]
def baseStart_3232169 : Nat := 118140960795 + 3232169 * 2 ^ 59
def prefixEnd_3232169 : Nat := 4983230072969 + 3 ^ 40 * 3232169 * 2
def baseEnd_3232169 : Nat := 553218751187356619207677

theorem tailTrace_3232169 : CollatzResearch.WordTrace tailWord_3232169 prefixEnd_3232169 553218751187356619207677 := by
  unfold tailWord_3232169
  simp only [CollatzResearch.WordTrace]
  refine ⟨117886888227411198362507561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78591258818274132241671707 117886888227411198362507561)
  ·
    refine ⟨88415166170558398771880671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117886888227411198362507561 88415166170558398771880671)
    ·
      refine ⟨132622749255837598157821007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88415166170558398771880671 132622749255837598157821007)
      ·
        refine ⟨198934123883756397236731511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132622749255837598157821007 198934123883756397236731511)
        ·
          refine ⟨298401185825634595855097267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198934123883756397236731511 298401185825634595855097267)
          ·
            refine ⟨447601778738451893782645901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298401185825634595855097267 447601778738451893782645901)
            ·
              refine ⟨167850667026919460168492213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 447601778738451893782645901 167850667026919460168492213)
              ·
                refine ⟨15736000033773699390796145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167850667026919460168492213 15736000033773699390796145)
                ·
                  refine ⟨11802000025330274543097109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15736000033773699390796145 11802000025330274543097109)
                  ·
                    refine ⟨553218751187356619207677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11802000025330274543097109 553218751187356619207677)
                    ·
                      rfl

theorem cell23_3232169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_3232169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232169 prefixEnd_3232169 := by exact prefixLift 3232169
  have htrace : WordTrace (prefixWord ++ tailWord_3232169) baseStart_3232169 baseEnd_3232169 := by
    simpa [prefixWord, tailWord_3232169, baseEnd_3232169] using wordTrace_append hprefix tailTrace_3232169
  have hstable : (prefixWord ++ tailWord_3232169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232169).length < 2 ^ (prefixWord ++ tailWord_3232169).sum := by decide
  have hdescent : baseEnd_3232169 < baseStart_3232169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232206 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3232206 : Nat := 118140960795 + 3232206 * 2 ^ 59
def prefixEnd_3232206 : Nat := 4983230072969 + 3 ^ 40 * 3232206 * 2
def baseEnd_3232206 : Nat := 1659675252346286212860361

theorem tailTrace_3232206 : CollatzResearch.WordTrace tailWord_3232206 prefixEnd_3232206 1659675252346286212860361 := by
  unfold tailWord_3232206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14736029716034644210200559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78592158485518102454402981 14736029716034644210200559)
  ·
    refine ⟨22104044574051966315300839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14736029716034644210200559 22104044574051966315300839)
    ·
      refine ⟨33156066861077949472951259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22104044574051966315300839 33156066861077949472951259)
      ·
        refine ⟨49734100291616924209426889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33156066861077949472951259 49734100291616924209426889)
        ·
          refine ⟨37300575218712693157070167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49734100291616924209426889 37300575218712693157070167)
          ·
            refine ⟨55950862828069039735605251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37300575218712693157070167 55950862828069039735605251)
            ·
              refine ⟨83926294242103559603407877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55950862828069039735605251 83926294242103559603407877)
              ·
                refine ⟨15736180170394417425638977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83926294242103559603407877 15736180170394417425638977)
                ·
                  refine ⟨11802135127795813069229233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15736180170394417425638977 11802135127795813069229233)
                  ·
                    refine ⟨8851601345846859801921925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11802135127795813069229233 8851601345846859801921925)
                    ·
                      refine ⟨1659675252346286212860361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8851601345846859801921925 1659675252346286212860361)
                      ·
                        rfl

theorem cell23_3232206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3232206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232206 prefixEnd_3232206 := by exact prefixLift 3232206
  have htrace : WordTrace (prefixWord ++ tailWord_3232206) baseStart_3232206 baseEnd_3232206 := by
    simpa [prefixWord, tailWord_3232206, baseEnd_3232206] using wordTrace_append hprefix tailTrace_3232206
  have hstable : (prefixWord ++ tailWord_3232206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232206).length < 2 ^ (prefixWord ++ tailWord_3232206).sum := by decide
  have hdescent : baseEnd_3232206 < baseStart_3232206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232209 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_3232209 : Nat := 118140960795 + 3232209 * 2 ^ 59
def prefixEnd_3232209 : Nat := 4983230072969 + 3 ^ 40 * 3232209 * 2
def baseEnd_3232209 : Nat := 1659676792788249701122847

theorem tailTrace_3232209 : CollatzResearch.WordTrace tailWord_3232209 prefixEnd_3232209 1659676792788249701122847 := by
  unfold tailWord_3232209
  simp only [CollatzResearch.WordTrace]
  refine ⟨117888347147266285193963681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78592231431510856795975787 117888347147266285193963681)
  ·
    refine ⟨88416260360449713895472761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117888347147266285193963681 88416260360449713895472761)
    ·
      refine ⟨66312195270337285421604571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88416260360449713895472761 66312195270337285421604571)
      ·
        refine ⟨99468292905505928132406857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66312195270337285421604571 99468292905505928132406857)
        ·
          refine ⟨74601219679129446099305143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99468292905505928132406857 74601219679129446099305143)
          ·
            refine ⟨111901829518694169148957715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74601219679129446099305143 111901829518694169148957715)
            ·
              refine ⟨167852744278041253723436573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111901829518694169148957715 167852744278041253723436573)
              ·
                refine ⟨62944779104265470146288715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167852744278041253723436573 62944779104265470146288715)
                ·
                  refine ⟨94417168656398205219433073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62944779104265470146288715 94417168656398205219433073)
                  ·
                    refine ⟨70812876492298653914574805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94417168656398205219433073 70812876492298653914574805)
                    ·
                      refine ⟨1659676792788249701122847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70812876492298653914574805 1659676792788249701122847)
                      ·
                        rfl

theorem cell23_3232209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_3232209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232209 prefixEnd_3232209 := by exact prefixLift 3232209
  have htrace : WordTrace (prefixWord ++ tailWord_3232209) baseStart_3232209 baseEnd_3232209 := by
    simpa [prefixWord, tailWord_3232209, baseEnd_3232209] using wordTrace_append hprefix tailTrace_3232209
  have hstable : (prefixWord ++ tailWord_3232209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232209).length < 2 ^ (prefixWord ++ tailWord_3232209).sum := by decide
  have hdescent : baseEnd_3232209 < baseStart_3232209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232293 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 3, 4]
def baseStart_3232293 : Nat := 118140960795 + 3232293 * 2 ^ 59
def prefixEnd_3232293 : Nat := 4983230072969 + 3 ^ 40 * 3232293 * 2
def baseEnd_3232293 : Nat := 553239975054409124157487

theorem tailTrace_3232293 : CollatzResearch.WordTrace tailWord_3232293 prefixEnd_3232293 553239975054409124157487 := by
  unfold tailWord_3232293
  simp only [CollatzResearch.WordTrace]
  refine ⟨117891410878961967540021533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78594273919307978360014355 117891410878961967540021533)
  ·
    refine ⟨44209279079610737827508075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117891410878961967540021533 44209279079610737827508075)
    ·
      refine ⟨66313918619416106741262113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44209279079610737827508075 66313918619416106741262113)
      ·
        refine ⟨49735438964562080055946585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66313918619416106741262113 49735438964562080055946585)
        ·
          refine ⟨37301579223421560041959939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49735438964562080055946585 37301579223421560041959939)
          ·
            refine ⟨55952368835132340062939909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37301579223421560041959939 55952368835132340062939909)
            ·
              refine ⟨10491069156587313761801233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55952368835132340062939909 10491069156587313761801233)
              ·
                refine ⟨7868301867440485321350925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10491069156587313761801233 7868301867440485321350925)
                ·
                  refine ⟨2950613200290181995506597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7868301867440485321350925 2950613200290181995506597)
                  ·
                    refine ⟨553239975054409124157487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2950613200290181995506597 553239975054409124157487)
                    ·
                      rfl

theorem cell23_3232293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_3232293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232293 prefixEnd_3232293 := by exact prefixLift 3232293
  have htrace : WordTrace (prefixWord ++ tailWord_3232293) baseStart_3232293 baseEnd_3232293 := by
    simpa [prefixWord, tailWord_3232293, baseEnd_3232293] using wordTrace_append hprefix tailTrace_3232293
  have hstable : (prefixWord ++ tailWord_3232293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232293).length < 2 ^ (prefixWord ++ tailWord_3232293).sum := by decide
  have hdescent : baseEnd_3232293 < baseStart_3232293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232301 : List Nat := [1, 5, 4, 1, 1, 2, 1, 3, 5]
def baseStart_3232301 : Nat := 118140960795 + 3232301 * 2 ^ 59
def prefixEnd_3232301 : Nat := 4983230072969 + 3 ^ 40 * 3232301 * 2
def baseEnd_3232301 : Nat := 184413781445384815685825

theorem tailTrace_3232301 : CollatzResearch.WordTrace tailWord_3232301 prefixEnd_3232301 184413781445384815685825 := by
  unfold tailWord_3232301
  simp only [CollatzResearch.WordTrace]
  refine ⟨117891702662932984906312757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78594468441955323270875171 117891702662932984906312757)
  ·
    refine ⟨11052347124649967334966821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117891702662932984906312757 11052347124649967334966821)
    ·
      refine ⟨2072315085871868875306279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11052347124649967334966821 2072315085871868875306279)
      ·
        refine ⟨3108472628807803312959419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2072315085871868875306279 3108472628807803312959419)
        ·
          refine ⟨4662708943211704969439129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108472628807803312959419 4662708943211704969439129)
          ·
            refine ⟨3497031707408778727079347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4662708943211704969439129 3497031707408778727079347)
            ·
              refine ⟨5245547561113168090619021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497031707408778727079347 5245547561113168090619021)
              ·
                refine ⟨1967080335417438033982133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5245547561113168090619021 1967080335417438033982133)
                ·
                  refine ⟨184413781445384815685825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1967080335417438033982133 184413781445384815685825)
                  ·
                    rfl

theorem cell23_3232301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_3232301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232301 prefixEnd_3232301 := by exact prefixLift 3232301
  have htrace : WordTrace (prefixWord ++ tailWord_3232301) baseStart_3232301 baseEnd_3232301 := by
    simpa [prefixWord, tailWord_3232301, baseEnd_3232301] using wordTrace_append hprefix tailTrace_3232301
  have hstable : (prefixWord ++ tailWord_3232301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232301).length < 2 ^ (prefixWord ++ tailWord_3232301).sum := by decide
  have hdescent : baseEnd_3232301 < baseStart_3232301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232306 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 8]
def baseStart_3232306 : Nat := 118140960795 + 3232306 * 2 ^ 59
def prefixEnd_3232306 : Nat := 4983230072969 + 3 ^ 40 * 3232306 * 2
def baseEnd_3232306 : Nat := 184414066712415091289989

theorem tailTrace_3232306 : CollatzResearch.WordTrace tailWord_3232306 prefixEnd_3232306 184414066712415091289989 := by
  unfold tailWord_3232306
  simp only [CollatzResearch.WordTrace]
  refine ⟨29472971256978717690061193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78594590018609913840163181 29472971256978717690061193)
  ·
    refine ⟨22104728442734038267545895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29472971256978717690061193 22104728442734038267545895)
    ·
      refine ⟨33157092664101057401318843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22104728442734038267545895 33157092664101057401318843)
      ·
        refine ⟨49735638996151586101978265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33157092664101057401318843 49735638996151586101978265)
        ·
          refine ⟨37301729247113689576483699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49735638996151586101978265 37301729247113689576483699)
          ·
            refine ⟨55952593870670534364725549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37301729247113689576483699 55952593870670534364725549)
            ·
              refine ⟨20982222701501450386772081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55952593870670534364725549 20982222701501450386772081)
              ·
                refine ⟨15736667026126087790079061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20982222701501450386772081 15736667026126087790079061)
                ·
                  refine ⟨184414066712415091289989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15736667026126087790079061 184414066712415091289989)
                  ·
                    rfl

theorem cell23_3232306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_3232306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232306 prefixEnd_3232306 := by exact prefixLift 3232306
  have htrace : WordTrace (prefixWord ++ tailWord_3232306) baseStart_3232306 baseEnd_3232306 := by
    simpa [prefixWord, tailWord_3232306, baseEnd_3232306] using wordTrace_append hprefix tailTrace_3232306
  have hstable : (prefixWord ++ tailWord_3232306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232306).length < 2 ^ (prefixWord ++ tailWord_3232306).sum := by decide
  have hdescent : baseEnd_3232306 < baseStart_3232306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232340 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 6]
def baseStart_3232340 : Nat := 118140960795 + 3232340 * 2 ^ 59
def prefixEnd_3232340 : Nat := 4983230072969 + 3 ^ 40 * 3232340 * 2
def baseEnd_3232340 : Nat := 184416006528220965398305

theorem tailTrace_3232340 : CollatzResearch.WordTrace tailWord_3232340 prefixEnd_3232340 184416006528220965398305 := by
  unfold tailWord_3232340
  simp only [CollatzResearch.WordTrace]
  refine ⟨58946562554895847283491237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78595416739861129711321649 58946562554895847283491237)
  ·
    refine ⟨11052480479042971365654607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58946562554895847283491237 11052480479042971365654607)
    ·
      refine ⟨16578720718564457048481911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11052480479042971365654607 16578720718564457048481911)
      ·
        refine ⟨24868081077846685572722867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16578720718564457048481911 24868081077846685572722867)
        ·
          refine ⟨37302121616770028359084301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24868081077846685572722867 37302121616770028359084301)
          ·
            refine ⟨13988295606288760634656613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37302121616770028359084301 13988295606288760634656613)
            ·
              refine ⟨2622805426179142618998115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13988295606288760634656613 2622805426179142618998115)
              ·
                refine ⟨3934208139268713928497173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622805426179142618998115 3934208139268713928497173)
                ·
                  refine ⟨184416006528220965398305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3934208139268713928497173 184416006528220965398305)
                  ·
                    rfl

theorem cell23_3232340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_3232340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232340 prefixEnd_3232340 := by exact prefixLift 3232340
  have htrace : WordTrace (prefixWord ++ tailWord_3232340) baseStart_3232340 baseEnd_3232340 := by
    simpa [prefixWord, tailWord_3232340, baseEnd_3232340] using wordTrace_append hprefix tailTrace_3232340
  have hstable : (prefixWord ++ tailWord_3232340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232340).length < 2 ^ (prefixWord ++ tailWord_3232340).sum := by decide
  have hdescent : baseEnd_3232340 < baseStart_3232340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232353 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 3, 5]
def baseStart_3232353 : Nat := 118140960795 + 3232353 * 2 ^ 59
def prefixEnd_3232353 : Nat := 4983230072969 + 3 ^ 40 * 3232353 * 2
def baseEnd_3232353 : Nat := 553250244667499045907395

theorem tailTrace_3232353 : CollatzResearch.WordTrace tailWord_3232353 prefixEnd_3232353 553250244667499045907395 := by
  unfold tailWord_3232353
  simp only [CollatzResearch.WordTrace]
  refine ⟨117893599258744597787205713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78595732839163065191470475 117893599258744597787205713)
  ·
    refine ⟨88420199444058448340404285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117893599258744597787205713 88420199444058448340404285)
    ·
      refine ⟨33157574791521918127651607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88420199444058448340404285 33157574791521918127651607)
      ·
        refine ⟨49736362187282877191477411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33157574791521918127651607 49736362187282877191477411)
        ·
          refine ⟨74604543280924315787216117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49736362187282877191477411 74604543280924315787216117)
          ·
            refine ⟨6994175932586654605051511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74604543280924315787216117 6994175932586654605051511)
            ·
              refine ⟨10491263898879981907577267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6994175932586654605051511 10491263898879981907577267)
              ·
                refine ⟨15736895848319972861365901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10491263898879981907577267 15736895848319972861365901)
                ·
                  refine ⟨5901335943119989823012213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15736895848319972861365901 5901335943119989823012213)
                  ·
                    refine ⟨553250244667499045907395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5901335943119989823012213 553250244667499045907395)
                    ·
                      rfl

theorem cell23_3232353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_3232353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232353 prefixEnd_3232353 := by exact prefixLift 3232353
  have htrace : WordTrace (prefixWord ++ tailWord_3232353) baseStart_3232353 baseEnd_3232353 := by
    simpa [prefixWord, tailWord_3232353, baseEnd_3232353] using wordTrace_append hprefix tailTrace_3232353
  have hstable : (prefixWord ++ tailWord_3232353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232353).length < 2 ^ (prefixWord ++ tailWord_3232353).sum := by decide
  have hdescent : baseEnd_3232353 < baseStart_3232353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232354 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3232354 : Nat := 118140960795 + 3232354 * 2 ^ 59
def prefixEnd_3232354 : Nat := 4983230072969 + 3 ^ 40 * 3232354 * 2
def baseEnd_3232354 : Nat := 1659751247483151633809681

theorem tailTrace_3232354 : CollatzResearch.WordTrace tailWord_3232354 prefixEnd_3232354 1659751247483151633809681 := by
  unfold tailWord_3232354
  simp only [CollatzResearch.WordTrace]
  refine ⟨29473408932935243739498029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78595757154493983305328077 29473408932935243739498029)
  ·
    refine ⟨11052528349850716402311761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29473408932935243739498029 11052528349850716402311761)
    ·
      refine ⟨8289396262388037301733821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11052528349850716402311761 8289396262388037301733821)
      ·
        refine ⟨3108523598395513988150183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8289396262388037301733821 3108523598395513988150183)
        ·
          refine ⟨4662785397593270982225275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108523598395513988150183 4662785397593270982225275)
          ·
            refine ⟨6994178096389906473337913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4662785397593270982225275 6994178096389906473337913)
            ·
              refine ⟨5245633572292429855003435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6994178096389906473337913 5245633572292429855003435)
              ·
                refine ⟨7868450358438644782505153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5245633572292429855003435 7868450358438644782505153)
                ·
                  refine ⟨5901337768828983586878865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7868450358438644782505153 5901337768828983586878865)
                  ·
                    refine ⟨4426003326621737690159149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5901337768828983586878865 4426003326621737690159149)
                    ·
                      refine ⟨1659751247483151633809681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4426003326621737690159149 1659751247483151633809681)
                      ·
                        rfl

theorem cell23_3232354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3232354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232354 prefixEnd_3232354 := by exact prefixLift 3232354
  have htrace : WordTrace (prefixWord ++ tailWord_3232354) baseStart_3232354 baseEnd_3232354 := by
    simpa [prefixWord, tailWord_3232354, baseEnd_3232354] using wordTrace_append hprefix tailTrace_3232354
  have hstable : (prefixWord ++ tailWord_3232354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232354).length < 2 ^ (prefixWord ++ tailWord_3232354).sum := by decide
  have hdescent : baseEnd_3232354 < baseStart_3232354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232384 : List Nat := [2, 1, 1, 2, 1, 5, 4, 2, 1, 1, 3]
def baseStart_3232384 : Nat := 118140960795 + 3232384 * 2 ^ 59
def prefixEnd_3232384 : Nat := 4983230072969 + 3 ^ 40 * 3232384 * 2
def baseEnd_3232384 : Nat := 1659766651902786516434543

theorem tailTrace_3232384 : CollatzResearch.WordTrace tailWord_3232384 prefixEnd_3232384 1659766651902786516434543 := by
  unfold tailWord_3232384
  simp only [CollatzResearch.WordTrace]
  refine ⟨58947364960816145040792103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78596486614421526721056137 58947364960816145040792103)
  ·
    refine ⟨88421047441224217561188155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58947364960816145040792103 88421047441224217561188155)
    ·
      refine ⟨132631571161836326341782233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88421047441224217561188155 132631571161836326341782233)
      ·
        refine ⟨99473678371377244756336675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132631571161836326341782233 99473678371377244756336675)
        ·
          refine ⟨149210517557065867134505013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99473678371377244756336675 149210517557065867134505013)
          ·
            refine ⟨13988486020974925043859845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149210517557065867134505013 13988486020974925043859845)
            ·
              refine ⟨2622841128932798445723721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13988486020974925043859845 2622841128932798445723721)
              ·
                refine ⟨1967130846699598834292791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2622841128932798445723721 1967130846699598834292791)
                ·
                  refine ⟨2950696270049398251439187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967130846699598834292791 2950696270049398251439187)
                  ·
                    refine ⟨4426044405074097377158781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2950696270049398251439187 4426044405074097377158781)
                    ·
                      refine ⟨1659766651902786516434543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4426044405074097377158781 1659766651902786516434543)
                      ·
                        rfl

theorem cell23_3232384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 1, 1, 3].length) (baseStart_3232384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232384 prefixEnd_3232384 := by exact prefixLift 3232384
  have htrace : WordTrace (prefixWord ++ tailWord_3232384) baseStart_3232384 baseEnd_3232384 := by
    simpa [prefixWord, tailWord_3232384, baseEnd_3232384] using wordTrace_append hprefix tailTrace_3232384
  have hstable : (prefixWord ++ tailWord_3232384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232384).length < 2 ^ (prefixWord ++ tailWord_3232384).sum := by decide
  have hdescent : baseEnd_3232384 < baseStart_3232384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232396 : List Nat := [2, 2, 1, 2, 1, 1, 2, 12]
def baseStart_3232396 : Nat := 118140960795 + 3232396 * 2 ^ 59
def prefixEnd_3232396 : Nat := 4983230072969 + 3 ^ 40 * 3232396 * 2
def baseEnd_3232396 : Nat := 61473067172986684054981

theorem tailTrace_3232396 : CollatzResearch.WordTrace tailWord_3232396 prefixEnd_3232396 61473067172986684054981 := by
  unfold tailWord_3232396
  simp only [CollatzResearch.WordTrace]
  refine ⟨58947583798794408065510521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78596778398392544087347361 58947583798794408065510521)
  ·
    refine ⟨44210687849095806049132891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58947583798794408065510521 44210687849095806049132891)
    ·
      refine ⟨66316031773643709073699337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44210687849095806049132891 66316031773643709073699337)
      ·
        refine ⟨49737023830232781805274503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66316031773643709073699337 49737023830232781805274503)
        ·
          refine ⟨74605535745349172707911755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49737023830232781805274503 74605535745349172707911755)
          ·
            refine ⟨111908303618023759061867633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74605535745349172707911755 111908303618023759061867633)
            ·
              refine ⟨83931227713517819296400725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111908303618023759061867633 83931227713517819296400725)
              ·
                refine ⟨61473067172986684054981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 83931227713517819296400725 61473067172986684054981)
                ·
                  rfl

theorem cell23_3232396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 12].length) (baseStart_3232396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232396 prefixEnd_3232396 := by exact prefixLift 3232396
  have htrace : WordTrace (prefixWord ++ tailWord_3232396) baseStart_3232396 baseEnd_3232396 := by
    simpa [prefixWord, tailWord_3232396, baseEnd_3232396] using wordTrace_append hprefix tailTrace_3232396
  have hstable : (prefixWord ++ tailWord_3232396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232396).length < 2 ^ (prefixWord ++ tailWord_3232396).sum := by decide
  have hdescent : baseEnd_3232396 < baseStart_3232396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232407 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 3, 2, 2]
def baseStart_3232407 : Nat := 118140960795 + 3232407 * 2 ^ 59
def prefixEnd_3232407 : Nat := 4983230072969 + 3 ^ 40 * 3232407 * 2
def baseEnd_3232407 : Nat := 1659778461957839926446937

theorem tailTrace_3232407 : CollatzResearch.WordTrace tailWord_3232407 prefixEnd_3232407 1659778461957839926446937 := by
  unfold tailWord_3232407
  simp only [CollatzResearch.WordTrace]
  refine ⟨117895568800548965009671475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78597045867032643339780983 117895568800548965009671475)
  ·
    refine ⟨176843353200823447514507213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117895568800548965009671475 176843353200823447514507213)
    ·
      refine ⟨66316257450308792817940205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176843353200823447514507213 66316257450308792817940205)
      ·
        refine ⟨24868596543865797306727577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66316257450308792817940205 24868596543865797306727577)
        ·
          refine ⟨18651447407899347980045683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24868596543865797306727577 18651447407899347980045683)
          ·
            refine ⟨27977171111849021970068525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18651447407899347980045683 27977171111849021970068525)
            ·
              refine ⟨10491439166943383238775697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27977171111849021970068525 10491439166943383238775697)
              ·
                refine ⟨7868579375207537429081773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10491439166943383238775697 7868579375207537429081773)
                ·
                  refine ⟨2950717265702826535905665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7868579375207537429081773 2950717265702826535905665)
                  ·
                    refine ⟨2213037949277119901929249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2950717265702826535905665 2213037949277119901929249)
                    ·
                      refine ⟨1659778461957839926446937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213037949277119901929249 1659778461957839926446937)
                      ·
                        rfl

theorem cell23_3232407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_3232407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232407 prefixEnd_3232407 := by exact prefixLift 3232407
  have htrace : WordTrace (prefixWord ++ tailWord_3232407) baseStart_3232407 baseEnd_3232407 := by
    simpa [prefixWord, tailWord_3232407, baseEnd_3232407] using wordTrace_append hprefix tailTrace_3232407
  have hstable : (prefixWord ++ tailWord_3232407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232407).length < 2 ^ (prefixWord ++ tailWord_3232407).sum := by decide
  have hdescent : baseEnd_3232407 < baseStart_3232407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232430 : List Nat := [4, 1, 4, 1, 1, 2, 10]
def baseStart_3232430 : Nat := 118140960795 + 3232430 * 2 ^ 59
def prefixEnd_3232430 : Nat := 4983230072969 + 3 ^ 40 * 3232430 * 2
def baseEnd_3232430 : Nat := 20491237926085102919251

theorem tailTrace_3232430 : CollatzResearch.WordTrace tailWord_3232430 prefixEnd_3232430 20491237926085102919251 := by
  unfold tailWord_3232430
  simp only [CollatzResearch.WordTrace]
  refine ⟨14737050959933204992219843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78597605119643759958505829 14737050959933204992219843)
  ·
    refine ⟨22105576439899807488329765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14737050959933204992219843 22105576439899807488329765)
    ·
      refine ⟨4144795582481213904061831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22105576439899807488329765 4144795582481213904061831)
      ·
        refine ⟨6217193373721820856092747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144795582481213904061831 6217193373721820856092747)
        ·
          refine ⟨9325790060582731284139121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217193373721820856092747 9325790060582731284139121)
          ·
            refine ⟨6994342545437048463104341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9325790060582731284139121 6994342545437048463104341)
            ·
              refine ⟨20491237926085102919251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6994342545437048463104341 20491237926085102919251)
              ·
                rfl

theorem cell23_3232430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 10].length) (baseStart_3232430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232430 prefixEnd_3232430 := by exact prefixLift 3232430
  have htrace : WordTrace (prefixWord ++ tailWord_3232430) baseStart_3232430 baseEnd_3232430 := by
    simpa [prefixWord, tailWord_3232430, baseEnd_3232430] using wordTrace_append hprefix tailTrace_3232430
  have hstable : (prefixWord ++ tailWord_3232430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232430).length < 2 ^ (prefixWord ++ tailWord_3232430).sum := by decide
  have hdescent : baseEnd_3232430 < baseStart_3232430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232454 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3232454 : Nat := 118140960795 + 3232454 * 2 ^ 59
def prefixEnd_3232454 : Nat := 4983230072969 + 3 ^ 40 * 3232454 * 2
def baseEnd_3232454 : Nat := 1659802595548601242559221

theorem tailTrace_3232454 : CollatzResearch.WordTrace tailWord_3232454 prefixEnd_3232454 1659802595548601242559221 := by
  unfold tailWord_3232454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3684290094730584126144763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78598188687585794691088277 3684290094730584126144763)
  ·
    refine ⟨5526435142095876189217145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3684290094730584126144763 5526435142095876189217145)
    ·
      refine ⟨4144826356571907141912859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5526435142095876189217145 4144826356571907141912859)
      ·
        refine ⟨6217239534857860712869289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144826356571907141912859 6217239534857860712869289)
        ·
          refine ⟨4662929651143395534651967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6217239534857860712869289 4662929651143395534651967)
          ·
            refine ⟨6994394476715093301977951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4662929651143395534651967 6994394476715093301977951)
            ·
              refine ⟨10491591715072639952966927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6994394476715093301977951 10491591715072639952966927)
              ·
                refine ⟨15737387572608959929450391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10491591715072639952966927 15737387572608959929450391)
                ·
                  refine ⟨23606081358913439894175587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15737387572608959929450391 23606081358913439894175587)
                  ·
                    refine ⟨35409122038370159841263381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23606081358913439894175587 35409122038370159841263381)
                    ·
                      refine ⟨1659802595548601242559221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35409122038370159841263381 1659802595548601242559221)
                      ·
                        rfl

theorem cell23_3232454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3232454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232454 prefixEnd_3232454 := by exact prefixLift 3232454
  have htrace : WordTrace (prefixWord ++ tailWord_3232454) baseStart_3232454 baseEnd_3232454 := by
    simpa [prefixWord, tailWord_3232454, baseEnd_3232454] using wordTrace_append hprefix tailTrace_3232454
  have hstable : (prefixWord ++ tailWord_3232454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232454).length < 2 ^ (prefixWord ++ tailWord_3232454).sum := by decide
  have hdescent : baseEnd_3232454 < baseStart_3232454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232461 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_3232461 : Nat := 118140960795 + 3232461 * 2 ^ 59
def prefixEnd_3232461 : Nat := 4983230072969 + 3 ^ 40 * 3232461 * 2
def baseEnd_3232461 : Nat := 1659806189913182715171689

theorem tailTrace_3232461 : CollatzResearch.WordTrace tailWord_3232461 prefixEnd_3232461 1659806189913182715171689 := by
  unfold tailWord_3232461
  simp only [CollatzResearch.WordTrace]
  refine ⟨117897538342353332232137237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78598358894902221488091491 117897538342353332232137237)
  ·
    refine ⟨5526447109797812448381433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117897538342353332232137237 5526447109797812448381433)
    ·
      refine ⟨4144835332348359336286075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5526447109797812448381433 4144835332348359336286075)
      ·
        refine ⟨6217252998522539004429113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144835332348359336286075 6217252998522539004429113)
        ·
          refine ⟨4662939748891904253321835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6217252998522539004429113 4662939748891904253321835)
          ·
            refine ⟨6994409623337856379982753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4662939748891904253321835 6994409623337856379982753)
            ·
              refine ⟨5245807217503392284987065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6994409623337856379982753 5245807217503392284987065)
              ·
                refine ⟨3934355413127544213740299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5245807217503392284987065 3934355413127544213740299)
                ·
                  refine ⟨5901533119691316320610449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934355413127544213740299 5901533119691316320610449)
                  ·
                    refine ⟨4426149839768487240457837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5901533119691316320610449 4426149839768487240457837)
                    ·
                      refine ⟨1659806189913182715171689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4426149839768487240457837 1659806189913182715171689)
                      ·
                        rfl

theorem cell23_3232461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_3232461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232461 prefixEnd_3232461 := by exact prefixLift 3232461
  have htrace : WordTrace (prefixWord ++ tailWord_3232461) baseStart_3232461 baseEnd_3232461 := by
    simpa [prefixWord, tailWord_3232461, baseEnd_3232461] using wordTrace_append hprefix tailTrace_3232461
  have hstable : (prefixWord ++ tailWord_3232461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232461).length < 2 ^ (prefixWord ++ tailWord_3232461).sum := by decide
  have hdescent : baseEnd_3232461 < baseStart_3232461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232480 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 3, 4, 2]
def baseStart_3232480 : Nat := 118140960795 + 3232480 * 2 ^ 59
def prefixEnd_3232480 : Nat := 4983230072969 + 3 ^ 40 * 3232480 * 2
def baseEnd_3232480 : Nat := 1659815946045618140834101

theorem tailTrace_3232480 : CollatzResearch.WordTrace tailWord_3232480 prefixEnd_3232480 1659815946045618140834101 := by
  unfold tailWord_3232480
  simp only [CollatzResearch.WordTrace]
  refine ⟨58949115664642249238539447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78598820886189665651385929 58949115664642249238539447)
  ·
    refine ⟨88423673496963373857809171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58949115664642249238539447 88423673496963373857809171)
    ·
      refine ⟨132635510245445060786713757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88423673496963373857809171 132635510245445060786713757)
      ·
        refine ⟨49738316342041897795017659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132635510245445060786713757 49738316342041897795017659)
        ·
          refine ⟨74607474513062846692526489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49738316342041897795017659 74607474513062846692526489)
          ·
            refine ⟨55955605884797135019394867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74607474513062846692526489 55955605884797135019394867)
            ·
              refine ⟨83933408827195702529092301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55955605884797135019394867 83933408827195702529092301)
              ·
                refine ⟨31475028310198388448409613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83933408827195702529092301 31475028310198388448409613)
                ·
                  refine ⟨11803135616324395668153605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31475028310198388448409613 11803135616324395668153605)
                  ·
                    refine ⟨2213087928060824187778801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11803135616324395668153605 2213087928060824187778801)
                    ·
                      refine ⟨1659815946045618140834101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213087928060824187778801 1659815946045618140834101)
                      ·
                        rfl

theorem cell23_3232480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_3232480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232480 prefixEnd_3232480 := by exact prefixLift 3232480
  have htrace : WordTrace (prefixWord ++ tailWord_3232480) baseStart_3232480 baseEnd_3232480 := by
    simpa [prefixWord, tailWord_3232480, baseEnd_3232480] using wordTrace_append hprefix tailTrace_3232480
  have hstable : (prefixWord ++ tailWord_3232480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232480).length < 2 ^ (prefixWord ++ tailWord_3232480).sum := by decide
  have hdescent : baseEnd_3232480 < baseStart_3232480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232497 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 4, 2, 2]
def baseStart_3232497 : Nat := 118140960795 + 3232497 * 2 ^ 59
def prefixEnd_3232497 : Nat := 4983230072969 + 3 ^ 40 * 3232497 * 2
def baseEnd_3232497 : Nat := 1659824675216744574321523

theorem tailTrace_3232497 : CollatzResearch.WordTrace tailWord_3232497 prefixEnd_3232497 1659824675216744574321523 := by
  unfold tailWord_3232497
  simp only [CollatzResearch.WordTrace]
  refine ⟨117898851370222910380447745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78599234246815273586965163 117898851370222910380447745)
  ·
    refine ⟨88424138527667182785335809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117898851370222910380447745 88424138527667182785335809)
    ·
      refine ⟨66318103895750387089001857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88424138527667182785335809 66318103895750387089001857)
      ·
        refine ⟨49738577921812790316751393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66318103895750387089001857 49738577921812790316751393)
        ·
          refine ⟨37303933441359592737563545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49738577921812790316751393 37303933441359592737563545)
          ·
            refine ⟨27977950081019694553172659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37303933441359592737563545 27977950081019694553172659)
            ·
              refine ⟨41966925121529541829758989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27977950081019694553172659 41966925121529541829758989)
              ·
                refine ⟨15737596920573578186159621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41966925121529541829758989 15737596920573578186159621)
                ·
                  refine ⟨2950799422607545909904929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15737596920573578186159621 2950799422607545909904929)
                  ·
                    refine ⟨2213099566955659432428697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2950799422607545909904929 2213099566955659432428697)
                    ·
                      refine ⟨1659824675216744574321523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213099566955659432428697 1659824675216744574321523)
                      ·
                        rfl

theorem cell23_3232497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_3232497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232497 prefixEnd_3232497 := by exact prefixLift 3232497
  have htrace : WordTrace (prefixWord ++ tailWord_3232497) baseStart_3232497 baseEnd_3232497 := by
    simpa [prefixWord, tailWord_3232497, baseEnd_3232497] using wordTrace_append hprefix tailTrace_3232497
  have hstable : (prefixWord ++ tailWord_3232497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232497).length < 2 ^ (prefixWord ++ tailWord_3232497).sum := by decide
  have hdescent : baseEnd_3232497 < baseStart_3232497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232564 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_3232564 : Nat := 118140960795 + 3232564 * 2 ^ 59
def prefixEnd_3232564 : Nat := 4983230072969 + 3 ^ 40 * 3232564 * 2
def baseEnd_3232564 : Nat := 1659859078420595812183715

theorem tailTrace_3232564 : CollatzResearch.WordTrace tailWord_3232564 prefixEnd_3232564 1659859078420595812183715 := by
  unfold tailWord_3232564
  simp only [CollatzResearch.WordTrace]
  refine ⟨58950647530490090411568373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78600863373986787215424497 58950647530490090411568373)
  ·
    refine ⟨5526623205983445976084535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58950647530490090411568373 5526623205983445976084535)
    ·
      refine ⟨8289934808975168964126803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5526623205983445976084535 8289934808975168964126803)
      ·
        refine ⟨12434902213462753446190205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8289934808975168964126803 12434902213462753446190205)
        ·
          refine ⟨4663088330048532542321327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12434902213462753446190205 4663088330048532542321327)
          ·
            refine ⟨6994632495072798813481991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663088330048532542321327 6994632495072798813481991)
            ·
              refine ⟨10491948742609198220222987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6994632495072798813481991 10491948742609198220222987)
              ·
                refine ⟨15737923113913797330334481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10491948742609198220222987 15737923113913797330334481)
                ·
                  refine ⟨11803442335435347997750861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15737923113913797330334481 11803442335435347997750861)
                  ·
                    refine ⟨4426290875788255499156573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11803442335435347997750861 4426290875788255499156573)
                    ·
                      refine ⟨1659859078420595812183715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4426290875788255499156573 1659859078420595812183715)
                      ·
                        rfl

theorem cell23_3232564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_3232564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232564 prefixEnd_3232564 := by exact prefixLift 3232564
  have htrace : WordTrace (prefixWord ++ tailWord_3232564) baseStart_3232564 baseEnd_3232564 := by
    simpa [prefixWord, tailWord_3232564, baseEnd_3232564] using wordTrace_append hprefix tailTrace_3232564
  have hstable : (prefixWord ++ tailWord_3232564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232564).length < 2 ^ (prefixWord ++ tailWord_3232564).sum := by decide
  have hdescent : baseEnd_3232564 < baseStart_3232564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232604 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_3232604 : Nat := 118140960795 + 3232604 * 2 ^ 59
def prefixEnd_3232604 : Nat := 4983230072969 + 3 ^ 40 * 3232604 * 2
def baseEnd_3232604 : Nat := 1659879617646775655683531

theorem tailTrace_3232604 : CollatzResearch.WordTrace tailWord_3232604 prefixEnd_3232604 1659879617646775655683531 := by
  unfold tailWord_3232604
  simp only [CollatzResearch.WordTrace]
  refine ⟨58951376990417633827296433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78601835987223511769728577 58951376990417633827296433)
  ·
    refine ⟨44213532742813225370472325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58951376990417633827296433 44213532742813225370472325)
    ·
      refine ⟨8290037389277479756963561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44213532742813225370472325 8290037389277479756963561)
      ·
        refine ⟨6217528041958109817722671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8290037389277479756963561 6217528041958109817722671)
        ·
          refine ⟨9326292062937164726584007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217528041958109817722671 9326292062937164726584007)
          ·
            refine ⟨13989438094405747089876011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9326292062937164726584007 13989438094405747089876011)
            ·
              refine ⟨20984157141608620634814017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13989438094405747089876011 20984157141608620634814017)
              ·
                refine ⟨15738117856206465476110513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20984157141608620634814017 15738117856206465476110513)
                ·
                  refine ⟨11803588392154849107082885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15738117856206465476110513 11803588392154849107082885)
                  ·
                    refine ⟨2213172823529034207578041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11803588392154849107082885 2213172823529034207578041)
                    ·
                      refine ⟨1659879617646775655683531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213172823529034207578041 1659879617646775655683531)
                      ·
                        rfl

theorem cell23_3232604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_3232604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232604 prefixEnd_3232604 := by exact prefixLift 3232604
  have htrace : WordTrace (prefixWord ++ tailWord_3232604) baseStart_3232604 baseEnd_3232604 := by
    simpa [prefixWord, tailWord_3232604, baseEnd_3232604] using wordTrace_append hprefix tailTrace_3232604
  have hstable : (prefixWord ++ tailWord_3232604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232604).length < 2 ^ (prefixWord ++ tailWord_3232604).sum := by decide
  have hdescent : baseEnd_3232604 < baseStart_3232604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232671 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 3, 1, 3]
def baseStart_3232671 : Nat := 118140960795 + 3232671 * 2 ^ 59
def prefixEnd_3232671 : Nat := 4983230072969 + 3 ^ 40 * 3232671 * 2
def baseEnd_3232671 : Nat := 1659914020850626893545723

theorem tailTrace_3232671 : CollatzResearch.WordTrace tailWord_3232671 prefixEnd_3232671 1659914020850626893545723 := by
  unfold tailWord_3232671
  simp only [CollatzResearch.WordTrace]
  refine ⟨117905197671592538097281867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78603465114395025398187911 117905197671592538097281867)
  ·
    refine ⟨176857796507388807145922801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117905197671592538097281867 176857796507388807145922801)
    ·
      refine ⟨132643347380541605359442101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176857796507388807145922801 132643347380541605359442101)
      ·
        refine ⟨12435313816925775502447697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132643347380541605359442101 12435313816925775502447697)
        ·
          refine ⟨9326485362694331626835773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12435313816925775502447697 9326485362694331626835773)
          ·
            refine ⟨3497432011010374360063415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9326485362694331626835773 3497432011010374360063415)
            ·
              refine ⟨5246148016515561540095123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497432011010374360063415 5246148016515561540095123)
              ·
                refine ⟨7869222024773342310142685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246148016515561540095123 7869222024773342310142685)
                ·
                  refine ⟨2950958259290003366303507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7869222024773342310142685 2950958259290003366303507)
                  ·
                    refine ⟨4426437388935005049455261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2950958259290003366303507 4426437388935005049455261)
                    ·
                      refine ⟨1659914020850626893545723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4426437388935005049455261 1659914020850626893545723)
                      ·
                        rfl

theorem cell23_3232671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_3232671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232671 prefixEnd_3232671 := by exact prefixLift 3232671
  have htrace : WordTrace (prefixWord ++ tailWord_3232671) baseStart_3232671 baseEnd_3232671 := by
    simpa [prefixWord, tailWord_3232671, baseEnd_3232671] using wordTrace_append hprefix tailTrace_3232671
  have hstable : (prefixWord ++ tailWord_3232671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232671).length < 2 ^ (prefixWord ++ tailWord_3232671).sum := by decide
  have hdescent : baseEnd_3232671 < baseStart_3232671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232708 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_3232708 : Nat := 118140960795 + 3232708 * 2 ^ 59
def prefixEnd_3232708 : Nat := 4983230072969 + 3 ^ 40 * 3232708 * 2
def baseEnd_3232708 : Nat := 553311006544947749594351

theorem tailTrace_3232708 : CollatzResearch.WordTrace tailWord_3232708 prefixEnd_3232708 553311006544947749594351 := by
  unfold tailWord_3232708
  simp only [CollatzResearch.WordTrace]
  refine ⟨58953273586229246708189389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78604364781638995610919185 58953273586229246708189389)
  ·
    refine ⟨22107477594835967515571021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58953273586229246708189389 22107477594835967515571021)
    ·
      refine ⟨8290304098063487818339133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22107477594835967515571021 8290304098063487818339133)
      ·
        refine ⟨3108864036773807931877175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8290304098063487818339133 3108864036773807931877175)
        ·
          refine ⟨4663296055160711897815763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108864036773807931877175 4663296055160711897815763)
          ·
            refine ⟨6994944082741067846723645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663296055160711897815763 6994944082741067846723645)
            ·
              refine ⟨2623104031027900442521367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6994944082741067846723645 2623104031027900442521367)
              ·
                refine ⟨3934656046541850663782051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623104031027900442521367 3934656046541850663782051)
                ·
                  refine ⟨5901984069812775995673077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934656046541850663782051 5901984069812775995673077)
                  ·
                    refine ⟨553311006544947749594351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5901984069812775995673077 553311006544947749594351)
                    ·
                      rfl

theorem cell23_3232708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_3232708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232708 prefixEnd_3232708 := by exact prefixLift 3232708
  have htrace : WordTrace (prefixWord ++ tailWord_3232708) baseStart_3232708 baseEnd_3232708 := by
    simpa [prefixWord, tailWord_3232708, baseEnd_3232708] using wordTrace_append hprefix tailTrace_3232708
  have hstable : (prefixWord ++ tailWord_3232708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232708).length < 2 ^ (prefixWord ++ tailWord_3232708).sum := by decide
  have hdescent : baseEnd_3232708 < baseStart_3232708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232728 : List Nat := [2, 1, 2, 2, 2, 4, 1, 4, 1, 2, 2]
def baseStart_3232728 : Nat := 118140960795 + 3232728 * 2 ^ 59
def prefixEnd_3232728 : Nat := 4983230072969 + 3 ^ 40 * 3232728 * 2
def baseEnd_3232728 : Nat := 1659943289247933170532961

theorem tailTrace_3232728 : CollatzResearch.WordTrace tailWord_3232728 prefixEnd_3232728 1659943289247933170532961 := by
  unfold tailWord_3232728
  simp only [CollatzResearch.WordTrace]
  refine ⟨58953638316193018416053419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78604851088257357888071225 58953638316193018416053419)
  ·
    refine ⟨88430457474289527624080129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58953638316193018416053419 88430457474289527624080129)
    ·
      refine ⟨66322843105717145718060097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88430457474289527624080129 66322843105717145718060097)
      ·
        refine ⟨49742132329287859288545073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66322843105717145718060097 49742132329287859288545073)
        ·
          refine ⟨37306599246965894466408805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49742132329287859288545073 37306599246965894466408805)
          ·
            refine ⟨6994987358806105212451651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37306599246965894466408805 6994987358806105212451651)
            ·
              refine ⟨10492481038209157818677477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6994987358806105212451651 10492481038209157818677477)
              ·
                refine ⟨1967340194664217091002027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10492481038209157818677477 1967340194664217091002027)
                ·
                  refine ⟨2951010291996325636503041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967340194664217091002027 2951010291996325636503041)
                  ·
                    refine ⟨2213257718997244227377281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2951010291996325636503041 2213257718997244227377281)
                    ·
                      refine ⟨1659943289247933170532961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213257718997244227377281 1659943289247933170532961)
                      ·
                        rfl

theorem cell23_3232728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_3232728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232728 prefixEnd_3232728 := by exact prefixLift 3232728
  have htrace : WordTrace (prefixWord ++ tailWord_3232728) baseStart_3232728 baseEnd_3232728 := by
    simpa [prefixWord, tailWord_3232728, baseEnd_3232728] using wordTrace_append hprefix tailTrace_3232728
  have hstable : (prefixWord ++ tailWord_3232728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232728).length < 2 ^ (prefixWord ++ tailWord_3232728).sum := by decide
  have hdescent : baseEnd_3232728 < baseStart_3232728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232741 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3232741 : Nat := 118140960795 + 3232741 * 2 ^ 59
def prefixEnd_3232741 : Nat := 4983230072969 + 3 ^ 40 * 3232741 * 2
def baseEnd_3232741 : Nat := 1659949964496441619670401

theorem tailTrace_3232741 : CollatzResearch.WordTrace tailWord_3232741 prefixEnd_3232741 1659949964496441619670401 := by
  unfold tailWord_3232741
  simp only [CollatzResearch.WordTrace]
  refine ⟨117907750781338940052330077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78605167187559293368220051 117907750781338940052330077)
  ·
    refine ⟨44215406543002102519623779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117907750781338940052330077 44215406543002102519623779)
    ·
      refine ⟨66323109814503153779435669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44215406543002102519623779 66323109814503153779435669)
      ·
        refine ⟨3108895772554835333411047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66323109814503153779435669 3108895772554835333411047)
        ·
          refine ⟨4663343658832253000116571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108895772554835333411047 4663343658832253000116571)
          ·
            refine ⟨6995015488248379500174857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663343658832253000116571 6995015488248379500174857)
            ·
              refine ⟨5246261616186284625131143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6995015488248379500174857 5246261616186284625131143)
              ·
                refine ⟨7869392424279426937696715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246261616186284625131143 7869392424279426937696715)
                ·
                  refine ⟨11804088636419140406545073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7869392424279426937696715 11804088636419140406545073)
                  ·
                    refine ⟨8853066477314355304908805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11804088636419140406545073 8853066477314355304908805)
                    ·
                      refine ⟨1659949964496441619670401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8853066477314355304908805 1659949964496441619670401)
                      ·
                        rfl

theorem cell23_3232741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3232741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232741 prefixEnd_3232741 := by exact prefixLift 3232741
  have htrace : WordTrace (prefixWord ++ tailWord_3232741) baseStart_3232741 baseEnd_3232741 := by
    simpa [prefixWord, tailWord_3232741, baseEnd_3232741] using wordTrace_append hprefix tailTrace_3232741
  have hstable : (prefixWord ++ tailWord_3232741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232741).length < 2 ^ (prefixWord ++ tailWord_3232741).sum := by decide
  have hdescent : baseEnd_3232741 < baseStart_3232741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232760 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 3, 8]
def baseStart_3232760 : Nat := 118140960795 + 3232760 * 2 ^ 59
def prefixEnd_3232760 : Nat := 4983230072969 + 3 ^ 40 * 3232760 * 2
def baseEnd_3232760 : Nat := 553319906876292348444271

theorem tailTrace_3232760 : CollatzResearch.WordTrace tailWord_3232760 prefixEnd_3232760 553319906876292348444271 := by
  unfold tailWord_3232760
  simp only [CollatzResearch.WordTrace]
  refine ⟨58954221884135053148635867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78605629178846737531514489 58954221884135053148635867)
  ·
    refine ⟨88431332826202579722953801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58954221884135053148635867 88431332826202579722953801)
    ·
      refine ⟨66323499619651934792215351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88431332826202579722953801 66323499619651934792215351)
      ·
        refine ⟨99485249429477902188323027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66323499619651934792215351 99485249429477902188323027)
        ·
          refine ⟨149227874144216853282484541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99485249429477902188323027 149227874144216853282484541)
          ·
            refine ⟨55960452804081319980931703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149227874144216853282484541 55960452804081319980931703)
            ·
              refine ⟨83940679206121979971397555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55960452804081319980931703 83940679206121979971397555)
              ·
                refine ⟨125911018809182969957096333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83940679206121979971397555 125911018809182969957096333)
                ·
                  refine ⟨47216632053443613733911125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125911018809182969957096333 47216632053443613733911125)
                  ·
                    refine ⟨553319906876292348444271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47216632053443613733911125 553319906876292348444271)
                    ·
                      rfl

theorem cell23_3232760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_3232760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232760 prefixEnd_3232760 := by exact prefixLift 3232760
  have htrace : WordTrace (prefixWord ++ tailWord_3232760) baseStart_3232760 baseEnd_3232760 := by
    simpa [prefixWord, tailWord_3232760, baseEnd_3232760] using wordTrace_append hprefix tailTrace_3232760
  have hstable : (prefixWord ++ tailWord_3232760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232760).length < 2 ^ (prefixWord ++ tailWord_3232760).sum := by decide
  have hdescent : baseEnd_3232760 < baseStart_3232760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232778 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_3232778 : Nat := 118140960795 + 3232778 * 2 ^ 59
def prefixEnd_3232778 : Nat := 4983230072969 + 3 ^ 40 * 3232778 * 2
def baseEnd_3232778 : Nat := 1659968963280657974907731

theorem tailTrace_3232778 : CollatzResearch.WordTrace tailWord_3232778 prefixEnd_3232778 1659968963280657974907731 := by
  unfold tailWord_3232778
  simp only [CollatzResearch.WordTrace]
  refine ⟨29477275070551223842856747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78606066854803263580951325 29477275070551223842856747)
  ·
    refine ⟨44215912605826835764285121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29477275070551223842856747 44215912605826835764285121)
    ·
      refine ⟨33161934454370126823213841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44215912605826835764285121 33161934454370126823213841)
      ·
        refine ⟨24871450840777595117410381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33161934454370126823213841 24871450840777595117410381)
        ·
          refine ⟨9326794065291598169028893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24871450840777595117410381 9326794065291598169028893)
          ·
            refine ⟨3497547774484349313385835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9326794065291598169028893 3497547774484349313385835)
            ·
              refine ⟨5246321661726523970078753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497547774484349313385835 5246321661726523970078753)
              ·
                refine ⟨3934741246294892977559065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5246321661726523970078753 3934741246294892977559065)
                ·
                  refine ⟨2951055934721169733169299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3934741246294892977559065 2951055934721169733169299)
                  ·
                    refine ⟨4426583902081754599753949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2951055934721169733169299 4426583902081754599753949)
                    ·
                      refine ⟨1659968963280657974907731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4426583902081754599753949 1659968963280657974907731)
                      ·
                        rfl

theorem cell23_3232778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_3232778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232778 prefixEnd_3232778 := by exact prefixLift 3232778
  have htrace : WordTrace (prefixWord ++ tailWord_3232778) baseStart_3232778 baseEnd_3232778 := by
    simpa [prefixWord, tailWord_3232778, baseEnd_3232778] using wordTrace_append hprefix tailTrace_3232778
  have hstable : (prefixWord ++ tailWord_3232778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232778).length < 2 ^ (prefixWord ++ tailWord_3232778).sum := by decide
  have hdescent : baseEnd_3232778 < baseStart_3232778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232801 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 1, 4, 2]
def baseStart_3232801 : Nat := 118140960795 + 3232801 * 2 ^ 59
def prefixEnd_3232801 : Nat := 4983230072969 + 3 ^ 40 * 3232801 * 2
def baseEnd_3232801 : Nat := 1659980773335711384920125

theorem tailTrace_3232801 : CollatzResearch.WordTrace tailWord_3232801 prefixEnd_3232801 1659980773335711384920125 := by
  unfold tailWord_3232801
  simp only [CollatzResearch.WordTrace]
  refine ⟨117909939161121570299514257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78606626107414380199676171 117909939161121570299514257)
  ·
    refine ⟨88432454370841177724635693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117909939161121570299514257 88432454370841177724635693)
    ·
      refine ⟨33162170389065441646738385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88432454370841177724635693 33162170389065441646738385)
      ·
        refine ⟨24871627791799081235053789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33162170389065441646738385 24871627791799081235053789)
        ·
          refine ⟨9326860421924655463145171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24871627791799081235053789 9326860421924655463145171)
          ·
            refine ⟨13990290632886983194717757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9326860421924655463145171 13990290632886983194717757)
            ·
              refine ⟨5246358987332618698019159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13990290632886983194717757 5246358987332618698019159)
              ·
                refine ⟨7869538480998928047028739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246358987332618698019159 7869538480998928047028739)
                ·
                  refine ⟨11804307721498392070543109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7869538480998928047028739 11804307721498392070543109)
                  ·
                    refine ⟨2213307697780948513226833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11804307721498392070543109 2213307697780948513226833)
                    ·
                      refine ⟨1659980773335711384920125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213307697780948513226833 1659980773335711384920125)
                      ·
                        rfl

theorem cell23_3232801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_3232801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232801 prefixEnd_3232801 := by exact prefixLift 3232801
  have htrace : WordTrace (prefixWord ++ tailWord_3232801) baseStart_3232801 baseEnd_3232801 := by
    simpa [prefixWord, tailWord_3232801, baseEnd_3232801] using wordTrace_append hprefix tailTrace_3232801
  have hstable : (prefixWord ++ tailWord_3232801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232801).length < 2 ^ (prefixWord ++ tailWord_3232801).sum := by decide
  have hdescent : baseEnd_3232801 < baseStart_3232801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232837 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_3232837 : Nat := 118140960795 + 3232837 * 2 ^ 59
def prefixEnd_3232837 : Nat := 4983230072969 + 3 ^ 40 * 3232837 * 2
def baseEnd_3232837 : Nat := 553333086213091081356653

theorem tailTrace_3232837 : CollatzResearch.WordTrace tailWord_3232837 prefixEnd_3232837 553333086213091081356653 := by
  unfold tailWord_3232837
  simp only [CollatzResearch.WordTrace]
  refine ⟨117911252188991148447824765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78607501459327432298549843 117911252188991148447824765)
  ·
    refine ⟨44216719570871680667934287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117911252188991148447824765 44216719570871680667934287)
    ·
      refine ⟨66325079356307521001901431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44216719570871680667934287 66325079356307521001901431)
      ·
        refine ⟨99487619034461281502852147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66325079356307521001901431 99487619034461281502852147)
        ·
          refine ⟨149231428551691922254278221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99487619034461281502852147 149231428551691922254278221)
          ·
            refine ⟨55961785706884470845354333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149231428551691922254278221 55961785706884470845354333)
            ·
              refine ⟨20985669640081676567007875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55961785706884470845354333 20985669640081676567007875)
              ·
                refine ⟨31478504460122514850511813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20985669640081676567007875 31478504460122514850511813)
                ·
                  refine ⟨5902219586272971534470965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31478504460122514850511813 5902219586272971534470965)
                  ·
                    refine ⟨553333086213091081356653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5902219586272971534470965 553333086213091081356653)
                    ·
                      rfl

theorem cell23_3232837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_3232837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232837 prefixEnd_3232837 := by exact prefixLift 3232837
  have htrace : WordTrace (prefixWord ++ tailWord_3232837) baseStart_3232837 baseEnd_3232837 := by
    simpa [prefixWord, tailWord_3232837, baseEnd_3232837] using wordTrace_append hprefix tailTrace_3232837
  have hstable : (prefixWord ++ tailWord_3232837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232837).length < 2 ^ (prefixWord ++ tailWord_3232837).sum := by decide
  have hdescent : baseEnd_3232837 < baseStart_3232837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232844 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 2, 5, 2]
def baseStart_3232844 : Nat := 118140960795 + 3232844 * 2 ^ 59
def prefixEnd_3232844 : Nat := 4983230072969 + 3 ^ 40 * 3232844 * 2
def baseEnd_3232844 : Nat := 1660002853003854716682427

theorem tailTrace_3232844 : CollatzResearch.WordTrace tailWord_3232844 prefixEnd_3232844 1660002853003854716682427 := by
  unfold tailWord_3232844
  simp only [CollatzResearch.WordTrace]
  refine ⟨58955753749982894321664793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78607671666643859095553057 58955753749982894321664793)
  ·
    refine ⟨44216815312487170741248595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58955753749982894321664793 44216815312487170741248595)
    ·
      refine ⟨66325222968730756111872893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44216815312487170741248595 66325222968730756111872893)
      ·
        refine ⟨24871958613274033541952335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66325222968730756111872893 24871958613274033541952335)
        ·
          refine ⟨37307937919911050312928503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24871958613274033541952335 37307937919911050312928503)
          ·
            refine ⟨55961906879866575469392755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37307937919911050312928503 55961906879866575469392755)
            ·
              refine ⟨83942860319799863204089133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55961906879866575469392755 83942860319799863204089133)
              ·
                refine ⟨31478572619924948701533425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83942860319799863204089133 31478572619924948701533425)
                ·
                  refine ⟨23608929464943711526150069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31478572619924948701533425 23608929464943711526150069)
                  ·
                    refine ⟨2213337137338472955576569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23608929464943711526150069 2213337137338472955576569)
                    ·
                      refine ⟨1660002853003854716682427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213337137338472955576569 1660002853003854716682427)
                      ·
                        rfl

theorem cell23_3232844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_3232844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232844 prefixEnd_3232844 := by exact prefixLift 3232844
  have htrace : WordTrace (prefixWord ++ tailWord_3232844) baseStart_3232844 baseEnd_3232844 := by
    simpa [prefixWord, tailWord_3232844, baseEnd_3232844] using wordTrace_append hprefix tailTrace_3232844
  have hstable : (prefixWord ++ tailWord_3232844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232844).length < 2 ^ (prefixWord ++ tailWord_3232844).sum := by decide
  have hdescent : baseEnd_3232844 < baseStart_3232844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232857 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 4]
def baseStart_3232857 : Nat := 118140960795 + 3232857 * 2 ^ 59
def prefixEnd_3232857 : Nat := 4983230072969 + 3 ^ 40 * 3232857 * 2
def baseEnd_3232857 : Nat := 1660009528252363165819867

theorem tailTrace_3232857 : CollatzResearch.WordTrace tailWord_3232857 prefixEnd_3232857 1660009528252363165819867 := by
  unfold tailWord_3232857
  simp only [CollatzResearch.WordTrace]
  refine ⟨117911981648918691863552825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78607987765945794575701883 117911981648918691863552825)
  ·
    refine ⟨88433986236689018897664619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117911981648918691863552825 88433986236689018897664619)
    ·
      refine ⟨132650979355033528346496929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88433986236689018897664619 132650979355033528346496929)
      ·
        refine ⟨99488234516275146259872697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132650979355033528346496929 99488234516275146259872697)
        ·
          refine ⟨74616175887206359694904523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99488234516275146259872697 74616175887206359694904523)
          ·
            refine ⟨111924263830809539542356785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74616175887206359694904523 111924263830809539542356785)
            ·
              refine ⟨83943197873107154656767589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111924263830809539542356785 83943197873107154656767589)
              ·
                refine ⟨15739349601207591498143923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83943197873107154656767589 15739349601207591498143923)
                ·
                  refine ⟨23609024401811387247215885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15739349601207591498143923 23609024401811387247215885)
                  ·
                    refine ⟨8853384150679270217705957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23609024401811387247215885 8853384150679270217705957)
                    ·
                      refine ⟨1660009528252363165819867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8853384150679270217705957 1660009528252363165819867)
                      ·
                        rfl

theorem cell23_3232857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_3232857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232857 prefixEnd_3232857 := by exact prefixLift 3232857
  have htrace : WordTrace (prefixWord ++ tailWord_3232857) baseStart_3232857 baseEnd_3232857 := by
    simpa [prefixWord, tailWord_3232857, baseEnd_3232857] using wordTrace_append hprefix tailTrace_3232857
  have hstable : (prefixWord ++ tailWord_3232857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232857).length < 2 ^ (prefixWord ++ tailWord_3232857).sum := by decide
  have hdescent : baseEnd_3232857 < baseStart_3232857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232887 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_3232887 : Nat := 118140960795 + 3232887 * 2 ^ 59
def prefixEnd_3232887 : Nat := 4983230072969 + 3 ^ 40 * 3232887 * 2
def baseEnd_3232887 : Nat := 1660024932671998048444729

theorem tailTrace_3232887 : CollatzResearch.WordTrace tailWord_3232887 prefixEnd_3232887 1660024932671998048444729 := by
  unfold tailWord_3232887
  simp only [CollatzResearch.WordTrace]
  refine ⟨117913075838810006987144915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78608717225873337991429943 117913075838810006987144915)
  ·
    refine ⟨176869613758215010480717373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117913075838810006987144915 176869613758215010480717373)
    ·
      refine ⟨66326105159330628930269015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176869613758215010480717373 66326105159330628930269015)
      ·
        refine ⟨99489157738995943395403523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66326105159330628930269015 99489157738995943395403523)
        ·
          refine ⟨149233736608493915093105285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99489157738995943395403523 149233736608493915093105285)
          ·
            refine ⟨27981325614092609079957241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149233736608493915093105285 27981325614092609079957241)
            ·
              refine ⟨20985994210569456809967931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27981325614092609079957241 20985994210569456809967931)
              ·
                refine ⟨31478991315854185214951897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20985994210569456809967931 31478991315854185214951897)
                ·
                  refine ⟨23609243486890638911213923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31478991315854185214951897 23609243486890638911213923)
                  ·
                    refine ⟨35413865230335958366820885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23609243486890638911213923 35413865230335958366820885)
                    ·
                      refine ⟨1660024932671998048444729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35413865230335958366820885 1660024932671998048444729)
                      ·
                        rfl

theorem cell23_3232887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_3232887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232887 prefixEnd_3232887 := by exact prefixLift 3232887
  have htrace : WordTrace (prefixWord ++ tailWord_3232887) baseStart_3232887 baseEnd_3232887 := by
    simpa [prefixWord, tailWord_3232887, baseEnd_3232887] using wordTrace_append hprefix tailTrace_3232887
  have hstable : (prefixWord ++ tailWord_3232887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232887).length < 2 ^ (prefixWord ++ tailWord_3232887).sum := by decide
  have hdescent : baseEnd_3232887 < baseStart_3232887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232917 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_3232917 : Nat := 118140960795 + 3232917 * 2 ^ 59
def prefixEnd_3232917 : Nat := 4983230072969 + 3 ^ 40 * 3232917 * 2
def baseEnd_3232917 : Nat := 1660040337091632931069591

theorem tailTrace_3232917 : CollatzResearch.WordTrace tailWord_3232917 prefixEnd_3232917 1660040337091632931069591 := by
  unfold tailWord_3232917
  simp only [CollatzResearch.WordTrace]
  refine ⟨117914170028701322110737005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78609446685800881407158003 117914170028701322110737005)
  ·
    refine ⟨44217813760762995791526377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117914170028701322110737005 44217813760762995791526377)
    ·
      refine ⟨33163360320572246843644783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44217813760762995791526377 33163360320572246843644783)
      ·
        refine ⟨49745040480858370265467175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33163360320572246843644783 49745040480858370265467175)
        ·
          refine ⟨74617560721287555398200763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49745040480858370265467175 74617560721287555398200763)
          ·
            refine ⟨111926341081931333097301145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74617560721287555398200763 111926341081931333097301145)
            ·
              refine ⟨83944755811448499822975859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111926341081931333097301145 83944755811448499822975859)
              ·
                refine ⟨125917133717172749734463789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83944755811448499822975859 125917133717172749734463789)
                ·
                  refine ⟨47218925143939781150423921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125917133717172749734463789 47218925143939781150423921)
                  ·
                    refine ⟨35414193857954835862817941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47218925143939781150423921 35414193857954835862817941)
                    ·
                      refine ⟨1660040337091632931069591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35414193857954835862817941 1660040337091632931069591)
                      ·
                        rfl

theorem cell23_3232917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_3232917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232917 prefixEnd_3232917 := by exact prefixLift 3232917
  have htrace : WordTrace (prefixWord ++ tailWord_3232917) baseStart_3232917 baseEnd_3232917 := by
    simpa [prefixWord, tailWord_3232917, baseEnd_3232917] using wordTrace_append hprefix tailTrace_3232917
  have hstable : (prefixWord ++ tailWord_3232917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232917).length < 2 ^ (prefixWord ++ tailWord_3232917).sum := by decide
  have hdescent : baseEnd_3232917 < baseStart_3232917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232935 : List Nat := [1, 1, 6, 2, 1, 2, 2, 3, 1, 4]
def baseStart_3232935 : Nat := 118140960795 + 3232935 * 2 ^ 59
def prefixEnd_3232935 : Nat := 4983230072969 + 3 ^ 40 * 3232935 * 2
def baseEnd_3232935 : Nat := 553349859914471286881503

theorem tailTrace_3232935 : CollatzResearch.WordTrace tailWord_3232935 prefixEnd_3232935 553349859914471286881503 := by
  unfold tailWord_3232935
  simp only [CollatzResearch.WordTrace]
  refine ⟨117914826542636111184892259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78609884361757407456594839 117914826542636111184892259)
  ·
    refine ⟨176872239813954166777338389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117914826542636111184892259 176872239813954166777338389)
    ·
      refine ⟨8290886241279101567687737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 176872239813954166777338389 8290886241279101567687737)
      ·
        refine ⟨6218164680959326175765803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8290886241279101567687737 6218164680959326175765803)
        ·
          refine ⟨9327247021438989263648705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6218164680959326175765803 9327247021438989263648705)
          ·
            refine ⟨6995435266079241947736529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9327247021438989263648705 6995435266079241947736529)
            ·
              refine ⟨5246576449559431460802397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6995435266079241947736529 5246576449559431460802397)
              ·
                refine ⟨1967466168584786797800899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5246576449559431460802397 1967466168584786797800899)
                ·
                  refine ⟨2951199252877180196701349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967466168584786797800899 2951199252877180196701349)
                  ·
                    refine ⟨553349859914471286881503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2951199252877180196701349 553349859914471286881503)
                    ·
                      rfl

theorem cell23_3232935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_3232935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232935 prefixEnd_3232935 := by exact prefixLift 3232935
  have htrace : WordTrace (prefixWord ++ tailWord_3232935) baseStart_3232935 baseEnd_3232935 := by
    simpa [prefixWord, tailWord_3232935, baseEnd_3232935] using wordTrace_append hprefix tailTrace_3232935
  have hstable : (prefixWord ++ tailWord_3232935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232935).length < 2 ^ (prefixWord ++ tailWord_3232935).sum := by decide
  have hdescent : baseEnd_3232935 < baseStart_3232935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232944 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 1, 5]
def baseStart_3232944 : Nat := 118140960795 + 3232944 * 2 ^ 59
def prefixEnd_3232944 : Nat := 4983230072969 + 3 ^ 40 * 3232944 * 2
def baseEnd_3232944 : Nat := 553351400356434775143989

theorem tailTrace_3232944 : CollatzResearch.WordTrace tailWord_3232944 prefixEnd_3232944 553351400356434775143989 := by
  unfold tailWord_3232944
  simp only [CollatzResearch.WordTrace]
  refine ⟨58957577399801752860984943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78610103199735670481313257 58957577399801752860984943)
  ·
    refine ⟨88436366099702629291477415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58957577399801752860984943 88436366099702629291477415)
    ·
      refine ⟨132654549149553943937216123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88436366099702629291477415 132654549149553943937216123)
      ·
        refine ⟨198981823724330915905824185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132654549149553943937216123 198981823724330915905824185)
        ·
          refine ⟨149236367793248186929368139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198981823724330915905824185 149236367793248186929368139)
          ·
            refine ⟨223854551689872280394052209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149236367793248186929368139 223854551689872280394052209)
            ·
              refine ⟨167890913767404210295539157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223854551689872280394052209 167890913767404210295539157)
              ·
                refine ⟨3934943291423536178801699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 167890913767404210295539157 3934943291423536178801699)
                ·
                  refine ⟨5902414937135304268202549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934943291423536178801699 5902414937135304268202549)
                  ·
                    refine ⟨553351400356434775143989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5902414937135304268202549 553351400356434775143989)
                    ·
                      rfl

theorem cell23_3232944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 5].length) (baseStart_3232944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232944 prefixEnd_3232944 := by exact prefixLift 3232944
  have htrace : WordTrace (prefixWord ++ tailWord_3232944) baseStart_3232944 baseEnd_3232944 := by
    simpa [prefixWord, tailWord_3232944, baseEnd_3232944] using wordTrace_append hprefix tailTrace_3232944
  have hstable : (prefixWord ++ tailWord_3232944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232944).length < 2 ^ (prefixWord ++ tailWord_3232944).sum := by decide
  have hdescent : baseEnd_3232944 < baseStart_3232944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232951 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 4, 3, 2]
def baseStart_3232951 : Nat := 118140960795 + 3232951 * 2 ^ 59
def prefixEnd_3232951 : Nat := 4983230072969 + 3 ^ 40 * 3232951 * 2
def baseEnd_3232951 : Nat := 1660057795433885798044435

theorem tailTrace_3232951 : CollatzResearch.WordTrace tailWord_3232951 prefixEnd_3232951 1660057795433885798044435 := by
  unfold tailWord_3232951
  simp only [CollatzResearch.WordTrace]
  refine ⟨117915410110578145917474707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78610273407052097278316471 117915410110578145917474707)
  ·
    refine ⟨176873115165867218876212061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117915410110578145917474707 176873115165867218876212061)
    ·
      refine ⟨66327418187200207078579523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176873115165867218876212061 66327418187200207078579523)
      ·
        refine ⟨99491127280800310617869285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66327418187200207078579523 99491127280800310617869285)
        ·
          refine ⟨18654586365150058240850491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99491127280800310617869285 18654586365150058240850491)
          ·
            refine ⟨27981879547725087361275737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18654586365150058240850491 27981879547725087361275737)
            ·
              refine ⟨20986409660793815520956803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27981879547725087361275737 20986409660793815520956803)
              ·
                refine ⟨31479614491190723281435205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20986409660793815520956803 31479614491190723281435205)
                ·
                  refine ⟨5902427717098260615269101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31479614491190723281435205 5902427717098260615269101)
                  ·
                    refine ⟨2213410393911847730725913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5902427717098260615269101 2213410393911847730725913)
                    ·
                      refine ⟨1660057795433885798044435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213410393911847730725913 1660057795433885798044435)
                      ·
                        rfl

theorem cell23_3232951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 3, 2].length) (baseStart_3232951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232951 prefixEnd_3232951 := by exact prefixLift 3232951
  have htrace : WordTrace (prefixWord ++ tailWord_3232951) baseStart_3232951 baseEnd_3232951 := by
    simpa [prefixWord, tailWord_3232951, baseEnd_3232951] using wordTrace_append hprefix tailTrace_3232951
  have hstable : (prefixWord ++ tailWord_3232951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232951).length < 2 ^ (prefixWord ++ tailWord_3232951).sum := by decide
  have hdescent : baseEnd_3232951 < baseStart_3232951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3232958 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_3232958 : Nat := 118140960795 + 3232958 * 2 ^ 59
def prefixEnd_3232958 : Nat := 4983230072969 + 3 ^ 40 * 3232958 * 2
def baseEnd_3232958 : Nat := 1660061389798467270656903

theorem tailTrace_3232958 : CollatzResearch.WordTrace tailWord_3232958 prefixEnd_3232958 1660061389798467270656903 := by
  unfold tailWord_3232958
  simp only [CollatzResearch.WordTrace]
  refine ⟨14739458177694098264122441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78610443614368524075319685 14739458177694098264122441)
  ·
    refine ⟨11054593633270573698091831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14739458177694098264122441 11054593633270573698091831)
    ·
      refine ⟨16581890449905860547137747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11054593633270573698091831 16581890449905860547137747)
      ·
        refine ⟨24872835674858790820706621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16581890449905860547137747 24872835674858790820706621)
        ·
          refine ⟨9327313378072046557764983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24872835674858790820706621 9327313378072046557764983)
          ·
            refine ⟨13990970067108069836647475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9327313378072046557764983 13990970067108069836647475)
            ·
              refine ⟨20986455100662104754971213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13990970067108069836647475 20986455100662104754971213)
              ·
                refine ⟨7869920662748289283114205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20986455100662104754971213 7869920662748289283114205)
                ·
                  refine ⟨2951220248530608481167827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7869920662748289283114205 2951220248530608481167827)
                  ·
                    refine ⟨4426830372795912721751741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2951220248530608481167827 4426830372795912721751741)
                    ·
                      refine ⟨1660061389798467270656903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4426830372795912721751741 1660061389798467270656903)
                      ·
                        rfl

theorem cell23_3232958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_3232958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3232958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3232958 prefixEnd_3232958 := by exact prefixLift 3232958
  have htrace : WordTrace (prefixWord ++ tailWord_3232958) baseStart_3232958 baseEnd_3232958 := by
    simpa [prefixWord, tailWord_3232958, baseEnd_3232958] using wordTrace_append hprefix tailTrace_3232958
  have hstable : (prefixWord ++ tailWord_3232958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3232958).length < 2 ^ (prefixWord ++ tailWord_3232958).sum := by decide
  have hdescent : baseEnd_3232958 < baseStart_3232958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3232958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233004 : List Nat := [2, 2, 1, 1, 2, 6, 9]
def baseStart_3233004 : Nat := 118140960795 + 3233004 * 2 ^ 59
def prefixEnd_3233004 : Nat := 4983230072969 + 3 ^ 40 * 3233004 * 2
def baseEnd_3233004 : Nat := 20494876665537951736811

theorem tailTrace_3233004 : CollatzResearch.WordTrace tailWord_3233004 prefixEnd_3233004 20494876665537951736811 := by
  unfold tailWord_3233004
  simp only [CollatzResearch.WordTrace]
  refine ⟨58958671589693067984577033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78611562119590757312769377 58958671589693067984577033)
  ·
    refine ⟨44219003692269800988432775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58958671589693067984577033 44219003692269800988432775)
    ·
      refine ⟨66328505538404701482649163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44219003692269800988432775 66328505538404701482649163)
      ·
        refine ⟨99492758307607052223973745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66328505538404701482649163 99492758307607052223973745)
        ·
          refine ⟨74619568730705289167980309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99492758307607052223973745 74619568730705289167980309)
          ·
            refine ⟨3497792284251810429749077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74619568730705289167980309 3497792284251810429749077)
            ·
              refine ⟨20494876665537951736811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3497792284251810429749077 20494876665537951736811)
              ·
                rfl

theorem cell23_3233004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 9].length) (baseStart_3233004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233004 prefixEnd_3233004 := by exact prefixLift 3233004
  have htrace : WordTrace (prefixWord ++ tailWord_3233004) baseStart_3233004 baseEnd_3233004 := by
    simpa [prefixWord, tailWord_3233004, baseEnd_3233004] using wordTrace_append hprefix tailTrace_3233004
  have hstable : (prefixWord ++ tailWord_3233004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233004).length < 2 ^ (prefixWord ++ tailWord_3233004).sum := by decide
  have hdescent : baseEnd_3233004 < baseStart_3233004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233025 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 2, 4]
def baseStart_3233025 : Nat := 118140960795 + 3233025 * 2 ^ 59
def prefixEnd_3233025 : Nat := 4983230072969 + 3 ^ 40 * 3233025 * 2
def baseEnd_3233025 : Nat := 553365264334106169506365

theorem tailTrace_3233025 : CollatzResearch.WordTrace tailWord_3233025 prefixEnd_3233025 553365264334106169506365 := by
  unfold tailWord_3233025
  simp only [CollatzResearch.WordTrace]
  refine ⟨117918109112310056555668529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78612072741540037703779019 117918109112310056555668529)
  ·
    refine ⟨88438581834232542416751397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117918109112310056555668529 88438581834232542416751397)
    ·
      refine ⟨16582234093918601703140887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88438581834232542416751397 16582234093918601703140887)
      ·
        refine ⟨24873351140877902554711331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16582234093918601703140887 24873351140877902554711331)
        ·
          refine ⟨37310026711316853832066997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24873351140877902554711331 37310026711316853832066997)
          ·
            refine ⟨3497815004185955046756281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37310026711316853832066997 3497815004185955046756281)
            ·
              refine ⟨2623361253139466285067211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3497815004185955046756281 2623361253139466285067211)
              ·
                refine ⟨3935041879709199427600817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623361253139466285067211 3935041879709199427600817)
                ·
                  refine ⟨2951281409781899570700613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3935041879709199427600817 2951281409781899570700613)
                  ·
                    refine ⟨553365264334106169506365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2951281409781899570700613 553365264334106169506365)
                    ·
                      rfl

theorem cell23_3233025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_3233025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233025 prefixEnd_3233025 := by exact prefixLift 3233025
  have htrace : WordTrace (prefixWord ++ tailWord_3233025) baseStart_3233025 baseEnd_3233025 := by
    simpa [prefixWord, tailWord_3233025, baseEnd_3233025] using wordTrace_append hprefix tailTrace_3233025
  have hstable : (prefixWord ++ tailWord_3233025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233025).length < 2 ^ (prefixWord ++ tailWord_3233025).sum := by decide
  have hdescent : baseEnd_3233025 < baseStart_3233025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233066 : List Nat := [3, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_3233066 : Nat := 118140960795 + 3233066 * 2 ^ 59
def prefixEnd_3233066 : Nat := 4983230072969 + 3 ^ 40 * 3233066 * 2
def baseEnd_3233066 : Nat := 1660116845709152848106407

theorem tailTrace_3233066 : CollatzResearch.WordTrace tailWord_3233066 prefixEnd_3233066 1660116845709152848106407 := by
  unfold tailWord_3233066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29479901126290380139477763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78613069670107680371940701 29479901126290380139477763)
  ·
    refine ⟨44219851689435570209216645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29479901126290380139477763 44219851689435570209216645)
    ·
      refine ⟨8291222191769169414228121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44219851689435570209216645 8291222191769169414228121)
      ·
        refine ⟨6218416643826877060671091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8291222191769169414228121 6218416643826877060671091)
        ·
          refine ⟨9327624965740315591006637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6218416643826877060671091 9327624965740315591006637)
          ·
            refine ⟨3497859362152618346627489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9327624965740315591006637 3497859362152618346627489)
            ·
              refine ⟨2623394521614463759970617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3497859362152618346627489 2623394521614463759970617)
              ·
                refine ⟨1967545891210847819977963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623394521614463759970617 1967545891210847819977963)
                ·
                  refine ⟨2951318836816271729966945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967545891210847819977963 2951318836816271729966945)
                  ·
                    refine ⟨2213489127612203797475209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2951318836816271729966945 2213489127612203797475209)
                    ·
                      refine ⟨1660116845709152848106407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213489127612203797475209 1660116845709152848106407)
                      ·
                        rfl

theorem cell23_3233066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_3233066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233066 prefixEnd_3233066 := by exact prefixLift 3233066
  have htrace : WordTrace (prefixWord ++ tailWord_3233066) baseStart_3233066 baseEnd_3233066 := by
    simpa [prefixWord, tailWord_3233066, baseEnd_3233066] using wordTrace_append hprefix tailTrace_3233066
  have hstable : (prefixWord ++ tailWord_3233066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233066).length < 2 ^ (prefixWord ++ tailWord_3233066).sum := by decide
  have hdescent : baseEnd_3233066 < baseStart_3233066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233071 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 5, 4, 2]
def baseStart_3233071 : Nat := 118140960795 + 3233071 * 2 ^ 59
def prefixEnd_3233071 : Nat := 4983230072969 + 3 ^ 40 * 3233071 * 2
def baseEnd_3233071 : Nat := 1660119413112425328543883

theorem tailTrace_3233071 : CollatzResearch.WordTrace tailWord_3233071 prefixEnd_3233071 1660119413112425328543883 := by
  unfold tailWord_3233071
  simp only [CollatzResearch.WordTrace]
  refine ⟨117919786870143406411843067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78613191246762270941228711 117919786870143406411843067)
  ·
    refine ⟨176879680305215109617764601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117919786870143406411843067 176879680305215109617764601)
    ·
      refine ⟨132659760228911332213323451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176879680305215109617764601 132659760228911332213323451)
      ·
        refine ⟨198989640343366998319985177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132659760228911332213323451 198989640343366998319985177)
        ·
          refine ⟨149242230257525248739988883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198989640343366998319985177 149242230257525248739988883)
          ·
            refine ⟨223863345386287873109983325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149242230257525248739988883 223863345386287873109983325)
            ·
              refine ⟨83948754519857952416243747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223863345386287873109983325 83948754519857952416243747)
              ·
                refine ⟨125923131779786928624365621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83948754519857952416243747 125923131779786928624365621)
                ·
                  refine ⟨11805293604355024558534277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125923131779786928624365621 11805293604355024558534277)
                  ·
                    refine ⟨2213492550816567104725177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11805293604355024558534277 2213492550816567104725177)
                    ·
                      refine ⟨1660119413112425328543883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213492550816567104725177 1660119413112425328543883)
                      ·
                        rfl

theorem cell23_3233071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 4, 2].length) (baseStart_3233071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233071 prefixEnd_3233071 := by exact prefixLift 3233071
  have htrace : WordTrace (prefixWord ++ tailWord_3233071) baseStart_3233071 baseEnd_3233071 := by
    simpa [prefixWord, tailWord_3233071, baseEnd_3233071] using wordTrace_append hprefix tailTrace_3233071
  have hstable : (prefixWord ++ tailWord_3233071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233071).length < 2 ^ (prefixWord ++ tailWord_3233071).sum := by decide
  have hdescent : baseEnd_3233071 < baseStart_3233071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233088 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 1, 4, 2]
def baseStart_3233088 : Nat := 118140960795 + 3233088 * 2 ^ 59
def prefixEnd_3233088 : Nat := 4983230072969 + 3 ^ 40 * 3233088 * 2
def baseEnd_3233088 : Nat := 1660128142283551762031305

theorem tailTrace_3233088 : CollatzResearch.WordTrace tailWord_3233088 prefixEnd_3233088 1660128142283551762031305 := by
  unfold tailWord_3233088
  simp only [CollatzResearch.WordTrace]
  refine ⟨58960203455540909157605959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78613604607387878876807945 58960203455540909157605959)
  ·
    refine ⟨88440305183311363736408939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58960203455540909157605959 88440305183311363736408939)
    ·
      refine ⟨132660457774967045604613409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88440305183311363736408939 132660457774967045604613409)
      ·
        refine ⟨99495343331225284203460057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132660457774967045604613409 99495343331225284203460057)
        ·
          refine ⟨74621507498418963152595043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99495343331225284203460057 74621507498418963152595043)
          ·
            refine ⟨111932261247628444728892565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74621507498418963152595043 111932261247628444728892565)
            ·
              refine ⟨5246824745982583346666839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111932261247628444728892565 5246824745982583346666839)
              ·
                refine ⟨7870237118973875020000259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246824745982583346666839 7870237118973875020000259)
                ·
                  refine ⟨11805355678460812530000389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7870237118973875020000259 11805355678460812530000389)
                  ·
                    refine ⟨2213504189711402349375073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11805355678460812530000389 2213504189711402349375073)
                    ·
                      refine ⟨1660128142283551762031305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213504189711402349375073 1660128142283551762031305)
                      ·
                        rfl

theorem cell23_3233088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 4, 2].length) (baseStart_3233088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233088 prefixEnd_3233088 := by exact prefixLift 3233088
  have htrace : WordTrace (prefixWord ++ tailWord_3233088) baseStart_3233088 baseEnd_3233088 := by
    simpa [prefixWord, tailWord_3233088, baseEnd_3233088] using wordTrace_append hprefix tailTrace_3233088
  have hstable : (prefixWord ++ tailWord_3233088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233088).length < 2 ^ (prefixWord ++ tailWord_3233088).sum := by decide
  have hdescent : baseEnd_3233088 < baseStart_3233088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233128 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 7]
def baseStart_3233128 : Nat := 118140960795 + 3233128 * 2 ^ 59
def prefixEnd_3233128 : Nat := 4983230072969 + 3 ^ 40 * 3233128 * 2
def baseEnd_3233128 : Nat := 184460964612192400614569

theorem tailTrace_3233128 : CollatzResearch.WordTrace tailWord_3233128 prefixEnd_3233128 184460964612192400614569 := by
  unfold tailWord_3233128
  simp only [CollatzResearch.WordTrace]
  refine ⟨58960932915468452573334019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78614577220624603431112025 58960932915468452573334019)
  ·
    refine ⟨88441399373202678860001029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58960932915468452573334019 88441399373202678860001029)
    ·
      refine ⟨16582762382475502286250193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88441399373202678860001029 16582762382475502286250193)
      ·
        refine ⟨12437071786856626714687645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16582762382475502286250193 12437071786856626714687645)
        ·
          refine ⟨4663901920071235018007867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12437071786856626714687645 4663901920071235018007867)
          ·
            refine ⟨6995852880106852527011801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663901920071235018007867 6995852880106852527011801)
            ·
              refine ⟨5246889660080139395258851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6995852880106852527011801 5246889660080139395258851)
              ·
                refine ⟨7870334490120209092888277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246889660080139395258851 7870334490120209092888277)
                ·
                  refine ⟨184460964612192400614569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7870334490120209092888277 184460964612192400614569)
                  ·
                    rfl

theorem cell23_3233128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 7].length) (baseStart_3233128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233128 prefixEnd_3233128 := by exact prefixLift 3233128
  have htrace : WordTrace (prefixWord ++ tailWord_3233128) baseStart_3233128 baseEnd_3233128 := by
    simpa [prefixWord, tailWord_3233128, baseEnd_3233128] using wordTrace_append hprefix tailTrace_3233128
  have hstable : (prefixWord ++ tailWord_3233128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233128).length < 2 ^ (prefixWord ++ tailWord_3233128).sum := by decide
  have hdescent : baseEnd_3233128 < baseStart_3233128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233178 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_3233178 : Nat := 118140960795 + 3233178 * 2 ^ 59
def prefixEnd_3233178 : Nat := 4983230072969 + 3 ^ 40 * 3233178 * 2
def baseEnd_3233178 : Nat := 1660174355542456409905891

theorem tailTrace_3233178 : CollatzResearch.WordTrace tailWord_3233178 prefixEnd_3233178 1660174355542456409905891 := by
  unfold tailWord_3233178
  simp only [CollatzResearch.WordTrace]
  refine ⟨29480922370188940921497047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78615792987170509123992125 29480922370188940921497047)
  ·
    refine ⟨44221383555283411382245571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29480922370188940921497047 44221383555283411382245571)
    ·
      refine ⟨66332075332925117073368357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44221383555283411382245571 66332075332925117073368357)
      ·
        refine ⟨12437264124923459451256567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66332075332925117073368357 12437264124923459451256567)
        ·
          refine ⟨18655896187385189176884851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12437264124923459451256567 18655896187385189176884851)
          ·
            refine ⟨27983844281077783765327277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18655896187385189176884851 27983844281077783765327277)
            ·
              refine ⟨10493941605404168911997729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27983844281077783765327277 10493941605404168911997729)
              ·
                refine ⟨7870456204053126683998297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10493941605404168911997729 7870456204053126683998297)
                ·
                  refine ⟨5902842153039845012998723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7870456204053126683998297 5902842153039845012998723)
                  ·
                    refine ⟨8854263229559767519498085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5902842153039845012998723 8854263229559767519498085)
                    ·
                      refine ⟨1660174355542456409905891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8854263229559767519498085 1660174355542456409905891)
                      ·
                        rfl

theorem cell23_3233178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_3233178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233178 prefixEnd_3233178 := by exact prefixLift 3233178
  have htrace : WordTrace (prefixWord ++ tailWord_3233178) baseStart_3233178 baseEnd_3233178 := by
    simpa [prefixWord, tailWord_3233178, baseEnd_3233178] using wordTrace_append hprefix tailTrace_3233178
  have hstable : (prefixWord ++ tailWord_3233178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233178).length < 2 ^ (prefixWord ++ tailWord_3233178).sum := by decide
  have hdescent : baseEnd_3233178 < baseStart_3233178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233271 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_3233271 : Nat := 118140960795 + 3233271 * 2 ^ 59
def prefixEnd_3233271 : Nat := 4983230072969 + 3 ^ 40 * 3233271 * 2
def baseEnd_3233271 : Nat := 1660222109243324546042963

theorem tailTrace_3233271 : CollatzResearch.WordTrace tailWord_3233271 prefixEnd_3233271 1660222109243324546042963 := by
  unfold tailWord_3233271
  simp only [CollatzResearch.WordTrace]
  refine ⟨117927081469418840569123667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78618054312945893712749111 117927081469418840569123667)
  ·
    refine ⟨176890622204128260853685501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117927081469418840569123667 176890622204128260853685501)
    ·
      refine ⟨66333983326548097820132063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176890622204128260853685501 66333983326548097820132063)
      ·
        refine ⟨99500974989822146730198095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66333983326548097820132063 99500974989822146730198095)
        ·
          refine ⟨149251462484733220095297143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99500974989822146730198095 149251462484733220095297143)
          ·
            refine ⟨223877193727099830142945715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149251462484733220095297143 223877193727099830142945715)
            ·
              refine ⟨335815790590649745214418573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223877193727099830142945715 335815790590649745214418573)
              ·
                refine ⟨125930921471493654455406965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335815790590649745214418573 125930921471493654455406965)
                ·
                  refine ⟨11806023887952530105194403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125930921471493654455406965 11806023887952530105194403)
                  ·
                    refine ⟨17709035831928795157791605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11806023887952530105194403 17709035831928795157791605)
                    ·
                      refine ⟨1660222109243324546042963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17709035831928795157791605 1660222109243324546042963)
                      ·
                        rfl

theorem cell23_3233271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_3233271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233271 prefixEnd_3233271 := by exact prefixLift 3233271
  have htrace : WordTrace (prefixWord ++ tailWord_3233271) baseStart_3233271 baseEnd_3233271 := by
    simpa [prefixWord, tailWord_3233271, baseEnd_3233271] using wordTrace_append hprefix tailTrace_3233271
  have hstable : (prefixWord ++ tailWord_3233271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233271).length < 2 ^ (prefixWord ++ tailWord_3233271).sum := by decide
  have hdescent : baseEnd_3233271 < baseStart_3233271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233272 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 2, 3, 2]
def baseStart_3233272 : Nat := 118140960795 + 3233272 * 2 ^ 59
def prefixEnd_3233272 : Nat := 4983230072969 + 3 ^ 40 * 3233272 * 2
def baseEnd_3233272 : Nat := 1660222622723979042130459

theorem tailTrace_3233272 : CollatzResearch.WordTrace tailWord_3233272 prefixEnd_3233272 1660222622723979042130459 := by
  unfold tailWord_3233272
  simp only [CollatzResearch.WordTrace]
  refine ⟨58963558971207608869955035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78618078628276811826606713 58963558971207608869955035)
  ·
    refine ⟨88445338456811413304932553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58963558971207608869955035 88445338456811413304932553)
    ·
      refine ⟨66334003842608559978699415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88445338456811413304932553 66334003842608559978699415)
      ·
        refine ⟨99501005763912839968049123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66334003842608559978699415 99501005763912839968049123)
        ·
          refine ⟨149251508645869259952073685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99501005763912839968049123 149251508645869259952073685)
          ·
            refine ⟨3498082233887560780126727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 149251508645869259952073685 3498082233887560780126727)
            ·
              refine ⟨5247123350831341170190091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3498082233887560780126727 5247123350831341170190091)
              ·
                refine ⟨7870685026247011755285137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5247123350831341170190091 7870685026247011755285137)
                ·
                  refine ⟨5903013769685258816463853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7870685026247011755285137 5903013769685258816463853)
                  ·
                    refine ⟨2213630163631972056173945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5903013769685258816463853 2213630163631972056173945)
                    ·
                      refine ⟨1660222622723979042130459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213630163631972056173945 1660222622723979042130459)
                      ·
                        rfl

theorem cell23_3233272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 3, 2].length) (baseStart_3233272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233272 prefixEnd_3233272 := by exact prefixLift 3233272
  have htrace : WordTrace (prefixWord ++ tailWord_3233272) baseStart_3233272 baseEnd_3233272 := by
    simpa [prefixWord, tailWord_3233272, baseEnd_3233272] using wordTrace_append hprefix tailTrace_3233272
  have hstable : (prefixWord ++ tailWord_3233272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233272).length < 2 ^ (prefixWord ++ tailWord_3233272).sum := by decide
  have hdescent : baseEnd_3233272 < baseStart_3233272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233282 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_3233282 : Nat := 118140960795 + 3233282 * 2 ^ 59
def prefixEnd_3233282 : Nat := 4983230072969 + 3 ^ 40 * 3233282 * 2
def baseEnd_3233282 : Nat := 553409252510174667668471

theorem tailTrace_3233282 : CollatzResearch.WordTrace tailWord_3233282 prefixEnd_3233282 553409252510174667668471 := by
  unfold tailWord_3233282
  simp only [CollatzResearch.WordTrace]
  refine ⟨29481870668094747361943525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78618321781585992965182733 29481870668094747361943525)
  ·
    refine ⟨5527850750267765130364411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29481870668094747361943525 5527850750267765130364411)
    ·
      refine ⟨8291776125401647695546617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5527850750267765130364411 8291776125401647695546617)
      ·
        refine ⟨6218832094051235771659963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8291776125401647695546617 6218832094051235771659963)
        ·
          refine ⟨9328248141076853657489945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6218832094051235771659963 9328248141076853657489945)
          ·
            refine ⟨6996186105807640243117459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9328248141076853657489945 6996186105807640243117459)
            ·
              refine ⟨10494279158711460364676189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6996186105807640243117459 10494279158711460364676189)
              ·
                refine ⟨3935354684516797636753571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10494279158711460364676189 3935354684516797636753571)
                ·
                  refine ⟨5903032026775196455130357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3935354684516797636753571 5903032026775196455130357)
                  ·
                    refine ⟨553409252510174667668471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5903032026775196455130357 553409252510174667668471)
                    ·
                      rfl

theorem cell23_3233282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_3233282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233282 prefixEnd_3233282 := by exact prefixLift 3233282
  have htrace : WordTrace (prefixWord ++ tailWord_3233282) baseStart_3233282 baseEnd_3233282 := by
    simpa [prefixWord, tailWord_3233282, baseEnd_3233282] using wordTrace_append hprefix tailTrace_3233282
  have hstable : (prefixWord ++ tailWord_3233282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233282).length < 2 ^ (prefixWord ++ tailWord_3233282).sum := by decide
  have hdescent : baseEnd_3233282 < baseStart_3233282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233285 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 7, 2, 2]
def baseStart_3233285 : Nat := 118140960795 + 3233285 * 2 ^ 59
def prefixEnd_3233285 : Nat := 4983230072969 + 3 ^ 40 * 3233285 * 2
def baseEnd_3233285 : Nat := 1660229297972487491267899

theorem tailTrace_3233285 : CollatzResearch.WordTrace tailWord_3233285 prefixEnd_3233285 1660229297972487491267899 := by
  unfold tailWord_3233285
  simp only [CollatzResearch.WordTrace]
  refine ⟨117927592091368120960133309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78618394727578747306755539 117927592091368120960133309)
  ·
    refine ⟨44222847034263045360049991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117927592091368120960133309 44222847034263045360049991)
    ·
      refine ⟨66334270551394568040074987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44222847034263045360049991 66334270551394568040074987)
      ·
        refine ⟨99501405827091852060112481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66334270551394568040074987 99501405827091852060112481)
        ·
          refine ⟨74626054370318889045084361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99501405827091852060112481 74626054370318889045084361)
          ·
            refine ⟨55969540777739166783813271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74626054370318889045084361 55969540777739166783813271)
            ·
              refine ⟨83954311166608750175719907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55969540777739166783813271 83954311166608750175719907)
              ·
                refine ⟨125931466749913125263579861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83954311166608750175719907 125931466749913125263579861)
                ·
                  refine ⟨2951518751951088873365153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 125931466749913125263579861 2951518751951088873365153)
                  ·
                    refine ⟨2213639063963316655023865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2951518751951088873365153 2213639063963316655023865)
                    ·
                      refine ⟨1660229297972487491267899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213639063963316655023865 1660229297972487491267899)
                      ·
                        rfl

theorem cell23_3233285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 2, 2].length) (baseStart_3233285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233285 prefixEnd_3233285 := by exact prefixLift 3233285
  have htrace : WordTrace (prefixWord ++ tailWord_3233285) baseStart_3233285 baseEnd_3233285 := by
    simpa [prefixWord, tailWord_3233285, baseEnd_3233285] using wordTrace_append hprefix tailTrace_3233285
  have hstable : (prefixWord ++ tailWord_3233285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233285).length < 2 ^ (prefixWord ++ tailWord_3233285).sum := by decide
  have hdescent : baseEnd_3233285 < baseStart_3233285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233286 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_3233286 : Nat := 118140960795 + 3233286 * 2 ^ 59
def prefixEnd_3233286 : Nat := 4983230072969 + 3 ^ 40 * 3233286 * 2
def baseEnd_3233286 : Nat := 184469979050349109706155

theorem tailTrace_3233286 : CollatzResearch.WordTrace tailWord_3233286 prefixEnd_3233286 184469979050349109706155 := by
  unfold tailWord_3233286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685238392636390566591241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78618419042909665420613141 3685238392636390566591241)
  ·
    refine ⟨2763928794477292924943431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3685238392636390566591241 2763928794477292924943431)
    ·
      refine ⟨4145893191715939387415147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2763928794477292924943431 4145893191715939387415147)
      ·
        refine ⟨6218839787573909081122721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4145893191715939387415147 6218839787573909081122721)
        ·
          refine ⟨4664129840680431810842041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6218839787573909081122721 4664129840680431810842041)
          ·
            refine ⟨3498097380510323858131531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4664129840680431810842041 3498097380510323858131531)
            ·
              refine ⟨5247146070765485787197297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3498097380510323858131531 5247146070765485787197297)
              ·
                refine ⟨3935359553074114340397973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5247146070765485787197297 3935359553074114340397973)
                ·
                  refine ⟨184469979050349109706155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3935359553074114340397973 184469979050349109706155)
                  ·
                    rfl

theorem cell23_3233286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_3233286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233286 prefixEnd_3233286 := by exact prefixLift 3233286
  have htrace : WordTrace (prefixWord ++ tailWord_3233286) baseStart_3233286 baseEnd_3233286 := by
    simpa [prefixWord, tailWord_3233286, baseEnd_3233286] using wordTrace_append hprefix tailTrace_3233286
  have hstable : (prefixWord ++ tailWord_3233286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233286).length < 2 ^ (prefixWord ++ tailWord_3233286).sum := by decide
  have hdescent : baseEnd_3233286 < baseStart_3233286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233322 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_3233322 : Nat := 118140960795 + 3233322 * 2 ^ 59
def prefixEnd_3233322 : Nat := 4983230072969 + 3 ^ 40 * 3233322 * 2
def baseEnd_3233322 : Nat := 1660248296756703846505229

theorem tailTrace_3233322 : CollatzResearch.WordTrace tailWord_3233322 prefixEnd_3233322 1660248296756703846505229 := by
  unfold tailWord_3233322
  simp only [CollatzResearch.WordTrace]
  refine ⟨29482235398058519069807555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78619294394822717519486813 29482235398058519069807555)
  ·
    refine ⟨44223353097087778604711333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29482235398058519069807555 44223353097087778604711333)
    ·
      refine ⟨8291878705703958488383375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44223353097087778604711333 8291878705703958488383375)
      ·
        refine ⟨12437818058555937732575063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8291878705703958488383375 12437818058555937732575063)
        ·
          refine ⟨18656727087833906598862595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12437818058555937732575063 18656727087833906598862595)
          ·
            refine ⟨27985090631750859898293893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18656727087833906598862595 27985090631750859898293893)
            ·
              refine ⟨5247204493453286230930105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27985090631750859898293893 5247204493453286230930105)
              ·
                refine ⟨3935403370089964673197579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5247204493453286230930105 3935403370089964673197579)
                ·
                  refine ⟨5903105055134947009796369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3935403370089964673197579 5903105055134947009796369)
                  ·
                    refine ⟨4427328791351210257347277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5903105055134947009796369 4427328791351210257347277)
                    ·
                      refine ⟨1660248296756703846505229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4427328791351210257347277 1660248296756703846505229)
                      ·
                        rfl

theorem cell23_3233322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_3233322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233322 prefixEnd_3233322 := by exact prefixLift 3233322
  have htrace : WordTrace (prefixWord ++ tailWord_3233322) baseStart_3233322 baseEnd_3233322 := by
    simpa [prefixWord, tailWord_3233322, baseEnd_3233322] using wordTrace_append hprefix tailTrace_3233322
  have hstable : (prefixWord ++ tailWord_3233322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233322).length < 2 ^ (prefixWord ++ tailWord_3233322).sum := by decide
  have hdescent : baseEnd_3233322 < baseStart_3233322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233335 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 4, 1, 3]
def baseStart_3233335 : Nat := 118140960795 + 3233335 * 2 ^ 59
def prefixEnd_3233335 : Nat := 4983230072969 + 3 ^ 40 * 3233335 * 2
def baseEnd_3233335 : Nat := 1660254972005212295642669

theorem tailTrace_3233335 : CollatzResearch.WordTrace tailWord_3233335 prefixEnd_3233335 1660254972005212295642669 := by
  unfold tailWord_3233335
  simp only [CollatzResearch.WordTrace]
  refine ⟨117929415741186979499453459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78619610494124652999635639 117929415741186979499453459)
  ·
    refine ⟨176894123611780469249180189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117929415741186979499453459 176894123611780469249180189)
    ·
      refine ⟨66335296354417675968442571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176894123611780469249180189 66335296354417675968442571)
      ·
        refine ⟨99502944531626513952663857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66335296354417675968442571 99502944531626513952663857)
        ·
          refine ⟨74627208398719885464497893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99502944531626513952663857 74627208398719885464497893)
          ·
            refine ⟨13992601574759978524593355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74627208398719885464497893 13992601574759978524593355)
            ·
              refine ⟨20988902362139967786890033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13992601574759978524593355 20988902362139967786890033)
              ·
                refine ⟨15741676771604975840167525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20988902362139967786890033 15741676771604975840167525)
                ·
                  refine ⟨2951564394675932970031411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15741676771604975840167525 2951564394675932970031411)
                  ·
                    refine ⟨4427346592013899455047117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2951564394675932970031411 4427346592013899455047117)
                    ·
                      refine ⟨1660254972005212295642669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4427346592013899455047117 1660254972005212295642669)
                      ·
                        rfl

theorem cell23_3233335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_3233335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233335 prefixEnd_3233335 := by exact prefixLift 3233335
  have htrace : WordTrace (prefixWord ++ tailWord_3233335) baseStart_3233335 baseEnd_3233335 := by
    simpa [prefixWord, tailWord_3233335, baseEnd_3233335] using wordTrace_append hprefix tailTrace_3233335
  have hstable : (prefixWord ++ tailWord_3233335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233335).length < 2 ^ (prefixWord ++ tailWord_3233335).sum := by decide
  have hdescent : baseEnd_3233335 < baseStart_3233335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233336 : List Nat := [2, 1, 2, 1, 4, 4, 1, 3, 1, 2, 2]
def baseStart_3233336 : Nat := 118140960795 + 3233336 * 2 ^ 59
def prefixEnd_3233336 : Nat := 4983230072969 + 3 ^ 40 * 3233336 * 2
def baseEnd_3233336 : Nat := 1660255485485866791730165

theorem tailTrace_3233336 : CollatzResearch.WordTrace tailWord_3233336 prefixEnd_3233336 1660255485485866791730165 := by
  unfold tailWord_3233336
  simp only [CollatzResearch.WordTrace]
  refine ⟨58964726107091678335119931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78619634809455571113493241 58964726107091678335119931)
  ·
    refine ⟨88447089160637517502679897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58964726107091678335119931 88447089160637517502679897)
    ·
      refine ⟨66335316870478138127009923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88447089160637517502679897 66335316870478138127009923)
      ·
        refine ⟨99502975305717207190514885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66335316870478138127009923 99502975305717207190514885)
        ·
          refine ⟨18656807869821976348221541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99502975305717207190514885 18656807869821976348221541)
          ·
            refine ⟨3498151475591620565291539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18656807869821976348221541 3498151475591620565291539)
            ·
              refine ⟨5247227213387430847937309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3498151475591620565291539 5247227213387430847937309)
              ·
                refine ⟨1967710205020286567976491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5247227213387430847937309 1967710205020286567976491)
                ·
                  refine ⟨2951565307530429851964737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967710205020286567976491 2951565307530429851964737)
                  ·
                    refine ⟨2213673980647822388973553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2951565307530429851964737 2213673980647822388973553)
                    ·
                      refine ⟨1660255485485866791730165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213673980647822388973553 1660255485485866791730165)
                      ·
                        rfl

theorem cell23_3233336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 1, 2, 2].length) (baseStart_3233336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233336 prefixEnd_3233336 := by exact prefixLift 3233336
  have htrace : WordTrace (prefixWord ++ tailWord_3233336) baseStart_3233336 baseEnd_3233336 := by
    simpa [prefixWord, tailWord_3233336, baseEnd_3233336] using wordTrace_append hprefix tailTrace_3233336
  have hstable : (prefixWord ++ tailWord_3233336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233336).length < 2 ^ (prefixWord ++ tailWord_3233336).sum := by decide
  have hdescent : baseEnd_3233336 < baseStart_3233336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233358 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3233358 : Nat := 118140960795 + 3233358 * 2 ^ 59
def prefixEnd_3233358 : Nat := 4983230072969 + 3 ^ 40 * 3233358 * 2
def baseEnd_3233358 : Nat := 1660266782060265705655063

theorem tailTrace_3233358 : CollatzResearch.WordTrace tailWord_3233358 prefixEnd_3233358 1660266782060265705655063 := by
  unfold tailWord_3233358
  simp only [CollatzResearch.WordTrace]
  refine ⟨14741281827512956803442591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78620169746735769618360485 14741281827512956803442591)
  ·
    refine ⟨22111922741269435205163887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14741281827512956803442591 22111922741269435205163887)
    ·
      refine ⟨33167884111904152807745831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22111922741269435205163887 33167884111904152807745831)
      ·
        refine ⟨49751826167856229211618747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33167884111904152807745831 49751826167856229211618747)
        ·
          refine ⟨74627739251784343817428121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49751826167856229211618747 74627739251784343817428121)
          ·
            refine ⟨55970804438838257863071091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74627739251784343817428121 55970804438838257863071091)
            ·
              refine ⟨83956206658257386794606637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55970804438838257863071091 83956206658257386794606637)
              ·
                refine ⟨31483577496846520047977489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83956206658257386794606637 31483577496846520047977489)
                ·
                  refine ⟨23612683122634890035983117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31483577496846520047977489 23612683122634890035983117)
                  ·
                    refine ⟨8854756170988083763493669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23612683122634890035983117 8854756170988083763493669)
                    ·
                      refine ⟨1660266782060265705655063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8854756170988083763493669 1660266782060265705655063)
                      ·
                        rfl

theorem cell23_3233358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3233358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233358 prefixEnd_3233358 := by exact prefixLift 3233358
  have htrace : WordTrace (prefixWord ++ tailWord_3233358) baseStart_3233358 baseEnd_3233358 := by
    simpa [prefixWord, tailWord_3233358, baseEnd_3233358] using wordTrace_append hprefix tailTrace_3233358
  have hstable : (prefixWord ++ tailWord_3233358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233358).length < 2 ^ (prefixWord ++ tailWord_3233358).sum := by decide
  have hdescent : baseEnd_3233358 < baseStart_3233358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233373 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3233373 : Nat := 118140960795 + 3233373 * 2 ^ 59
def prefixEnd_3233373 : Nat := 4983230072969 + 3 ^ 40 * 3233373 * 2
def baseEnd_3233373 : Nat := 1660274484270083146967495

theorem tailTrace_3233373 : CollatzResearch.WordTrace tailWord_3233373 prefixEnd_3233373 1660274484270083146967495 := by
  unfold tailWord_3233373
  simp only [CollatzResearch.WordTrace]
  refine ⟨117930801715049311989336773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78620534476699541326224515 117930801715049311989336773)
  ·
    refine ⟨22112025321571745998000645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117930801715049311989336773 22112025321571745998000645)
    ·
      refine ⟨4146004747794702374625121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22112025321571745998000645 4146004747794702374625121)
      ·
        refine ⟨3109503560846026780968841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4146004747794702374625121 3109503560846026780968841)
        ·
          refine ⟨2332127670634520085726631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3109503560846026780968841 2332127670634520085726631)
          ·
            refine ⟨3498191505951780128589947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332127670634520085726631 3498191505951780128589947)
            ·
              refine ⟨5247287258927670192884921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3498191505951780128589947 5247287258927670192884921)
              ·
                refine ⟨3935465444195752644663691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5247287258927670192884921 3935465444195752644663691)
                ·
                  refine ⟨5903198166293628966995537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3935465444195752644663691 5903198166293628966995537)
                  ·
                    refine ⟨4427398624720221725246653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5903198166293628966995537 4427398624720221725246653)
                    ·
                      refine ⟨1660274484270083146967495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4427398624720221725246653 1660274484270083146967495)
                      ·
                        rfl

theorem cell23_3233373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3233373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233373 prefixEnd_3233373 := by exact prefixLift 3233373
  have htrace : WordTrace (prefixWord ++ tailWord_3233373) baseStart_3233373 baseEnd_3233373 := by
    simpa [prefixWord, tailWord_3233373, baseEnd_3233373] using wordTrace_append hprefix tailTrace_3233373
  have hstable : (prefixWord ++ tailWord_3233373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233373).length < 2 ^ (prefixWord ++ tailWord_3233373).sum := by decide
  have hdescent : baseEnd_3233373 < baseStart_3233373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233379 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 1, 3, 2]
def baseStart_3233379 : Nat := 118140960795 + 3233379 * 2 ^ 59
def prefixEnd_3233379 : Nat := 4983230072969 + 3 ^ 40 * 3233379 * 2
def baseEnd_3233379 : Nat := 1660277565154010123492467

theorem tailTrace_3233379 : CollatzResearch.WordTrace tailWord_3233379 prefixEnd_3233379 1660277565154010123492467 := by
  unfold tailWord_3233379
  simp only [CollatzResearch.WordTrace]
  refine ⟨117931020553027575014055191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78620680368685050009370127 117931020553027575014055191)
  ·
    refine ⟨176896530829541362521082787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117931020553027575014055191 176896530829541362521082787)
    ·
      refine ⟨265344796244312043781624181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176896530829541362521082787 265344796244312043781624181)
      ·
        refine ⟨24876074647904254104527267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265344796244312043781624181 24876074647904254104527267)
        ·
          refine ⟨37314111971856381156790901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24876074647904254104527267 37314111971856381156790901)
          ·
            refine ⟨3498197997361535733449147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37314111971856381156790901 3498197997361535733449147)
            ·
              refine ⟨5247296996042303600173721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3498197997361535733449147 5247296996042303600173721)
              ·
                refine ⟨3935472747031727700130291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5247296996042303600173721 3935472747031727700130291)
                ·
                  refine ⟨5903209120547591550195437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3935472747031727700130291 5903209120547591550195437)
                  ·
                    refine ⟨2213703420205346831323289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5903209120547591550195437 2213703420205346831323289)
                    ·
                      refine ⟨1660277565154010123492467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213703420205346831323289 1660277565154010123492467)
                      ·
                        rfl

theorem cell23_3233379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_3233379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233379 prefixEnd_3233379 := by exact prefixLift 3233379
  have htrace : WordTrace (prefixWord ++ tailWord_3233379) baseStart_3233379 baseEnd_3233379 := by
    simpa [prefixWord, tailWord_3233379, baseEnd_3233379] using wordTrace_append hprefix tailTrace_3233379
  have hstable : (prefixWord ++ tailWord_3233379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233379).length < 2 ^ (prefixWord ++ tailWord_3233379).sum := by decide
  have hdescent : baseEnd_3233379 < baseStart_3233379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233388 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_3233388 : Nat := 118140960795 + 3233388 * 2 ^ 59
def prefixEnd_3233388 : Nat := 4983230072969 + 3 ^ 40 * 3233388 * 2
def baseEnd_3233388 : Nat := 1660282186479900588279925

theorem tailTrace_3233388 : CollatzResearch.WordTrace tailWord_3233388 prefixEnd_3233388 1660282186479900588279925 := by
  unfold tailWord_3233388
  simp only [CollatzResearch.WordTrace]
  refine ⟨58965674404997484775566409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78620899206663313034088545 58965674404997484775566409)
  ·
    refine ⟨44224255803748113581674807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58965674404997484775566409 44224255803748113581674807)
    ·
      refine ⟨66336383705622170372512211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44224255803748113581674807 66336383705622170372512211)
      ·
        refine ⟨99504575558433255558768317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66336383705622170372512211 99504575558433255558768317)
        ·
          refine ⟨37314215834412470834538119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99504575558433255558768317 37314215834412470834538119)
          ·
            refine ⟨55971323751618706251807179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37314215834412470834538119 55971323751618706251807179)
            ·
              refine ⟨83956985627428059377710769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55971323751618706251807179 83956985627428059377710769)
              ·
                refine ⟨62967739220571044533283077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83956985627428059377710769 62967739220571044533283077)
                ·
                  refine ⟨11806451103857070849990577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62967739220571044533283077 11806451103857070849990577)
                  ·
                    refine ⟨8854838327892803137492933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11806451103857070849990577 8854838327892803137492933)
                    ·
                      refine ⟨1660282186479900588279925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8854838327892803137492933 1660282186479900588279925)
                      ·
                        rfl

theorem cell23_3233388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_3233388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233388 prefixEnd_3233388 := by exact prefixLift 3233388
  have htrace : WordTrace (prefixWord ++ tailWord_3233388) baseStart_3233388 baseEnd_3233388 := by
    simpa [prefixWord, tailWord_3233388, baseEnd_3233388] using wordTrace_append hprefix tailTrace_3233388
  have hstable : (prefixWord ++ tailWord_3233388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233388).length < 2 ^ (prefixWord ++ tailWord_3233388).sum := by decide
  have hdescent : baseEnd_3233388 < baseStart_3233388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233392 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 1, 4, 2]
def baseStart_3233392 : Nat := 118140960795 + 3233392 * 2 ^ 59
def prefixEnd_3233392 : Nat := 4983230072969 + 3 ^ 40 * 3233392 * 2
def baseEnd_3233392 : Nat := 1660284240402518572629907

theorem tailTrace_3233392 : CollatzResearch.WordTrace tailWord_3233392 prefixEnd_3233392 1660284240402518572629907 := by
  unfold tailWord_3233392
  simp only [CollatzResearch.WordTrace]
  refine ⟨58965747350990239117139215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78620996467986985489518953 58965747350990239117139215)
  ·
    refine ⟨88448621026485358675708823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58965747350990239117139215 88448621026485358675708823)
    ·
      refine ⟨132672931539728038013563235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88448621026485358675708823 132672931539728038013563235)
      ·
        refine ⟨199009397309592057020344853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132672931539728038013563235 199009397309592057020344853)
        ·
          refine ⟨9328565498887127672828665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 199009397309592057020344853 9328565498887127672828665)
          ·
            refine ⟨6996424124165345754621499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9328565498887127672828665 6996424124165345754621499)
            ·
              refine ⟨10494636186248018631932249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6996424124165345754621499 10494636186248018631932249)
              ·
                refine ⟨7870977139686013973949187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10494636186248018631932249 7870977139686013973949187)
                ·
                  refine ⟨11806465709529020960923781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7870977139686013973949187 11806465709529020960923781)
                  ·
                    refine ⟨2213712320536691430173209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11806465709529020960923781 2213712320536691430173209)
                    ·
                      refine ⟨1660284240402518572629907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213712320536691430173209 1660284240402518572629907)
                      ·
                        rfl

theorem cell23_3233392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 4, 2].length) (baseStart_3233392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233392 prefixEnd_3233392 := by exact prefixLift 3233392
  have htrace : WordTrace (prefixWord ++ tailWord_3233392) baseStart_3233392 baseEnd_3233392 := by
    simpa [prefixWord, tailWord_3233392, baseEnd_3233392] using wordTrace_append hprefix tailTrace_3233392
  have hstable : (prefixWord ++ tailWord_3233392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233392).length < 2 ^ (prefixWord ++ tailWord_3233392).sum := by decide
  have hdescent : baseEnd_3233392 < baseStart_3233392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233409 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_3233409 : Nat := 118140960795 + 3233409 * 2 ^ 59
def prefixEnd_3233409 : Nat := 4983230072969 + 3 ^ 40 * 3233409 * 2
def baseEnd_3233409 : Nat := 1660292969573645006117329

theorem tailTrace_3233409 : CollatzResearch.WordTrace tailWord_3233409 prefixEnd_3233409 1660292969573645006117329 := by
  unfold tailWord_3233409
  simp only [CollatzResearch.WordTrace]
  refine ⟨117932114742918890137647281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78621409828612593425098187 117932114742918890137647281)
  ·
    refine ⟨88449086057189167603235461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117932114742918890137647281 88449086057189167603235461)
    ·
      refine ⟨16584203635722968925606649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88449086057189167603235461 16584203635722968925606649)
      ·
        refine ⟨12438152726792226694204987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16584203635722968925606649 12438152726792226694204987)
        ·
          refine ⟨18657229090188340041307481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12438152726792226694204987 18657229090188340041307481)
          ·
            refine ⟨13992921817641255030980611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18657229090188340041307481 13992921817641255030980611)
            ·
              refine ⟨20989382726461882546470917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13992921817641255030980611 20989382726461882546470917)
              ·
                refine ⟨3935509261211602977463297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20989382726461882546470917 3935509261211602977463297)
                ·
                  refine ⟨2951631945908702233097473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3935509261211602977463297 2951631945908702233097473)
                  ·
                    refine ⟨2213723959431526674823105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2951631945908702233097473 2213723959431526674823105)
                    ·
                      refine ⟨1660292969573645006117329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213723959431526674823105 1660292969573645006117329)
                      ·
                        rfl

theorem cell23_3233409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_3233409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233409 prefixEnd_3233409 := by exact prefixLift 3233409
  have htrace : WordTrace (prefixWord ++ tailWord_3233409) baseStart_3233409 baseEnd_3233409 := by
    simpa [prefixWord, tailWord_3233409, baseEnd_3233409] using wordTrace_append hprefix tailTrace_3233409
  have hstable : (prefixWord ++ tailWord_3233409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233409).length < 2 ^ (prefixWord ++ tailWord_3233409).sum := by decide
  have hdescent : baseEnd_3233409 < baseStart_3233409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233445 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 2, 5]
def baseStart_3233445 : Nat := 118140960795 + 3233445 * 2 ^ 59
def prefixEnd_3233445 : Nat := 4983230072969 + 3 ^ 40 * 3233445 * 2
def baseEnd_3233445 : Nat := 553437151625735621755721

theorem tailTrace_3233445 : CollatzResearch.WordTrace tailWord_3233445 prefixEnd_3233445 553437151625735621755721 := by
  unfold tailWord_3233445
  simp only [CollatzResearch.WordTrace]
  refine ⟨117933427770788468285957789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78622285180525645523971859 117933427770788468285957789)
  ·
    refine ⟨44225035414045675607234171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117933427770788468285957789 44225035414045675607234171)
    ·
      refine ⟨66337553121068513410851257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44225035414045675607234171 66337553121068513410851257)
      ·
        refine ⟨49753164840801385058138443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66337553121068513410851257 49753164840801385058138443)
        ·
          refine ⟨74629747261202077587207665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49753164840801385058138443 74629747261202077587207665)
          ·
            refine ⟨55972310445901558190405749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74629747261202077587207665 55972310445901558190405749)
            ·
              refine ⟨5247404104303271080350539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55972310445901558190405749 5247404104303271080350539)
              ·
                refine ⟨7871106156454906620525809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5247404104303271080350539 7871106156454906620525809)
                ·
                  refine ⟨5903329617341179965394357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7871106156454906620525809 5903329617341179965394357)
                  ·
                    refine ⟨553437151625735621755721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5903329617341179965394357 553437151625735621755721)
                    ·
                      rfl

theorem cell23_3233445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_3233445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233445 prefixEnd_3233445 := by exact prefixLift 3233445
  have htrace : WordTrace (prefixWord ++ tailWord_3233445) baseStart_3233445 baseEnd_3233445 := by
    simpa [prefixWord, tailWord_3233445, baseEnd_3233445] using wordTrace_append hprefix tailTrace_3233445
  have hstable : (prefixWord ++ tailWord_3233445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233445).length < 2 ^ (prefixWord ++ tailWord_3233445).sum := by decide
  have hdescent : baseEnd_3233445 < baseStart_3233445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233465 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3233465 : Nat := 118140960795 + 3233465 * 2 ^ 59
def prefixEnd_3233465 : Nat := 4983230072969 + 3 ^ 40 * 3233465 * 2
def baseEnd_3233465 : Nat := 1660321724490296787017071

theorem tailTrace_3233465 : CollatzResearch.WordTrace tailWord_3233465 prefixEnd_3233465 1660321724490296787017071 := by
  unfold tailWord_3233465
  simp only [CollatzResearch.WordTrace]
  refine ⟨117934157230716011701685849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78622771487144007801123899 117934157230716011701685849)
  ·
    refine ⟨88450617923037008776264387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117934157230716011701685849 88450617923037008776264387)
    ·
      refine ⟨132675926884555513164396581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88450617923037008776264387 132675926884555513164396581)
      ·
        refine ⟨24876736290854158718324359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132675926884555513164396581 24876736290854158718324359)
        ·
          refine ⟨37315104436281238077486539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24876736290854158718324359 37315104436281238077486539)
          ·
            refine ⟨55972656654421857116229809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37315104436281238077486539 55972656654421857116229809)
            ·
              refine ⟨41979492490816392837172357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55972656654421857116229809 41979492490816392837172357)
              ·
                refine ⟨7871154842028073656969817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41979492490816392837172357 7871154842028073656969817)
                ·
                  refine ⟨5903366131521055242727363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7871154842028073656969817 5903366131521055242727363)
                  ·
                    refine ⟨8855049197281582864091045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5903366131521055242727363 8855049197281582864091045)
                    ·
                      refine ⟨1660321724490296787017071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8855049197281582864091045 1660321724490296787017071)
                      ·
                        rfl

theorem cell23_3233465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3233465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233465 prefixEnd_3233465 := by exact prefixLift 3233465
  have htrace : WordTrace (prefixWord ++ tailWord_3233465) baseStart_3233465 baseEnd_3233465 := by
    simpa [prefixWord, tailWord_3233465, baseEnd_3233465] using wordTrace_append hprefix tailTrace_3233465
  have hstable : (prefixWord ++ tailWord_3233465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233465).length < 2 ^ (prefixWord ++ tailWord_3233465).sum := by decide
  have hdescent : baseEnd_3233465 < baseStart_3233465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233559 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 2, 3, 2]
def baseStart_3233559 : Nat := 118140960795 + 3233559 * 2 ^ 59
def prefixEnd_3233559 : Nat := 4983230072969 + 3 ^ 40 * 3233559 * 2
def baseEnd_3233559 : Nat := 1660369991671819419241639

theorem tailTrace_3233559 : CollatzResearch.WordTrace tailWord_3233559 prefixEnd_3233559 1660369991671819419241639 := by
  unfold tailWord_3233559
  simp only [CollatzResearch.WordTrace]
  refine ⟨117937585692375465755607731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78625057128250310503738487 117937585692375465755607731)
  ·
    refine ⟨176906378538563198633411597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117937585692375465755607731 176906378538563198633411597)
    ·
      refine ⟨66339891951961199487529349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176906378538563198633411597 66339891951961199487529349)
      ·
        refine ⟨12438729740992724903911753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66339891951961199487529349 12438729740992724903911753)
        ·
          refine ⟨9329047305744543677933815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12438729740992724903911753 9329047305744543677933815)
          ·
            refine ⟨13993570958616815516900723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9329047305744543677933815 13993570958616815516900723)
            ·
              refine ⟨20990356437925223275351085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13993570958616815516900723 20990356437925223275351085)
              ·
                refine ⟨7871383664221958728256657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20990356437925223275351085 7871383664221958728256657)
                ·
                  refine ⟨5903537748166469046192493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7871383664221958728256657 5903537748166469046192493)
                  ·
                    refine ⟨2213826655562425892322185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5903537748166469046192493 2213826655562425892322185)
                    ·
                      refine ⟨1660369991671819419241639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213826655562425892322185 1660369991671819419241639)
                      ·
                        rfl

theorem cell23_3233559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_3233559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233559 prefixEnd_3233559 := by exact prefixLift 3233559
  have htrace : WordTrace (prefixWord ++ tailWord_3233559) baseStart_3233559 baseEnd_3233559 := by
    simpa [prefixWord, tailWord_3233559, baseEnd_3233559] using wordTrace_append hprefix tailTrace_3233559
  have hstable : (prefixWord ++ tailWord_3233559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233559).length < 2 ^ (prefixWord ++ tailWord_3233559).sum := by decide
  have hdescent : baseEnd_3233559 < baseStart_3233559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233569 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 1, 5]
def baseStart_3233569 : Nat := 118140960795 + 3233569 * 2 ^ 59
def prefixEnd_3233569 : Nat := 4983230072969 + 3 ^ 40 * 3233569 * 2
def baseEnd_3233569 : Nat := 553458375492788126705531

theorem tailTrace_3233569 : CollatzResearch.WordTrace tailWord_3233569 prefixEnd_3233569 553458375492788126705531 := by
  unfold tailWord_3233569
  simp only [CollatzResearch.WordTrace]
  refine ⟨117937950422339237463471761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78625300281559491642314507 117937950422339237463471761)
  ·
    refine ⟨88453462816754428097603821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117937950422339237463471761 88453462816754428097603821)
    ·
      refine ⟨33170048556282910536601433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88453462816754428097603821 33170048556282910536601433)
      ·
        refine ⟨24877536417212182902451075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33170048556282910536601433 24877536417212182902451075)
        ·
          refine ⟨37316304625818274353676613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24877536417212182902451075 37316304625818274353676613)
          ·
            refine ⟨6996807117340926441314365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37316304625818274353676613 6996807117340926441314365)
            ·
              refine ⟨2623802669002847415492887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6996807117340926441314365 2623802669002847415492887)
              ·
                refine ⟨3935704003504271123239331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623802669002847415492887 3935704003504271123239331)
                ·
                  refine ⟨5903556005256406684858997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3935704003504271123239331 5903556005256406684858997)
                  ·
                    refine ⟨553458375492788126705531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5903556005256406684858997 553458375492788126705531)
                    ·
                      rfl

theorem cell23_3233569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_3233569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233569 prefixEnd_3233569 := by exact prefixLift 3233569
  have htrace : WordTrace (prefixWord ++ tailWord_3233569) baseStart_3233569 baseEnd_3233569 := by
    simpa [prefixWord, tailWord_3233569, baseEnd_3233569] using wordTrace_append hprefix tailTrace_3233569
  have hstable : (prefixWord ++ tailWord_3233569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233569).length < 2 ^ (prefixWord ++ tailWord_3233569).sum := by decide
  have hdescent : baseEnd_3233569 < baseStart_3233569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233592 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 3, 2, 3]
def baseStart_3233592 : Nat := 118140960795 + 3233592 * 2 ^ 59
def prefixEnd_3233592 : Nat := 4983230072969 + 3 ^ 40 * 3233592 * 2
def baseEnd_3233592 : Nat := 1660386936533417790128987

theorem tailTrace_3233592 : CollatzResearch.WordTrace tailWord_3233592 prefixEnd_3233592 1660386936533417790128987 := by
  unfold tailWord_3233592
  simp only [CollatzResearch.WordTrace]
  refine ⟨58969394650627956195779515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78625859534170608261039353 58969394650627956195779515)
  ·
    refine ⟨88454091975941934293669273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58969394650627956195779515 88454091975941934293669273)
    ·
      refine ⟨66340568981956450720251955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88454091975941934293669273 66340568981956450720251955)
      ·
        refine ⟨99510853472934676080377933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66340568981956450720251955 99510853472934676080377933)
        ·
          refine ⟨37316570052350503530141725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99510853472934676080377933 37316570052350503530141725)
          ·
            refine ⟨13993713769631438823803147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37316570052350503530141725 13993713769631438823803147)
            ·
              refine ⟨20990570654447158235704721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13993713769631438823803147 20990570654447158235704721)
              ·
                refine ⟨15742927990835368676778541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20990570654447158235704721 15742927990835368676778541)
                ·
                  refine ⟨5903597996563263253791953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15742927990835368676778541 5903597996563263253791953)
                  ·
                    refine ⟨4427698497422447440343965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5903597996563263253791953 4427698497422447440343965)
                    ·
                      refine ⟨1660386936533417790128987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4427698497422447440343965 1660386936533417790128987)
                      ·
                        rfl

theorem cell23_3233592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_3233592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233592 prefixEnd_3233592 := by exact prefixLift 3233592
  have htrace : WordTrace (prefixWord ++ tailWord_3233592) baseStart_3233592 baseEnd_3233592 := by
    simpa [prefixWord, tailWord_3233592, baseEnd_3233592] using wordTrace_append hprefix tailTrace_3233592
  have hstable : (prefixWord ++ tailWord_3233592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233592).length < 2 ^ (prefixWord ++ tailWord_3233592).sum := by decide
  have hdescent : baseEnd_3233592 < baseStart_3233592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233606 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3233606 : Nat := 118140960795 + 3233606 * 2 ^ 59
def prefixEnd_3233606 : Nat := 4983230072969 + 3 ^ 40 * 3233606 * 2
def baseEnd_3233606 : Nat := 1660394125262580735353923

theorem tailTrace_3233606 : CollatzResearch.WordTrace tailWord_3233606 prefixEnd_3233606 1660394125262580735353923 := by
  unfold tailWord_3233606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685603122600162274455271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78626199948803461855045781 3685603122600162274455271)
  ·
    refine ⟨5528404683900243411682907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3685603122600162274455271 5528404683900243411682907)
    ·
      refine ⟨8292607025850365117524361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5528404683900243411682907 8292607025850365117524361)
      ·
        refine ⟨6219455269387773838143271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8292607025850365117524361 6219455269387773838143271)
        ·
          refine ⟨9329182904081660757214907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6219455269387773838143271 9329182904081660757214907)
          ·
            refine ⟨13993774356122491135822361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9329182904081660757214907 13993774356122491135822361)
            ·
              refine ⟨10495330767091868351866771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13993774356122491135822361 10495330767091868351866771)
              ·
                refine ⟨15742996150637802527800157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10495330767091868351866771 15742996150637802527800157)
                ·
                  refine ⟨5903623556489175947925059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15742996150637802527800157 5903623556489175947925059)
                  ·
                    refine ⟨8855435334733763921887589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5903623556489175947925059 8855435334733763921887589)
                    ·
                      refine ⟨1660394125262580735353923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8855435334733763921887589 1660394125262580735353923)
                      ·
                        rfl

theorem cell23_3233606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3233606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233606 prefixEnd_3233606 := by exact prefixLift 3233606
  have htrace : WordTrace (prefixWord ++ tailWord_3233606) baseStart_3233606 baseEnd_3233606 := by
    simpa [prefixWord, tailWord_3233606, baseEnd_3233606] using wordTrace_append hprefix tailTrace_3233606
  have hstable : (prefixWord ++ tailWord_3233606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233606).length < 2 ^ (prefixWord ++ tailWord_3233606).sum := by decide
  have hdescent : baseEnd_3233606 < baseStart_3233606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233623 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 1, 1, 4]
def baseStart_3233623 : Nat := 118140960795 + 3233623 * 2 ^ 59
def prefixEnd_3233623 : Nat := 4983230072969 + 3 ^ 40 * 3233623 * 2
def baseEnd_3233623 : Nat := 1660402854433707168841345

theorem tailTrace_3233623 : CollatzResearch.WordTrace tailWord_3233623 prefixEnd_3233623 1660402854433707168841345 := by
  unfold tailWord_3233623
  simp only [CollatzResearch.WordTrace]
  refine ⟨117939919964143604685937523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78626613309429069790625015 117939919964143604685937523)
  ·
    refine ⟨176909879946215407028906285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117939919964143604685937523 176909879946215407028906285)
    ·
      refine ⟨66341204979830777635839857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176909879946215407028906285 66341204979830777635839857)
      ·
        refine ⟨49755903734873083226879893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66341204979830777635839857 49755903734873083226879893)
        ·
          refine ⟨2332307987572175776259995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49755903734873083226879893 2332307987572175776259995)
          ·
            refine ⟨3498461981358263664389993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332307987572175776259995 3498461981358263664389993)
            ·
              refine ⟨2623846486018697748292495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3498461981358263664389993 2623846486018697748292495)
              ·
                refine ⟨3935769729028046622438743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623846486018697748292495 3935769729028046622438743)
                ·
                  refine ⟨5903654593542069933658115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3935769729028046622438743 5903654593542069933658115)
                  ·
                    refine ⟨8855481890313104900487173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5903654593542069933658115 8855481890313104900487173)
                    ·
                      refine ⟨1660402854433707168841345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8855481890313104900487173 1660402854433707168841345)
                      ·
                        rfl

theorem cell23_3233623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_3233623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233623 prefixEnd_3233623 := by exact prefixLift 3233623
  have htrace : WordTrace (prefixWord ++ tailWord_3233623) baseStart_3233623 baseEnd_3233623 := by
    simpa [prefixWord, tailWord_3233623, baseEnd_3233623] using wordTrace_append hprefix tailTrace_3233623
  have hstable : (prefixWord ++ tailWord_3233623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233623).length < 2 ^ (prefixWord ++ tailWord_3233623).sum := by decide
  have hdescent : baseEnd_3233623 < baseStart_3233623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
